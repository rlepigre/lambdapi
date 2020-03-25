(** Calling a prover using Why3. *)

open Console
open Terms
open Extra
open Timed
open Scope

(** Logging function for external prover calling with Why3. *)
let log_why3 = new_logger 'w' "why3" "why3 provers"
let log_why3 = log_why3.logger

(** [default_prover] contains the name of the current prover. Note that it can
    be changed by using the "set prover <string>" command. *)
let default_prover : string ref = ref "Alt-Ergo"

(** [timeout] is the current time limit (in seconds) for a Why3 prover to find
    a proof. It can be changed with "set prover <int>". *)
let timeout : int ref = ref 2

(** [why3_config] is the Why3 configuration read the configuration file (it is
    usually located at ["~/.why3.conf"]). For more information, visit the Why3
    documentation at http://why3.lri.fr/api/Whyconf.html. *)
let why3_config : Why3.Whyconf.config = Why3.Whyconf.read_config None

(** [why3_main] is the main section of the Why3 configuration. *)
let why3_main : Why3.Whyconf.main = Why3.Whyconf.get_main why3_config

(** [why3_env] is the initialized Why3 environment. *)
let why3_env : Why3.Env.env =
  Why3.Env.create_env (Why3.Whyconf.loadpath why3_main)

(** Builtins configuration for propositional logic. *)
type config =
  { symb_P   : sym (** Encoding of propositions. *)
  ; symb_T   : sym (** Encoding of types.        *)
  ; symb_or  : sym (** Disjunction(∨) symbol.    *)
  ; symb_and : sym (** Conjunction(∧) symbol.    *)
  ; symb_imp : sym (** Implication(⇒) symbol.    *)
  ; symb_bot : sym (** Bot(⊥) symbol.            *)
  ; symb_top : sym (** Top(⊤) symbol.            *)
  ; symb_not : sym (** Not(¬) symbol.            *) }

(** [get_config pos builtins] build the configuration using [builtins]. *)
let get_config : Pos.popt -> sym StrMap.t -> config = fun pos builtins ->
  { symb_P   = Sign.builtin pos builtins "P"
  ; symb_T   = Sign.builtin pos builtins "T"
  ; symb_or  = Sign.builtin pos builtins "or"
  ; symb_and = Sign.builtin pos builtins "and"
  ; symb_imp = Sign.builtin pos builtins "imp"
  ; symb_bot = Sign.builtin pos builtins "bot"
  ; symb_top = Sign.builtin pos builtins "top"
  ; symb_not = Sign.builtin pos builtins "not" }

(** A map from lambdapi terms to Why3 constants. *)
type cnst_table = (term * Why3.Term.lsymbol) list

(** [new_axiom_name ()] generates a fresh axiom name. *)
let new_axiom_name : unit -> string =
  let counter = ref 0 in
  fun _ -> incr counter; "Why3axiom_" ^ (string_of_int !counter)

(** [translate_term cfg tbl t] translates the given lambdapi term [t] into the
    correspondig Why3 term, using the configuration [cfg] and constants in the
    association list [tbl]. *)
let translate_term : config -> cnst_table -> term ->
                       (cnst_table * Why3.Term.term) option = fun cfg tbl t ->
  let rec translate_prop tbl t =
    match Basics.get_args t with
    | (Symb(s,_), [t1; t2]) when s == cfg.symb_and ->
        let (tbl, t1) = translate_prop tbl t1 in
        let (tbl, t2) = translate_prop tbl t2 in
        (tbl, Why3.Term.t_and t1 t2)
    | (Symb(s,_), [t1; t2]) when s == cfg.symb_or  ->
        let (tbl, t1) = translate_prop tbl t1 in
        let (tbl, t2) = translate_prop tbl t2 in
        (tbl, Why3.Term.t_or t1 t2)
    | (Symb(s,_), [t1; t2]) when s == cfg.symb_imp ->
        let (tbl, t1) = translate_prop tbl t1 in
        let (tbl, t2) = translate_prop tbl t2 in
        (tbl, Why3.Term.t_implies t1 t2)
    | (Symb(s,_), [t]     ) when s == cfg.symb_not ->
        let (tbl, t) = translate_prop tbl t in
        (tbl, Why3.Term.t_not t)
    | (Symb(s,_), []      ) when s == cfg.symb_bot ->
        (tbl, Why3.Term.t_false)
    | (Symb(s,_), []      ) when s == cfg.symb_top ->
        (tbl, Why3.Term.t_true)
    | (_        , _       )                        ->
        (* If the term [p] is mapped in [tbl] then use it. *)
        try (tbl, Why3.Term.ps_app (List.assoc_eq Basics.eq t tbl) [])
        with Not_found ->
          (* Otherwise generate a new constant in why3. *)
          let sym = Why3.Term.create_psymbol (Why3.Ident.id_fresh "P") [] in
          ((t, sym)::tbl, Why3.Term.ps_app sym [])
  in
  match Basics.get_args t with
  | (Symb(s,_), [t]) when s == cfg.symb_P -> Some (translate_prop tbl t)
  | _                                     -> None

(** [encode pos builtins hs g] translates the hypotheses [hs] and the goal [g]
    into Why3 terms, to construct a Why3 task. *)
let encode : Pos.popt -> sym StrMap.t -> Env.env -> term -> Why3.Task.task =
    fun pos builtins hs g ->
  let cfg = get_config pos builtins in
  let (constants, hypothesis) =
    let translate_hyp (tbl, map) (name, (_, hyp)) =
      match translate_term cfg tbl (Bindlib.unbox hyp) with
      | Some(tbl, why3_hyp) -> (tbl, StrMap.add name why3_hyp map)
      | None                -> (tbl, map)
    in
    List.fold_left translate_hyp ([], StrMap.empty) hs
  in
  (* Translate the goal term. *)
  let (tbl, why3_term) =
    match translate_term cfg constants g with
    | Some(tbl, why3_term) -> (tbl, why3_term)
    | None                 ->
        fatal pos "The goal [%a] is not of the form [P _]" Print.pp g
  in
  (* Add the declaration of every constant in a task. *)
  let fn tsk (_,t) = Why3.Task.add_param_decl tsk t in
  let tsk = List.fold_left fn None tbl in
  (* Add the declaration of every hypothesis in the task. *)
  let fn name t tsk =
    let axiom = Why3.Decl.create_prsymbol (Why3.Ident.id_fresh name) in
    Why3.Task.add_prop_decl tsk Why3.Decl.Paxiom axiom t
  in
  let tsk = StrMap.fold fn hypothesis tsk in
  (* Add the goal itself. *)
  let goal = Why3.Decl.create_prsymbol (Why3.Ident.id_fresh "main_goal") in
  (* Return the task that contains the encoded lambdapi formula in Why3. *)
  Why3.Task.add_prop_decl tsk Why3.Decl.Pgoal goal why3_term

(** [run_task tsk pos prover_name] Run the task [tsk] with the specified
    prover named [prover_name] and return the answer of the prover. *)
let run_task : Why3.Task.task -> Pos.popt -> string -> bool =
    fun tsk pos prover_name ->
  (* Filter the set of why3 provers. *)
  let filter = Why3.Whyconf.parse_filter_prover prover_name in
  let provers = Why3.Whyconf.filter_provers why3_config filter in
  (* Fail if we did not find a matching prover. *)
  if Why3.Whyconf.Mprover.is_empty provers then
    begin
      fatal_msg "prover [%s] not found.\n" prover_name;
      let provers = Why3.Whyconf.get_provers why3_config in
      let _ =
        if Why3.Whyconf.Mprover.is_empty provers then
          fatal_msg "There are no available Why3 provers.\n"
        else
          let fn p _ = fatal_msg " - %a\n" Why3.Whyconf.print_prover p in
          fatal_msg "The available Why3 provers are:\n";
          Why3.Whyconf.Mprover.iter fn provers
      in
      fatal_msg "Why3 configuration read from [%s].\n"
        (Why3.Whyconf.get_conf_file why3_config);
      fatal_msg "Your prover might not be installed or detected, ";
      fatal pos "remember to run [why3 config --detect]."
    end;
  (* Return the prover configuration and load the driver. *)
  let prover = snd (Why3.Whyconf.Mprover.max_binding provers) in
  let driver =
    try Why3.Whyconf.(load_driver why3_main why3_env prover.driver [])
    with e -> fatal pos "Failed to load driver for %s (%a)"
                prover.prover.prover_name Why3.Exn_printer.exn_printer e
  in
  (* Actually run the prover. *)
  let limit = {Why3.Call_provers.empty_limit with limit_time = !timeout} in
  let command = prover.Why3.Whyconf.command in
  let call = Why3.Driver.prove_task ~limit ~command driver tsk in
  Why3.Call_provers.((wait_on_call call).pr_answer = Valid)

(** [handle pos ps ss prover_name g] runs the Why3 prover corresponding to the
    name [prover_name] (if given or a default one otherwise) on the goal  [g].
    If the prover succeeded to prove the goal, then this is reflected by a new
    axiom that is added to signature [ss]. *)
let handle : Pos.popt -> Proof.proof_state -> sig_state -> string option ->
               Proof.Goal.t -> term = fun pos ps ss prover_name g ->
  (* Get the goal to prove. *)
  let (hyps, trm) = Proof.Goal.get_type g in
  (* Get the default or the indicated name of the prover. *)
  let prover_name = Option.get !default_prover prover_name in
  if !log_enabled then log_why3 "running with configuration [%s]" prover_name;
  (* Encode the goal in Why3. *)
  let tsk = encode pos ps.Proof.proof_builtins hyps trm in
  (* Run the task with the prover named [prover_name]. *)
  if not (run_task tsk pos prover_name) then
    fatal pos "%s did not found a proof" prover_name;
  (* Create a new axiom that represents the proved goal. *)
  let axiom_name = new_axiom_name () in
  (* Get the meta type of the current goal (with quantified context). *)
  let trm = !((Proof.Goal.get_meta g).meta_type) in
  (* Add the axiom to the current signature. *)
  let a =
    Sign.add_symbol ss.signature Privat Const (Pos.none axiom_name) trm []
  in
  (* Tell the user that the goal is proved (verbose 2). *)
  if !log_enabled then log_why3 "goal proved: axiom [%s] created" axiom_name;
  (* Return the variable terms of each item in the context. *)
  let terms = List.rev_map (fun (_, (x, _)) -> Vari x) hyps in
  (* Apply the instance of the axiom with context. *)
  Basics.add_args (symb a) terms
