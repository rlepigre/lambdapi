(** Toplevel commands. *)

open Extra
open Timed
open Console
open Terms
open Print
open Sign
open Pos
open Files
open Syntax
open Scope

(** [handle_cmd_aux ss cmd] tries to handle the command [cmd] with [ss] as the
    module state. On success, an updated module state is returned, and [Fatal]
    is raised in case of an error. *)
let handle_cmd_aux : sig_state -> command -> sig_state = fun ss cmd ->
  let scope_basic ss t = Scope.scope_term StrMap.empty ss Env.empty t in
  match cmd.elt with
  | P_require(p, m)            ->
      (* Check that the module has not already been required. *)
      if PathMap.mem p !(ss.signature.sign_deps) then
        fatal cmd.pos "Module [%a] is already required." pp_path p;
      (* Add the dependency and compile the module. *)
      ss.signature.sign_deps := PathMap.add p [] !(ss.signature.sign_deps);
      (*compile false p;*)
      (* Open or alias if necessary. *)
      begin
        match m with
        | P_require_default -> ss
        | P_require_open    ->
            let sign =
              try PathMap.find p !(Sign.loaded)
              with Not_found -> assert false (* Cannot happen. *)
            in
            open_sign ss sign
        | P_require_as(id)  ->
            let aliases = StrMap.add id.elt p ss.aliases in
            {ss with aliases}
      end
  | P_open(m)                  ->
      (* Obtain the signature corresponding to [m]. *)
      let sign =
        try PathMap.find m !(Sign.loaded) with Not_found ->
        (* The signature has nob been required... *)
        fatal cmd.pos "Module [%a] has not been required." pp_path m
      in
      (* Open the module. *)
      open_sign ss sign
  | P_symbol(ts, x, a)         ->
      (* We first build the symbol declaration mode from the tags. *)
      let m =
        match ts with
        | []              -> Defin
        | Sym_const :: [] -> Const
        | Sym_inj   :: [] -> Injec
        | _               -> fatal cmd.pos "Multiple symbol tags."
      in
      (* We scope the type of the declaration. *)
      let a = fst (scope_basic ss a) in
      (* We check that [x] is not already used. *)
      if Sign.mem ss.signature x.elt then
        fatal x.pos "Symbol [%s] already exists." x.elt;
      (* We check that [a] is typable by a sort. *)
      Solve.sort_type Ctxt.empty a;
      (* Actually add the symbol to the signature and the state. *)
      let s = Sign.add_symbol ss.signature m x a in
      out 3 "(symb) %s.\n" s.sym_name;
      {ss with in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope}
  | P_rules(rs)                ->
      (* Scoping and checking each rule in turn. *)
      let handle_rule r =
        let (s,_,_) as r = scope_rule ss r in
        if !(s.sym_def) <> None then
          fatal_no_pos "Symbol [%s] cannot be (re)defined." s.sym_name;
        Sr.check_rule r; r
      in
      let rs = List.map handle_rule rs in
      (* Adding the rules all at once. *)
      let add_rule (s,h,r) =
        out 3 "(rule) %a\n" Print.pp_rule (s,h,r.elt);
        Sign.add_rule ss.signature s r.elt
      in
      List.iter add_rule rs; ss
  | P_definition(op,x,xs,ao,t) ->
      (* Desugaring of arguments and scoping of [t]. *)
      let t = if xs = [] then t else Pos.none (P_Abst(xs, t)) in
      let t = fst (scope_basic ss t) in
      (* Desugaring of arguments and scoping of [ao] (if not [None]). *)
      let fn a = if xs = [] then a else Pos.none (P_Prod(xs, a)) in
      let ao = Option.map fn ao in
      let ao = Option.map (fun a -> fst (scope_basic ss a)) ao in
      (* We check that [x] is not already used. *)
      if Sign.mem ss.signature x.elt then
        fatal x.pos "Symbol [%s] already exists." x.elt;
      (* We check that [t] has a type [a], and return it. *)
      let a =
        match ao with
        | Some(a) ->
            Solve.sort_type Ctxt.empty a;
            if Solve.check Ctxt.empty t a then a else
            fatal cmd.pos "Term [%a] does not have type [%a]." pp t pp a
        | None    ->
            match Solve.infer Ctxt.empty t with
            | Some(a) -> a
            | None    -> fatal cmd.pos "Cannot infer the type of [%a]." pp t
      in
      (* We check that no metavariable remains. *)
      let nb = List.length (Basics.get_metas t) in
      if nb > 0 then
        begin
          fatal_msg "The definition of [%s] contains [%i] metavariables.\n"
            x.elt nb;
          fatal x.pos "We have %s ≔ %a." x.elt pp t
        end;
      (* Actually add the symbol to the signature. *)
      let s = Sign.add_symbol ss.signature Defin x a in
      out 3 "(symb) %s (definition).\n" s.sym_name;
      (* Also add its definition, if it is not opaque. *)
      if not op then s.sym_def := Some(t);
      {ss with in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope}
  | P_theorem(x, a, ts, pe)    ->
      (* Scoping the type (statement) of the theorem, check sort. *)
      let a = fst (scope_basic ss a) in
      Solve.sort_type Ctxt.empty a;
      (* We check that [x] is not already used. *)
      if Sign.mem ss.signature x.elt then
        fatal x.pos "Symbol [%s] already exists." x.elt;
      (* Act according to the ending state. *)
      begin
        match pe with
        | P_proof_abort ->
            (* Just ignore the command, with a warning. *)
            wrn cmd.pos "Proof aborted."; ss
        | P_proof_admit ->
            (* Initialize the proof and plan the tactics. *)
            let st = Proof.init ss.builtins x a in
            let st = List.fold_left (Tactics.handle_tactic ss) st ts in
            (* If the proof is finished, display a warning. *)
            if Proof.finished st then wrn cmd.pos "You should add QED.";
            (* Add a symbol corresponding to the proof, with a warning. *)
            let s = Sign.add_symbol ss.signature Const x a in
            out 3 "(symb) %s (admit).\n" s.sym_name;
            wrn cmd.pos "Proof admitted.";
            {ss with in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope}
        | P_proof_QED   ->
            (* Initialize the proof and plan the tactics. *)
            let st = Proof.init ss.builtins x a in
            let st = List.fold_left (Tactics.handle_tactic ss) st ts in
            (* Check that the proof is indeed finished. *)
            if not (Proof.finished st) then
              fatal cmd.pos "The proof is not finished.";
            (* Add a symbol corresponding to the proof. *)
            let s = Sign.add_symbol ss.signature Const x a in
            out 3 "(symb) %s (QED).\n" s.sym_name;
            {ss with in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope}
      end
  | P_assert(must_fail, asrt)  ->
      let result =
        match asrt with
        | P_assert_typing(t,a) ->
            let t = fst (scope_basic ss t) in
            let a = fst (scope_basic ss a) in
            Solve.sort_type Ctxt.empty a;
            (try Solve.check Ctxt.empty t a with _ -> false)
        | P_assert_conv(t,u)   ->
            let t = fst (scope_basic ss t) in
            let u = fst (scope_basic ss u) in
            Eval.eq_modulo t u
      in
      if result = must_fail then fatal cmd.pos "Assertion failed."; ss
  | P_set(cfg)                 ->
      begin
        match cfg with
        | P_config_debug(e,s)     ->
            (* Just update the option, state not modified. *)
            Console.set_debug e s; ss
        | P_config_verbose(i)     ->
            (* Just update the option, state not modified. *)
            Console.verbose := i; ss
        | P_config_builtin(s,qid) ->
            (* Set the builtin symbol [s]. *)
            let sym = find_sym false ss qid in
            Sign.add_builtin ss.signature s sym;
            {ss with builtins = StrMap.add s sym ss.builtins}
        | P_config_binop(s,qid)   ->
            (* Define the binary operator [s]. *)
            let sym = find_sym false ss qid in
            Sign.add_binop ss.signature s sym; ss
      end
  | P_infer(t, cfg)            ->
      (* Infer the type of [t]. *)
      let t_pos = t.pos in
      let t = fst (scope_basic ss t) in
      let a =
        match Solve.infer [] t with
        | Some(a) -> Eval.eval cfg a
        | None    -> fatal t_pos "Cannot infer the type of [%a]." pp t
      in
      out 3 "(infr) %a : %a\n" pp t pp a; ss
  | P_normalize(t, cfg)        ->
      (* Infer a type for [t], and evaluate [t]. *)
      let t_pos = t.pos in
      let t = fst (scope_basic ss t) in
      let v =
        match Solve.infer [] t with
        | Some(_) -> Eval.eval cfg t
        | None    -> fatal t_pos "Cannot infer the type of [%a]." pp t
      in
      out 3 "(eval) %a\n" pp v; ss

(** [too_long] indicates the duration after which a warning should be given to
    indicate commands that take too long to execute. *)
let too_long = Pervasives.ref infinity

(** [handle_cmd ss cmd] is similar to [handle_cmd_aux ss cmd] but it adds some
    exception handling. In particular, the position of [cmd] is used on errors
    that lack a specific position. All exceptions except [Timeout] and [Fatal]
    are captured, although they should not occur. *)
let handle_cmd : sig_state -> command -> sig_state = fun ss cmd ->
  try
    let (tm, ss) = time (handle_cmd_aux ss) cmd in
    if Pervasives.(tm >= !too_long) then
      wrn cmd.pos "It took %.2f seconds to handle the command." tm;
    ss
  with
  | Timeout                as e -> raise e
  | Fatal(Some(Some(_)),_) as e -> raise e
  | Fatal(None         ,m)      -> fatal cmd.pos "Error on command.\n%s" m
  | Fatal(Some(None)   ,m)      -> fatal cmd.pos "Error on command.\n%s" m
  | e                           ->
      fatal cmd.pos "Uncaught exception [%s]." (Printexc.to_string e)
