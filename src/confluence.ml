(** Confluence checking.

    This module allows the translation of a signature in the TPDB format (used
    in the confluence competition. *)

open Extra
open Timed
open Console
open Terms

(** Logging function for the confluence checker interface. *)
let log_conf = new_logger 'c' "conf" "informations for the confluence checker"
let log_conf = log_conf.logger

(** [print_sym oc s] outputs the fully qualified name of [s] to [oc]. The name
    is prefixed by ["c_"], and moduls are separated with ["_"], not ["."]. *)
let print_sym : sym pp = fun oc s ->
  let print_path = List.pp Format.pp_print_string "_" in
  Format.fprintf oc "c_%a_%s" print_path s.sym_path s.sym_name
  
(** [print_patt oc p] outputs TPDB format corresponding to the pattern [p], to
    the channel [oc]. *)
let print_term : bool -> term pp = fun lhs ->
  let rec pp oc t =
    let out fmt = Format.fprintf oc fmt in
    match unfold t with
    (* Forbidden cases. *)
    | Meta(_,_)    -> assert false
    | TRef(_)      -> assert false
    | TEnv(_,_)    -> assert false
    | Wild         -> assert false
    | Kind         -> assert false
    (* Printing of atoms. *)
    | Vari(x)      -> out "v_%s" (Bindlib.name_of x)
    | Type         -> out "TYPE"
    | Symb(s,_)    -> print_sym oc s
    | Patt(i,n,ts) ->
        if ts = [||] then out "&%s" n else
        pp oc (Basics.add_args (Patt(i,n,[||])) ts)
    (* Applications are printed when priority is above [`Appl]. *)
    | Appl(t,args) ->
        Array.iter (fun _ -> out "app(") args;
        out "%a" pp t;
        Array.iter (fun u -> out ",%a)" pp u) args
    (* Abstractions and products are only printed at priority [`Func]. *)
    | Abst(a,t)    ->
        let (x, t) = Bindlib.unbind t in
        if lhs then out "lam(m_typ,\\v_%s.%a)" (Bindlib.name_of x) pp t
        else out "lam(%a,\\v_%s.%a)" pp a (Bindlib.name_of x) pp t
    | Prod(a,b)    ->
        let (x, b) = Bindlib.unbind b in
        out "pi(%a,\\v_%s.%a)" pp a (Bindlib.name_of x) pp b
  in pp

(** [print_rule oc s r] outputs the rule declaration corresponding [r] (on the
    symbol [s]), to the output channel [oc]. *)
let print_rule : Format.formatter -> sym -> rule -> unit = fun oc s r ->
  (* Print the pattern variables declarations. *)
  let get_patt_names : term list -> string list = fun ts ->
    let names = Pervasives.ref [] in
    let fn _ t =
      match t with
      | Patt(_,n,_) -> Pervasives.(names := n :: !names)
      | _           -> ()
    in
    List.iter (Basics.iter fn) ts;
    List.sort_uniq String.compare Pervasives.(!names)
  in
  let names = get_patt_names (Array.to_list r.lhs) in
  if names <> [] then
    begin
      let print_name oc x = Format.fprintf oc "  &%s : term" x in
      Format.fprintf oc "(VAR\n%a\n)\n" (List.pp print_name "\n") names
    end;
  (* Print the rewriting rule. *)
  let lhs = Basics.add_args (Symb(s,Qualified)) r.lhs in
  Format.fprintf oc "(RULES %a" (print_term true) lhs;
  let rhs = Basics.term_of_rhs r in
  Format.fprintf oc "\n    -> %a)\n" (print_term false) rhs

(** [to_TPDB oc sign] outputs a TPDB representation of the rewriting system of
    the signature [sign] to the output channel [oc]. *)
let to_TPDB : Format.formatter -> Sign.t -> unit = fun oc sign ->
  (* Get all the dependencies (every needed symbols and rewriting rules). *)
  let deps = Sign.dependencies sign in
  (* Function to iterate over every symbols. *)
  let iter_symbols : (sym -> unit) -> unit = fun fn ->
    let iter_symbols sign =
      StrMap.iter (fun _ (s,_) -> fn s) Sign.(!(sign.sign_symbols))
    in
    List.iter (fun (_, sign) -> iter_symbols sign) deps
  in
  (* Print the prelude. *)
  let prelude =
    [ "(FUN"
    ; "  lam  : term -> (term -> term) -> term"
    ; "  app  : term -> term -> term"
    ; "  pi   : term -> (term -> term) -> term"
    ; "  type : term"
    ; ")"
    ; ""
    ; "(COMMENT beta-reduction)"
    ; "(VAR"
    ; "  v_x   : term"
    ; "  m_typ : term"
    ; "  m_B   : term"
    ; "  m_F   : term -> term"
    ; ")"
    ; "(RULES app(lam(m_typ,\\v_x. m_F v_x), m_B) -> m_F(m_B))"
    ; ""
    ; "(COMMENT TYPE keyword)"
    ; "(FUN TYPE : term)" ]
  in
  List.iter (Format.fprintf oc "%s\n") prelude;
  (* Print the symbol declarations. *)
  Format.fprintf oc "\n(COMMENT symbols)\n";
  let print_symbol s = Format.fprintf oc "(FUN %a : term)\n" print_sym s in
  iter_symbols print_symbol;
  (* Print the rewriting rules. *)
  Format.fprintf oc "\n(COMMENT rewriting rules)\n";
  let print_rules s =
    match !(s.sym_def) with
    | Some(d) -> Format.fprintf oc "(RULES %a\n" print_sym s;
                 Format.fprintf oc "    -> %a)\n" (print_term false) d
    | None    -> List.iter (print_rule oc s) !(s.sym_rules)
  in
  iter_symbols print_rules

(** [check cmd sign] runs the confluence checker specified by command [cmd] on
    the rewrite system of signature [sign]. The return value is [Some true] in
    the case where the system is confluent.  It is [Some false] if the  system
    is not confluent, and it is [None] if the tool cannot conclude.  Note that
    it is assumed that [cmd] corresponds to a command that accepts TPSP format
    on its standard output, and outputs either ["YES"], ["NO"] or ["MAYBE"] as
    the first line of its standard output. The exception [Fatal] may be raised
    if [cmd] does not behave as expected. *)
let check : string -> Sign.t -> bool option = fun cmd sign ->
  (* Run the command. *)
  if !log_enabled then log_conf "Running command [%s]" cmd;
  let (ic, oc, ec) = Unix.open_process_full cmd (Unix.environment ()) in
  (* Feed it the TPDB problem. *)
  to_TPDB (Format.formatter_of_out_channel oc) sign;
  flush oc; close_out oc;
  if !log_enabled then log_conf "Wrote the data and closed the pipe.";
  (* Read the answer (and possible error messages). *)
  let out = input_lines ic in
  if !log_enabled && out <> [] then
    begin
      log_conf "==== Data written to [stdout] ====";
      List.iter (log_conf "%s") out;
      log_conf "==================================";
    end;
  let err = input_lines ec in
  if !log_enabled && err <> [] then
    begin
      log_conf "==== Data written to [stderr] ====";
      List.iter (log_conf "%s") err;
      log_conf "=================================="
    end;
  (* Terminate the process. *)
  match (Unix.close_process_full (ic, oc, ec), out) with
  | (Unix.WEXITED 0  , "YES"  ::_) -> Some true
  | (Unix.WEXITED 0  , "NO"   ::_) -> Some false
  | (Unix.WEXITED 0  , "MAYBE"::_) -> None
  | (Unix.WEXITED 0  , []        ) ->
      fatal_no_pos "The confluence checker prodced no output."
  | (Unix.WEXITED 0  , _         ) ->
      fatal_no_pos "The confluence checker gave an unexpected answer."
  | (Unix.WEXITED i  , _         ) ->
      fatal_no_pos "The confluence checker returned with code [%i]." i
  | (Unix.WSIGNALED i, _         ) ->
      fatal_no_pos "The confluence checker was killed by signal [%i]." i
  | (Unix.WSTOPPED  i, _         ) ->
      fatal_no_pos "The confluence checker was stopped by signal [%i]." i

(* NOTE the simplest, valid confluence checking command is ["echo MAYBE"]. The
   command ["cat > out.txt; echo MAYBE"] can conveniently be used to write the
   generated TPDB problem to the file ["out.txt"] for debugging purposes. *)
