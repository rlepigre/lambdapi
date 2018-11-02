(** Pretty-printing. *)

open Extra
open Terms

(** [pp_symbol h oc s] prints the name of the symbol [s] to channel [oc] using
    the printing hint [h] to decide qualification. *)
let pp_symbol : pp_hint -> sym pp = fun h oc s ->
  match h with
  | Nothing   -> Format.pp_print_string oc s.sym_name
  | Qualified -> Format.fprintf oc "%a.%s" Files.pp_path s.sym_path s.sym_name
  | Alias(a)  -> Format.fprintf oc "%s.%s" a s.sym_name
  | Binary(o) -> Format.fprintf oc "(%s)" o

(** [pp_tvar oc x] prints the term variable [x] to the channel [oc]. *)
let pp_tvar : tvar pp = fun oc x ->
  Format.pp_print_string oc (Bindlib.name_of x)

(** [pp_meta oc m] prints the uninstantiated meta-variable [m] to [oc]. *)
let pp_meta : meta pp = fun oc m ->
  Format.pp_print_string oc (meta_name m)

(** [pp_term oc t] prints the term [t] to the channel [oc]. *)
let pp_term : term pp = fun oc t ->
  let out oc fmt = Format.fprintf oc fmt in
  (* NOTE we apply the conventions used in [Parser.expr] for priorities. *)
  let rec pp (p : [`Func | `Appl | `Atom]) oc t =
    let pp_func = pp `Func in
    let pp_appl = pp `Appl in
    let pp_atom = pp `Atom in
    let pp_env oc ar =
      if Array.length ar <> 0 then out oc "[%a]" (Array.pp pp_appl ",") ar
    in
    let pp_term_env oc te =
      match te with
      | TE_Vari(m) -> out oc "%s" (Bindlib.name_of m)
      | _          -> assert false
    in
    match (unfold t, p) with
    (* Atoms are printed inconditonally. *)
    | (Vari(x)    , _    ) -> pp_tvar oc x
    | (Type       , _    ) -> out oc "TYPE"
    | (Kind       , _    ) -> out oc "KIND"
    | (Symb(s,h)  , _    ) -> pp_symbol h oc s
    | (Meta(m,e)  , _    ) -> out oc "%a%a" pp_meta m pp_env e
    | (Patt(_,n,e), _    ) -> out oc "&%s%a" n pp_env e
    | (TEnv(t,e)  , _    ) -> out oc "&%a%a" pp_term_env t pp_env e
    (* Applications are printed when priority is above [`Appl]. *)
    | (Appl(t,a)  , `Appl)
    | (Appl(t,a)  , `Func) ->
        out oc "%a %a" pp_appl t (Array.pp pp_atom " ") a
    (* Abstractions and products are only printed at priority [`Func]. *)
    | (Abst(a,t)  , `Func) ->
        let (x,t) = Bindlib.unbind t in
        out oc "λ(%a:%a), %a" pp_tvar x pp_func a pp_func t
    | (Prod(a,b)  , `Func) ->
        let (x,c) = Bindlib.unbind b in
        if Bindlib.binder_occur b then
          out oc "∀(%a:%a), %a" pp_tvar x pp_appl a pp_func c
        else out oc "%a ⇒ %a" pp_appl a pp_func c
    (* Anything else needs parentheses. *)
    | (_          , _    ) -> out oc "(%a)" pp_func t
  in
  pp `Func oc (cleanup t)

(** [pp] is a short synonym of [pp_term]. *)
let pp : term pp = pp_term

(** [pp_rule oc (s,h,r)] prints the rule [r] of symbol [s] (with printing hing
    [h]) to the output channel [oc]. *)
let pp_rule : (sym * pp_hint * rule) pp = fun oc (s,h,r) ->
  let lhs = Basics.add_args (Symb(s,h)) r.lhs in
  let (_, rhs) = Bindlib.unmbind r.rhs in
  Format.fprintf oc "%a → %a" pp lhs pp rhs
