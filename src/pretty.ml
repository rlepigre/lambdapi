(** Pretty-printing the parser-level AST. *)

open Extra
open Files
open Pos
open Syntax

let pp_ident : ident pp = fun oc id ->
  Format.pp_print_string oc id.elt

let pp_qident : qident pp = fun oc qid ->
  match qid.elt with
  | ([], id) -> Format.pp_print_string oc id
  | (mp, id) -> List.iter (Format.fprintf oc "%s.") mp;
                Format.pp_print_string oc id

let pp_symtag : symtag pp = fun oc tag ->
  match tag with
  | Sym_const -> Format.pp_print_string oc "const"
  | Sym_inj   -> Format.pp_print_string oc "injective"

let pp_symtags : symtag list pp = fun oc ->
  List.iter (Format.fprintf oc " %a" pp_symtag)

let rec pp_p_term : p_term pp = fun oc t ->
  let open Parser in
  let out fmt = Format.fprintf oc fmt in
  let rec pp p _ t =
    let pp_env _ ar =
      if Array.length ar > 0 then out "[%a]" (Array.pp (pp PFunc) ", ") ar
    in
    let pp_atom = pp PAtom in
    let pp_appl = pp PAppl in
    let pp_func = pp PFunc in
    match (t.elt, p) with
    | (P_Type            , _    ) -> out "TYPE"
    | (P_Vari(qid)       , _    ) -> out "%a" pp_qident qid
    | (P_Wild            , _    ) -> out "_"
    | (P_Meta(x,ar)      , _    ) -> out "?%a%a" pp_ident x pp_env ar
    | (P_Patt(x,ar)      , _    ) -> out "&%a%a" pp_ident x pp_env ar
    | (P_Appl(t,u)       , PAppl)
    | (P_Appl(t,u)       , PFunc) -> out "%a@ %a" pp_appl t pp_atom u
    | (P_Impl(a,b)       , PFunc) -> out "%a@ ⇒ %a" pp_appl a pp_func b
    | (P_Abst(args,t)    , PFunc) -> out "λ%a,@ %a" pp_p_args args pp_func t
    | (P_Prod(args,b)    , PFunc) -> out "∀%a,@ %a" pp_p_args args pp_func b
    | (P_LLet(x,args,t,u), PFunc) ->
        out "@[<hov 2>let %a%a = %a@]@ in@ %a"
          pp_ident x pp_p_args args pp_func t pp_func u
    | (P_NLit(i)         , _    ) -> out "%i" i
    | (P_BinO(t,b,u)     , _    ) ->
        let (b, _, _, _) = b in
        out "(%a %s %a)" pp_atom t b pp_atom u
    | (_                 , _    ) -> out "(%a)" pp_func t
  in
  let rec pp_toplevel _ t =
    match t.elt with
    | P_Abst(args,t)     -> out "λ%a,@ %a" pp_p_args args pp_toplevel t
    | P_Prod(args,b)     -> out "∀%a,@ %a" pp_p_args args pp_toplevel b
    | P_Impl(a,b)        -> out "%a@ ⇒ %a" (pp PAppl) a pp_toplevel b
    | P_LLet(x,args,t,u) -> out "@[<hov 2>let %a%a =@ %a@]@ in@ %a" pp_ident x
                              pp_p_args args pp_toplevel t pp_toplevel u
    | _                  -> out "@[<hov 2>%a@]" (pp PFunc) t
  in
  pp_toplevel oc t

and pp_p_arg : p_arg pp = fun oc (id,ao) ->
  match ao with
  | None    -> Format.pp_print_string oc id.elt
  | Some(a) -> Format.fprintf oc "(%s : %a)" id.elt pp_p_term a

and pp_p_args : p_arg list pp = fun oc ->
  List.iter (Format.fprintf oc " %a" pp_p_arg)

let pp_p_rule : p_rule pp = fun oc r ->
  let (lhs, rhs) = r.elt in
  Format.fprintf oc "@[<hov 3>rule %a@ → %a@]@?" pp_p_term lhs pp_p_term rhs

let pp_p_proof_end : p_proof_end pp = fun oc e ->
  match e with
  | P_proof_QED   -> Format.pp_print_string oc "qed"
  | P_proof_admit -> Format.pp_print_string oc "admit"
  | P_proof_abort -> Format.pp_print_string oc "abort"

let pp_p_rw_patt : p_rw_patt pp = fun oc p ->
  let out fmt = Format.fprintf oc fmt in
  match p with
  | P_rw_Term(t)               -> out "%a" pp_p_term t
  | P_rw_InTerm(t)             -> out "in %a" pp_p_term t
  | P_rw_InIdInTerm(x,t)       -> out "in %a in %a" pp_ident x pp_p_term t
  | P_rw_IdInTerm(x,t)         -> out "%a in %a" pp_ident x pp_p_term t
  | P_rw_TermInIdInTerm(u,x,t) -> out "%a in %a in %a" pp_p_term u
                                    pp_ident x pp_p_term t
  | P_rw_TermAsIdInTerm(u,x,t) -> out "%a as %a in %a" pp_p_term u
                                    pp_ident x pp_p_term t

let pp_p_tactic : p_tactic pp = fun oc t ->
  let out fmt = Format.fprintf oc fmt in
  match t.elt with
  | P_tac_refine(t)          -> out "@[<hov 2>refine@ %a@]" pp_p_term t
  | P_tac_intro(xs)          -> out "intro %a" (List.pp pp_ident " ") xs
  | P_tac_apply(t)           -> out "@[<hov 2>apply@ %a@]" pp_p_term t
  | P_tac_simpl              -> out "simpl"
  | P_tac_rewrite(None   ,t) -> out "@[<hov 2>rewrite@ %a@]" pp_p_term t
  | P_tac_rewrite(Some(p),t) -> out "@[<hov 2>rewrite [%a]@ %a@]"
                                  pp_p_rw_patt p.elt pp_p_term t
  | P_tac_refl               -> out "reflexivity"
  | P_tac_sym                -> out "symmetry"
  | P_tac_focus(i)           -> out "focus %i" i
  | P_tac_print              -> out "print"
  | P_tac_proofterm          -> out "proofterm"

let pp_p_assertion : p_assertion pp = fun oc asrt ->
  let out fmt = Format.fprintf oc fmt in
  match asrt with
  | P_assert_typing(t,a) -> out "%a@ : %a" pp_p_term t pp_p_term a
  | P_assert_conv(t,u)   -> out "%a@ ≡ %a" pp_p_term t pp_p_term u

let pp_command : command pp = fun oc cmd ->
  let out fmt = Format.fprintf oc fmt in
  match cmd.elt with
  | P_require(m, P_require_default) ->
      out "require %a" pp_path m
  | P_require(m, P_require_open   ) ->
      out "require open %a" pp_path m
  | P_require(m, P_require_as(i)  ) ->
      out "require %a as %s" pp_path m i.elt
  | P_open(m)                       ->
      out "open %a" pp_path m
  | P_symbol(tags,s,a)              ->
      out "@[<hov 2>symbol%a %s :@ @[%a@]@]"
        pp_symtags tags s.elt pp_p_term a
  | P_rules(rs)                     ->
      out "%a" (List.pp pp_p_rule "\n") rs
  | P_definition(_,s,args,ao,t)     ->
      out "@[<hov 2>definition %s" s.elt;
      List.iter (out " %a" pp_p_arg) args;
      Option.iter (out " :@ @[<hov>%a@]" pp_p_term) ao;
      out " ≔@ @[<hov>%a@]@]" pp_p_term t
  | P_theorem(s,a,ts,e)             ->
      out "@[<hov 2>theorem %s :@ @[<2>%a@]@]@." s.elt pp_p_term a;
      out "proof@.";
      List.iter (out "  @[<hov>%a@]@." pp_p_tactic) ts;
      out "%a" pp_p_proof_end e
  | P_assert(true , asrt)           ->
      out "assertnot %a" pp_p_assertion asrt
  | P_assert(false, asrt)           ->
      out "assert %a" pp_p_assertion asrt
  | P_set(P_config_verbose(i)    )  ->
      out "set verbose %i" i
  | P_set(P_config_debug(true ,s))  ->
      out "set debug \"+%s\"" s
  | P_set(P_config_debug(false,s))  ->
      out "set debug \"-%s\"" s
  | P_set(P_config_builtin(n,i)  )  ->
      out "set builtin %S ≔ %a" n pp_qident i
  | P_set(P_config_binop(binop)  )  ->
      let (s, a, p, qid) = binop in
      let a =
        match a with
        | Assoc_none  -> ""
        | Assoc_left  -> "l"
        | Assoc_right -> "r"
      in
      out "set infix%s %f %S ≔ %a" a p s pp_qident qid
  | P_infer(t, _)                   ->
      out "@[<hov 4>infer %a@]" pp_p_term t
  | P_normalize(t, _)               ->
      out "@[<hov 2>normalize@ %a@]" pp_p_term t

let rec pp_ast : ast pp = fun oc cs ->
  match cs with
  | []    -> ()
  | [c]   -> Format.fprintf oc "%a@." pp_command c
  | c::cs -> Format.fprintf oc "%a\n@.%a" pp_command c pp_ast cs

(** [beautify cmds] pretty-prints the commands [cmds] to standard output. *)
let beautify : ast -> unit =
  pp_ast Format.std_formatter
