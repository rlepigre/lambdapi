%{
open Extra
open Timed
open Pos
open Console
open Syntax
open Legacy_lexer

(** [get_args t] decomposes [t] into a head term and a list of arguments. Note
    that in the returned pair [(h,args)], [h] is never a [P_Appl] node. *)
let get_args : p_term -> p_term * (Pos.popt * p_term) list = fun t ->
  let rec get_args acc t =
    match t.elt with
    | P_Appl(u,v) -> get_args ((t.pos,v)::acc) u
    | _           -> (t, acc)
  in get_args [] t

(** [add_args t args] builds the application of the term [t] to the  arguments
    [args]. When [args] is empty, the returned value is exactly [t]. Note that
    this function is the inverse of [get_args] (in some sense). *)
let add_args : p_term -> (Pos.popt * p_term) list -> p_term =
  List.fold_left (fun t (p,u) -> Pos.make p (P_Appl(t,u)))

(** Representation of a reduction rule, with its context. *)
type old_p_rule = ((strloc * p_term option) list * p_term * p_term) Pos.loc

(** [translate_old_rule r] transforms the legacy representation of a rule into
    the new representation. This function will be removed soon. *)
let translate_old_rule : old_p_rule -> p_rule = fun r ->
  let (ctx, lhs, rhs) = r.elt in
  (* Check for (deprecated) annotations in the context. *)
  let get_var (x,ao) =
    let fn a = wrn a.pos "Ignored type annotation." in
    (if !verbose > 1 then Option.iter fn ao); x
  in
  let ctx = List.map get_var ctx in
  (* Find the minimum number of arguments a variable is applied to. *)
  let is_pat_var env x =
    not (List.mem x env) && List.exists (fun y -> y.elt = x) ctx
  in
  let arity = Hashtbl.create 7 in
  let rec compute_arities env t =
    let (h, args) = get_args t in
    let nb_args = List.length args in
    begin
      match h.elt with
      | P_Appl(_,_)      -> assert false (* Cannot happen. *)
      | P_Vari(x)        ->
          let (p,x) = x.elt in
          if p = [] && is_pat_var env x then
            begin
              try
                let n = Hashtbl.find arity x in
                if nb_args < n then Hashtbl.replace arity x nb_args
              with Not_found -> Hashtbl.add arity x nb_args
            end
      | P_Wild          -> ()
      | P_Type          -> ()
      | P_Prod(_,_)     -> fatal h.pos "Product in legacy pattern."
      | P_Meta(_,_)     -> fatal h.pos "Metaviable in legacy pattern."
      | P_Abst(xs,t)    ->
          begin
            match xs with
            | [(_, Some(a))] -> fatal a.pos "Annotation in legacy pattern."
            | [(x, None   )] -> compute_arities (x.elt::env) t
            | _              -> fatal h.pos "Invalid legacy pattern lambda."
          end
      | P_Patt(_,_)     -> fatal h.pos "Pattern in legacy rule."
      | P_Impl(_,_)     -> fatal h.pos "Implication in legacy pattern."
      | P_LLet(_,_,_,_) -> fatal h.pos "Let expression in legacy rule."
      | P_NLit(_)       -> fatal h.pos "Nat literal in legacy rule."
      | P_BinO(_,_,_)   -> fatal h.pos "Binary operator in legacy rule."
    end;
    List.iter (fun (_,t) -> compute_arities env t) args
  in
  compute_arities [] lhs;
  (* Check that all context variables occur in the LHS. *)
  let check_here x =
    try ignore (Hashtbl.find arity x.elt) with Not_found ->
      fatal x.pos "Variable [%s] does not occur in the LHS." x.elt
  in
  List.iter check_here ctx;
  (* Actually process the LHS and RHS. *)
  let rec build env t =
    let (h, lts) = get_args t in
    match h.elt with
    | P_Vari({elt = ([],x); _}) when is_pat_var env x ->
       let lts = List.map (fun (p,t) -> p,build env t) lts in
       let n =
         try Hashtbl.find arity x with Not_found ->
           assert false (* Unreachable. *)
       in
       let (lts1, lts2) = List.cut lts n in
       let ts1 = Array.of_list (List.map snd lts1) in
       add_args (Pos.make t.pos (P_Patt(Pos.make h.pos x, ts1))) lts2
    | _                                               ->
    match t.elt with
    | P_Vari(_)
    | P_Type
    | P_Wild          -> t
    | P_Prod(xs,b)    ->
        let (x,a) =
          match xs with
          | [(x, Some(a))] -> (x, build env a)
          | _              -> assert false (* Unreachable. *)
        in
        Pos.make t.pos (P_Prod([(x, Some(a))], build (x.elt::env) b))
    | P_Impl(a,b)     -> Pos.make t.pos (P_Impl(build env a, build env b))
    | P_Abst(xs,u)    ->
        let (x,a) =
          match xs with
          | [(x, ao)] -> (x, Option.map (build env) ao)
          | _         -> assert false (* Unreachable. *)
        in
        Pos.make t.pos (P_Abst([(x,a)], build (x.elt::env) u))
    | P_Appl(t1,t2)   -> Pos.make t.pos (P_Appl(build env t1, build env t2))
    | P_Meta(_,_)     -> fatal t.pos "Invalid legacy rule syntax."
    | P_Patt(_,_)     -> fatal h.pos "Pattern in legacy rule."
    | P_LLet(_,_,_,_) -> fatal h.pos "Let expression in legacy rule."
    | P_NLit(_)       -> fatal h.pos "Nat literal in legacy rule."
    | P_BinO(_,_,_)   -> fatal h.pos "Binary operator in legacy rule."
  in
  (* NOTE the computation order is important for setting arities properly. *)
  let lhs = build [] lhs in
  let rhs = build [] rhs in
  Pos.make r.pos (lhs, rhs)

let build_config : string -> string option -> Eval.config = fun s1 s2o ->
  try
    let open Eval in
    let config steps strategy =
      let steps =
        match steps with
        | None     -> None
        | Some(nb) -> Some(int_of_string nb)
      in
      {strategy; steps}
    in
    match (s1, s2o) with
    | ("SNF" , io         ) -> config io        SNF
    | ("HNF" , io         ) -> config io        HNF
    | ("WHNF", io         ) -> config io        WHNF
    | (i     , Some "SNF" ) -> config (Some(i)) SNF
    | (i     , Some "HNF" ) -> config (Some(i)) HNF
    | (i     , Some "WHNF") -> config (Some(i)) WHNF
    | (i     , None       ) -> config (Some(i)) NONE
    | (_     , _          ) -> raise Exit (* captured below *)
  with _ -> fatal_no_pos "Invalid command configuration."
%}

%token EOF
%token DOT
%token COMMA
%token COLON
%token EQUAL
%token ARROW
%token FARROW
%token LARROW
%token DEFEQ
%token L_PAR
%token R_PAR
%token L_SQB
%token R_SQB
%token EVAL
%token INFER
%token <bool> ASSERT
%token WILD
%token <string list> REQUIRE
%token TYPE
%token KW_DEF
%token KW_INJ
%token KW_THM
%token <string> ID
%token <string list * string> QID

%start line
%type <Syntax.command> line

%right ARROW FARROW

%%

line:
  | s=ID ps=param* COLON a=term DOT {
      let a = if ps = [] then a else make_pos $loc(a) (P_Prod(ps,a)) in
      make_pos $loc (P_symbol([Sym_const], make_pos $loc(s) s, a))
    }
  | KW_DEF s=ID COLON a=term DOT {
      make_pos $loc (P_symbol([], make_pos $loc(s) s, a))
    }
  | KW_INJ s=ID COLON a=term DOT {
      make_pos $loc (P_symbol([Sym_inj], make_pos $loc(s) s, a))
    }
  | KW_DEF s=ID COLON a=term DEFEQ t=term DOT {
      make_pos $loc (P_definition(false, make_pos $loc(s) s, [], Some(a), t))
    }
  | KW_DEF s=ID DEFEQ t=term DOT {
      make_pos $loc (P_definition(false, make_pos $loc(s) s, [], None, t))
    }
  | KW_DEF s=ID ps=param+ COLON a=term DEFEQ t=term DOT {
      make_pos $loc (P_definition(false, make_pos $loc(s) s, ps, Some(a), t))
    }
  | KW_DEF s=ID ps=param+ DEFEQ t=term DOT {
      make_pos $loc (P_definition(false, make_pos $loc(s) s, ps, None, t))
    }
  | KW_THM s=ID COLON a=term DEFEQ t=term DOT {
      make_pos $loc (P_definition(true , make_pos $loc(s) s, [], Some(a), t))
    }
  | KW_THM s=ID ps=param+ COLON a=term DEFEQ t=term DOT {
      make_pos $loc (P_definition(true , make_pos $loc(s) s, ps, Some(a), t))
    }
  | rs=rule+ DOT {
      make_pos $loc (P_rules(List.map translate_old_rule rs))
    }
  | EVAL t=term DOT {
      make_pos $loc (P_normalize(t, Eval.{strategy = SNF; steps = None}))
    }
  | EVAL c=eval_config t=term DOT {
      let c = Eval.(if c.strategy=NONE then {c with strategy=SNF} else c) in
      make_pos $loc (P_normalize(t, c))
    }
  | INFER t=term DOT {
      make_pos $loc (P_infer(t, Eval.{strategy = NONE; steps = None}))
    }
  | INFER c=eval_config t=term DOT {
      make_pos $loc (P_infer(t, c))
    }
  | mf=ASSERT t=aterm COLON a=term DOT {
      make_pos $loc (P_assert(mf, P_assert_typing(t,a)))
    }
  | mf=ASSERT t=aterm EQUAL u=term DOT {
      make_pos $loc (P_assert(mf, P_assert_conv(t,u)))
    }
  | r=REQUIRE    DOT {
      Pervasives.(!(Parser.require)) r;
      make_pos $loc (P_require(r, P_require_default))
    }
  | EOF {
      raise End_of_file
    }

eval_config:
  | L_SQB s=ID R_SQB              { build_config s None       }
  | L_SQB s1=ID COMMA s2=ID R_SQB { build_config s1 (Some s2) }

param:
  | L_PAR id=ID COLON te=term R_PAR { (make_pos $loc(id) id, Some(te)) }

context_item:
  | x=ID ao=option(COLON a=term { a }) { (make_pos $loc(x) x, ao) }

rule:
  | L_SQB c=separated_list(COMMA, context_item) R_SQB l=term LARROW r=term {
      make_pos $loc (c, l, r)
    }

sterm:
  | qid=QID            { make_pos $loc (P_Vari(make_pos $loc qid)) }
  | id=ID              { make_pos $loc (P_Vari(make_pos $loc ([], id))) }
  | WILD               { make_pos $loc P_Wild }
  | TYPE               { make_pos $loc P_Type }
  | L_PAR t=term R_PAR { t }

aterm:
  | t=aterm u=sterm { make_pos $loc (P_Appl(t,u)) }
  | t=sterm         { t }

term:
  | t=aterm { t }
  | x=ID COLON a=aterm ARROW b=term {
      make_pos $loc (P_Prod([(make_pos $loc(x) x, Some(a))], b))
    }
  | L_PAR x=ID COLON a=aterm R_PAR ARROW b=term {
      make_pos $loc (P_Prod([(make_pos $loc(x) x, Some(a))], b))
    }
  | a=term ARROW b=term {
      make_pos $loc (P_Impl(a, b))
    }
  | x=ID FARROW t=term {
      make_pos $loc (P_Abst([(make_pos $loc(x) x, None)], t))
    }
  | x=ID COLON a=aterm FARROW t=term {
      make_pos $loc (P_Abst([(make_pos $loc(x) x, Some(a))], t))
    }
%%
