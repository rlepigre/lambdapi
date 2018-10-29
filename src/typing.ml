(** Type-checking and inference *)

open Timed
open Console
open Terms
open Print

(** Logging function for typing. *)
let log_type = new_logger 't' "type" "debugging information for typing"
let log_type = log_type.logger

(** Type of a function to be called to check convertibility. *)
type conv_f = term -> term -> unit

(** [make_prod_domain ctx] builds a metavariable intended as a domain type for
    a product. It has access to the variables of the context [ctx]. *)
let make_prod_domain : Ctxt.t -> term = fun ctx ->
  Ctxt.make_meta ctx (Meta(fresh_meta Type 0, [||]))

(** [make_prod_codomain ctx a] builds a metavariable intended as the  codomain
    type for a product of domain type [a].  It has access to the variables  of
    the context [ctx] and a fresh variables corresponding to the argument. *)
let make_prod_codomain : Ctxt.t -> term -> tbinder = fun ctx a ->
  let x = Bindlib.new_var mkfree "x" in
  let b = Ctxt.make_meta ((x,a)::ctx) (Meta(fresh_meta Type 0, [||])) in
  Bindlib.unbox (Bindlib.bind_var x (lift b))

(** [infer_aux conv ctx t] infers a type for the term [t] in context [ctx]. In
    the process, the [conv] function is used as a convertibility test. In case
    of failure, the exception [Fatal] is raised. Note that we require [ctx] to
    be well-formed (with well-sorted types), and that the returned type can be
    assumed to be well-sorted. *)
let rec infer_aux : conv_f -> Ctxt.t -> term -> term = fun conv ctx t ->
  match unfold t with
  | Patt(_,_,_) -> assert false (* Forbidden case. *)
  | TEnv(_,_)   -> assert false (* Forbidden case. *)
  | Kind        -> assert false (* Forbidden case. *)
  | Wild        -> assert false (* Forbidden case. *)
  | TRef(_)     -> assert false (* Forbidden case. *)

  (* -------------------
      ctx ⊢ Type ⇒ Kind  *)
  | Type        -> Kind

  (* ---------------------------------
      ctx ⊢ Vari(x) ⇒ Ctxt.find x ctx  *)
  | Vari(x)     -> (try Ctxt.find x ctx with Not_found -> assert false)

  (* -------------------------------
      ctx ⊢ Symb(s) ⇒ !(s.sym_type)  *)
  | Symb(s,_)   -> Timed.(!(s.sym_type))

  (*  ctx ⊢ a ⇐ Type    ctx, x : a ⊢ b<x> ⇒ s
     -----------------------------------------
                ctx ⊢ Prod(a,b) ⇒ s            *)
  | Prod(a,b)   ->
      (* We ensure that [a] is of type [Type]. *)
      check_aux conv ctx a Type;
      (* We infer the type of the body, first extending the context. *)
      let (x,b) = Bindlib.unbind b in
      let s = infer_aux conv (Ctxt.add x a ctx) b in
      (* We check that [s] is a sort. *)
      begin
        match unfold s with
        | Type | Kind -> s
        | s           -> conv s Type; Type
      end

  (*  ctx ⊢ a ⇐ Type    ctx, x : a ⊢ t<x> ⇒ b<x>
     --------------------------------------------
             ctx ⊢ Abst(a,t) ⇒ Prod(a,b)          *)
  | Abst(a,t)   ->
      (* We ensure that [a] is of type [Type]. *)
      check_aux conv ctx a Type;
      (* We infer the type of the body, first extending the context. *)
      let (x,t) = Bindlib.unbind t in
      let b = infer_aux conv (Ctxt.add x a ctx) t in
      (* We build the product type by binding [x] in [b]. *)
      Prod(a, Bindlib.unbox (Bindlib.bind_var x (lift b)))

  (*  ctx ⊢ t ⇒ Prod(a,b)    ctx ⊢ u ⇐ a
     ------------------------------------
         ctx ⊢ Appl(t,u) ⇒ subst b u      *)
  | Appl(t,a)   ->
      let (t,u) =
        let len = Array.length a in
        if len = 0 then assert false;
        if len = 1 then (t, a.(0)) else
        (Appl(t, Array.sub a 0 (len-1)), a.(len-1))
      in
      (* We first infer a product type for [t]. *)
      let (a,b) =
        let c = Eval.whnf (infer_aux conv ctx t) in
        match c with
        | Prod(a,b) -> (a,b)
        | _         ->
            let a = make_prod_domain ctx in
            let b = make_prod_codomain ctx a in
            conv c (Prod(a,b)); (a,b)
      in
      (* We then check the type of [u] against the domain type. *)
      check_aux conv ctx u a;
      (* We produce the returned type. *)
      Bindlib.subst b u

  (*  ctx ⊢ term_of_meta m e ⇒ a
     ----------------------------
         ctx ⊢ Meta(m,e) ⇒ a      *)
  | Meta(m,e)   -> infer_aux conv ctx (term_of_meta m e)

(** [check_aux conv ctx t c] checks that the term [t] has type [c], in context
    [ctx]. In the process, the [conv] function is used as convertibility test.
    In case of failure, the exception [Fatal] is raised.  Note that we require
    [ctx] and [c] to be well-formed (with well-sorted types). *)
and check_aux : conv_f -> Ctxt.t -> term -> term -> unit = fun conv ctx t c ->
  match unfold t with
  | Patt(_,_,_) -> assert false (* Forbidden case. *)
  | TEnv(_,_)   -> assert false (* Forbidden case. *)
  | Kind        -> assert false (* Forbidden case. *)
  | Type        ->
      (* -------------------
          ctx ⊢ Type ⇐ Kind  *)
      begin
        match unfold c with
        | Kind -> ()
        | _    -> fatal_no_pos "[Kind] expected, [%a] given." pp c
      end
  | Abst(a,t)   ->
      (*  c → Prod(d,b)    a ~ d    ctx, x : A ⊢ t<x> ⇐ b<x>
         ----------------------------------------------------
                         ctx ⊢ Abst(a,t) ⇐ c                   *)
      begin
        (* We (hopefully) evaluate [c] to a product, and get its body. *)
        let b =
          let c = Eval.whnf c in
          match c with
          | Prod(d,b) -> conv d a; b (* Domains must be convertible. *)
          | _         -> (* Generate product type with codomain [a]. *)
              let b = make_prod_codomain ctx a in
              conv c (Prod(a,b)); b
        in
        (* We type-check the body with the codomain. *)
        let (x,t) = Bindlib.unbind t in
        check_aux conv (Ctxt.add x a ctx) t (Bindlib.subst b (Vari(x)))
      end
  | t           ->
      (*  ctx ⊢ t ⇒ a
         -------------
          ctx ⊢ t ⇐ a  *)
      conv (infer_aux conv ctx t) c

(** Type of a list of convertibility constraints. *)
type conv_constrs = (term * term) list

(** [infer ctx t] returns a pair [(a,cs)] where [a] is a type for the term [t]
    in the context [ctx], under unification constraints [cs].  In other words,
    the constraints of [cs] must be satisfied for [t] to have type [a] (in the
    context [ctx],  supposed well-formed).  The exception [Fatal] is raised in
    case of error (e.g., when [t] cannot be assigned a type). *)
let infer : Ctxt.t -> term -> term * conv_constrs = fun ctx t ->
  let constrs = Pervasives.ref [] in (* Accumulated constraints. *)
  let trivial = Pervasives.ref 0  in (* Number of trivial constraints. *)
  let conv a b =
    let open Pervasives in
    if Basics.eq a b then incr trivial
    else constrs := (a,b) :: !constrs
  in
  try
    let a = infer_aux conv ctx t in
    let constrs = Pervasives.(!constrs) in
    if !log_enabled then
      begin
        let trivial = Pervasives.(!trivial) in
        log_type (gre "infer [%a] yields [%a]") pp t pp a;
        let fn (a,b) = log_type "  assuming [%a] ~ [%a]" pp a pp b in
        List.iter fn constrs;
        if trivial > 0 then log_type "  with %i trivial constraints" trivial;
      end;
    (a, constrs)
  with e ->
    if !log_enabled then log_type (red "infer [%a] failed.") pp t;
    raise e

(** [check ctx t c] checks that the term [t] has type [c] in the context [ctx]
    and under the returned unification constraints.  The context [ctx] must be
    well-fomed, and the type [c] well-sorted. The exception [Fatal] is raised
    in case of error (e.g., when [t] definitely does not have type [c]). *)
let check : Ctxt.t -> term -> term -> conv_constrs = fun ctx t c ->
  let constrs = Pervasives.ref [] in (* Accumulated constraints. *)
  let trivial = Pervasives.ref 0  in (* Number of trivial constraints. *)
  let conv a b =
    let open Pervasives in
    if Basics.eq a b then incr trivial
    else constrs := (a,b) :: !constrs
  in
  try
    check_aux conv ctx t c;
    let constrs = Pervasives.(!constrs) in
    if !log_enabled then
      begin
        let trivial = Pervasives.(!trivial) in
        log_type (gre "check [%a] [%a]") pp t pp c;
        let fn (a,b) = log_type "  assuming [%a] ~ [%a]" pp a pp b in
        List.iter fn constrs;
        if trivial > 0 then log_type "  with %i trivial constraints" trivial;
      end;
    constrs
  with e ->
    if !log_enabled then log_type (red "check [%a] [%a] (failed)") pp t pp c;
    raise e
