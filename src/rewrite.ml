(** Implementation of the REWRITE tactic. *)

open Timed
open Extra
open Pos
open Terms
open Basics
open Console
open Proof
open Print

(** Logging function for the rewrite tactic. *)
let log_rewr = new_logger 'w' "rewr" "informations for the rewrite tactic"
let log_rewr = log_rewr.logger

(** Rewrite pattern. *)
type rw_patt =
  | RW_Term           of term
  | RW_InTerm         of term
  | RW_InIdInTerm     of (term, term) Bindlib.binder
  | RW_IdInTerm       of (term, term) Bindlib.binder
  | RW_TermInIdInTerm of term * (term, term) Bindlib.binder
  | RW_TermAsIdInTerm of term * (term, term) Bindlib.binder

(** Equality configuration. *)
type eq_config =
  { symb_P     : sym * pp_hint (** Encoding of propositions.        *)
  ; symb_T     : sym * pp_hint (** Encoding of types.               *)
  ; symb_eq    : sym * pp_hint (** Equality proposition.            *)
  ; symb_eqind : sym * pp_hint (** Induction principle on equality. *)
  ; symb_refl  : sym * pp_hint (** Reflexivity of equality.         *) }

(** [get_eq_config ()] returns the current configuration for equality, used by
    tactics such as “rewrite” or “reflexivity”. *)
let get_eq_config : Pos.strloc -> builtins -> eq_config = fun name builtins ->
  let {elt = id; pos} = name in
  let find_sym key =
    try StrMap.find key builtins with Not_found ->
    fatal pos "Builtin symbol [%s] undefined in the proof of [%s]." key id
  in
  { symb_P     = find_sym "P"
  ; symb_T     = find_sym "T"
  ; symb_eq    = find_sym "eq"
  ; symb_eqind = find_sym "eqind"
  ; symb_refl  = find_sym "refl" }

(** [get_eq_data cfg a] extra data from an equality type [a]. It consists of a
    triple containing the type in which equality is used and the equated terms
    (LHS and RHS). *)
let get_eq_data : eq_config -> term -> term * term * term = fun cfg a ->
  match get_args a with
  | (p, [|eq|]) when is_symb (fst cfg.symb_P) p ->
      begin
        match get_args eq with
        | (e, [|a;l;r|]) when is_symb (fst cfg.symb_eq) e -> (a, l, r)
        | _                                               ->
            fatal_no_pos "Expected an equality type, found [%a]." pp a
      end
  | _                                           ->
      fatal_no_pos "Expected an equality type, found [%a]." pp a

(** Type of a term with the free variables that need to be substituted (during
    some unification process).  It is usually used to store the LHS of a proof
    of equality, together with the variables that were quantified over. *)
type to_subst = tvar array * term

(** [add_refs t] substitutes each wildcard of [t] using a fresh reference cell
    ([TRef] constructor). This is used for unification, by performing  all the
    substitutions in-place. *)
let rec add_refs : term -> term = fun t ->
  match unfold t with
  | Wild         -> TRef(ref None)
  | Appl(h,args) -> Appl(add_refs h, Array.map add_refs args)
  | _            -> t

(** [break_prod a] eliminates the products at the surface of [a],  and returns
    the remaining term the variables that used to correspond to the eliminated
    products. These variables may appear free in the returned term. *)
let break_prod : term -> term * tvar array = fun a ->
  let rec aux : term -> tvar list -> term * tvar array = fun a vs ->
    match unfold a with
    | Prod(_,b) -> let (v,b) = Bindlib.unbind b in aux b (v::vs)
    | a         -> (a, Array.of_list (List.rev vs))
  in aux a []

(** [match_pattern (xs,p) t] attempts to match the pattern [p] (containing the
    “pattern variables” of [xs]) with the term [t]. If successful,  it returns
    [Some(ts)] where [ts] is an array of terms such that substituting elements
    of [xs] by the corresponding elements of [ts] in [p] yields a term that is
    equal to [t] (in terms of [eq]). *)
let match_pattern : to_subst -> term -> term array option = fun (xs,p) t ->
  let ts = Array.map (fun _ -> TRef(ref None)) xs in
  let p = Bindlib.msubst (Bindlib.unbox (Bindlib.bind_mvar xs (lift p))) ts in
  if Basics.eq p t then Some(Array.map unfold ts) else None

(** [find_subst t (xs,p)] is given a term [t] and a pattern [p] (with “pattern
    variables” of [xs]),  and it finds the first instance of (a term matching)
    [p] in [t] (if there is any). If successful, the function returns an array
    of terms corresponding to the substitution (see [match_pattern]). *)
let find_subst : term -> to_subst -> term array option = fun t (xs,p) ->
  let time = Time.save () in
  let rec find_subst : term list -> term array option = fun l ->
    match l with
    | []   -> None
    | t::l ->
    match match_pattern (xs,p) t with
    | None ->
        begin
          Time.restore time;
          match unfold t with
          | Appl(t,a) -> find_subst ((t :: Array.to_list a) @ l)
          | _         -> find_subst l
        end
    | sub  -> sub
  in
  find_subst [t]

(** [make_pat t p] is given a term [t], and a pattern [p] containing reference
    cells (that are not instantiated) and wildcards.  It then tries to find  a
    subterm of [t] that matches [p], using (instantiating) syntactic equality.
    In case of success, the function returns [true],  and the matching term is
    [p] itself (through instantiation). *)
let make_pat : term -> term -> bool = fun t p ->
  let time = Time.save () in
  let rec make_pat : term list -> bool = fun l ->
    match l with
    | []                      -> false
    | t::_ when Basics.eq t p -> true
    | t::l                    ->
        Time.restore time;
        match unfold t with
        | Appl(t,a) -> make_pat ((t :: Array.to_list a) @ l)
        | _         -> make_pat l
  in
  make_pat [t]

(** [bind_match p t] binds every occurence of the pattern [p] in the term [t].
    We require [t] not to contain products, abstractions, metavariables or any
    other awkward term constructor. *)
let bind_match : term -> term -> tbinder =  fun p t ->
  let x = Bindlib.new_var mkfree "X" in
  let rec lift_subst : term -> tbox = fun t ->
    if Basics.eq p t then _Vari x else
    match unfold t with
    | Vari(y)     -> _Vari y
    | Type        -> _Type
    | Kind        -> _Kind
    | Symb(s,h)   -> _Symb s h
    | Appl(t,a)   -> _Appl (lift_subst t) (Array.map lift_subst a)
    (* For now, we fail on products, abstractions and metavariables. *)
    | Prod(_)     -> fatal_no_pos "Cannot rewrite under products."
    | Abst(_)     -> fatal_no_pos "Cannot rewrite under abstractions."
    | Meta(_)     -> fatal_no_pos "Cannot rewrite metavariables."
    (* Forbidden cases. *)
    | Patt(_,_,_) -> assert false
    | TEnv(_,_)   -> assert false
    | Wild        -> assert false
    | TRef(_)     -> assert false
  in
  Bindlib.(unbox (bind_var x (lift_subst t)))

(* NOTE in [bind_match] we lift while matching for efficiency. *)

(** [rewrite ps po t] rewrites according to the equality proved by [t] in  the
    current goal of [ps].  The term [t] should have a type corresponding to an
    equality. Every occurrence of the first instance of the left-hand side  is
    replaced by the right-hand side of the obtained proof. It also handles the
    full set of SSReflect patterns. *)
let rewrite : Proof.t -> rw_patt option -> term -> term = fun ps p t ->
  (* Obtain the required symbols from the current signature. *)
  let cfg = get_eq_config ps.proof_name ps.proof_builtins in

  (* Get the focused goal. *)
  let g =
    try List.hd Proof.(ps.proof_goals) with Failure(_)  ->
      fatal_no_pos "No remaining goals..."
  in

  (* Infer the type of [t] (the argument given to the tactic). *)
  let (g_env, g_type) = Goal.get_type g in
  let g_ctxt = Ctxt.of_env g_env in
  let t_type =
    match Solve.infer g_ctxt t with
    | Some(a) -> a
    | None    -> fatal_no_pos "Cannot infer the type of [%a]." pp t
  in

  (* Check that the type of [t] is of the form “P (Eq a l r)”. *)
  let (t_type, vars) = break_prod t_type in
  let (a, l, r)  = get_eq_data cfg t_type in

  (* Apply [t] to the variables of [vars] to get a witness of the equality. *)
  let t_args = Basics.add_args t (Array.map mkfree vars) in

  (* Bind the variables in this new witness. *)
  let bound =
    let triple = Bindlib.box_triple (lift t_args) (lift l) (lift r) in
    Bindlib.unbox (Bindlib.bind_mvar vars triple)
  in

  (* Extract the term from the goal type (get “t” from “P t”). *)
  let g_term =
    match get_args g_type with
    | (p, [|t|]) when is_symb (fst cfg.symb_P) p -> t
    | _                                          ->
        fatal_no_pos "Goal type [%a] is not of the form “P t”." pp g_type
  in

  (* Obtain the different components depending on the pattern. *)
  let (pred_bind, new_term, t, l, r) =
    match p with
    (* Simple rewrite, no pattern. *)
    | None                         ->
        (* Build a substitution from the first instance of [l] in the goal. *)
        let sigma =
          match find_subst g_term (vars, l) with
          | Some(sigma) -> sigma
          | None        -> fatal_no_pos "No subterm of [%a] matches [%a]."
                             pp g_term pp l
        in
        (* Build the required data from that substitution. *)
        let (t, l, r) = Bindlib.msubst bound sigma in
        let pred_bind = bind_match l g_term in
        (pred_bind, Bindlib.subst pred_bind r, t, l, r)

    (* Basic patterns. *)
    | Some(RW_Term(p)            ) ->
        (* Find a subterm [match_p] of the goal that matches [p]. *)
        let match_p =
          let p_refs = add_refs p in
          if not (make_pat g_term p_refs) then
            fatal_no_pos "No subterm of [%a] matches [%a]." pp g_term pp p;
          p_refs (* [TRef] cells have been instantiated here. *)
        in
        (* Build a substitution by matching [match_p] with the LHS [l]. *)
        let sigma =
          match match_pattern (vars,l) match_p with
          | Some(sigma) -> sigma
          | None        -> fatal_no_pos "No subterm of [%a] matches [%a]."
                             pp match_p pp l
        in
        (* Build the data from the substitution. *)
        let (t, l, r) = Bindlib.msubst bound sigma in
        let pred_bind = bind_match l g_term in
        (pred_bind, Bindlib.subst pred_bind r, t, l, r)

    (* Nested patterns. *)
    | Some(RW_InTerm(p)          ) ->
        (* Find a subterm [match_p] of the goal that matches [p]. *)
        let match_p =
          let p_refs = add_refs p in
          if not (make_pat g_term p_refs) then
            fatal_no_pos "No subterm of [%a] matches [%a]." pp g_term pp p;
          p_refs (* [TRef] cells have been instantiated here. *)
        in
        (* Build a substitution from a subterm of [match_p] matching [l]. *)
        let sigma =
          match find_subst match_p (vars,l) with
          | Some(sigma) -> sigma
          | None        ->
              fatal_no_pos "No subterm of the pattern [%a] matches [%a]."
                pp match_p pp l
        in
        (* Build the data from the substitution. *)
        let (t, l, r) = Bindlib.msubst bound sigma in
        let p_x = bind_match l match_p in
        let p_r = Bindlib.subst p_x r in
        let pred_bind = bind_match match_p g_term in
        let new_term = Bindlib.subst pred_bind p_r in
        let (x, p_x) = Bindlib.unbind p_x in
        let pred_box = lift (Bindlib.subst pred_bind p_x) in
        let pred_bind = Bindlib.unbox (Bindlib.bind_var x pred_box) in
        (pred_bind, new_term, t, l, r)

    | Some(RW_IdInTerm(p)        ) ->
        (* The code here works as follows: *)
        (* 1 - Try to match [p] with some subterm of the goal. *)
        (* 2 - If we succeed we do two things, we first replace [id] with its
               value, [id_val], the value matched to get [pat_l] and  try to
               match [id_val] with the LHS of the lemma. *)
        (* 3 - If we succeed we create the "RHS" of the pattern, which is [p]
               with [sigma r] in place of [id]. *)
        (* 4 - We then construct the following binders:
               a - [pred_bind_l] : A binder with a new variable replacing each
                   occurrence of [pat_l] in g_term.
               b - [pred_bind] : A binder with a new variable only replacing
                   the subterms where a rewrite happens. *)
        (* 5 - The new goal [new_term] is constructed by substituting [r_pat]
               in [pred_bind_l]. *)
        let (id,p) = Bindlib.unbind p in
        let p_refs = add_refs p in
        let id_val =
          match find_subst g_term ([|id|],p_refs) with
          | Some(id_val) -> id_val.(0)
          | None         ->
              fatal_no_pos "The pattern [%a] does not match [%a]." pp p pp l
        in
        let pat = Bindlib.unbox (Bindlib.bind_var id (lift p_refs)) in
        (* The LHS of the pattern, i.e. the pattern with id replaced by *)
        (* id_val. *)
        let pat_l = Bindlib.subst pat id_val in

        (* This must match with the LHS of the equality proof we use. *)
        let sigma =
          match match_pattern (vars,l) id_val with
          | Some(sigma) -> sigma
          | None        ->
              fatal_no_pos
                "The value of [%s], [%a], in [%a] does not match [%a]."
                (Bindlib.name_of id) pp id_val pp p pp l
        in
        (* Build t, l, using the substitution we found. Note that r  *)
        (* corresponds to the value we get by applying rewrite to *)
        (* id val. *)
        let (t,l,r) = Bindlib.msubst bound sigma in

        (* The RHS of the pattern, i.e. the pattern with id replaced *)
        (* by the result of rewriting id_val. *)
        let pat_r = Bindlib.subst pat r in

        (* Build the predicate, identifying all occurrences of pat_l *)
        (* substituting them, first with pat_r, for the new goal and *)
        (* then with l_x for the lambda term. *)
        let pred_bind_l = bind_match pat_l g_term in

        (* This will be the new goal. *)
        let new_term = Bindlib.subst pred_bind_l pat_r in

        (* [l_x] is the pattern with [id] replaced by the variable X *)
        (* that we use for building the predicate. *)
        let (x, l_x) = Bindlib.unbind pat in
        let pred_box = lift (Bindlib.subst pred_bind_l l_x) in
        let pred_bind = Bindlib.unbox (Bindlib.bind_var x pred_box) in
        (pred_bind, new_term, t, l, r)

    (* Combinational patterns. *)
    | Some(RW_TermInIdInTerm(s,p)) ->
        (* This pattern combines the previous.  First, we identify the subterm
           of [g_term] that matches with [p] where [p] contains an identifier.
           Once we have the value that the identifier in [p] has been  matched
           to, we find a subterm of it that matches with [s].  Then in all the
           occurrences of the first instance of [p] in [g_term] we rewrite all
           occurrences of the first instance of [s] in the subterm of [p] that
           was matched with the identifier. *)
        let (id,p) = Bindlib.unbind p in
        let p_refs = add_refs p in
        let id_val =
          match find_subst g_term ([|id|],p_refs) with
          | Some(id_val) -> id_val
          | None         ->
              fatal_no_pos "The pattern [%a] does not match [%a]." pp p pp l
        in
        (* Once we get the value of id, we work with that as our main term
           since this is where s will appear and will be substituted in. *)
        let id_val = id_val.(0) in
        (* [pat] is the full value of the pattern, with the wildcards now
           replaced by subterms of the goal and [id]. *)
        let pat = Bindlib.unbox (Bindlib.bind_var id (lift p_refs)) in
        let pat_l = Bindlib.subst pat id_val in

        (* We then try to match the wildcards in [s] with subterms of
           [id_val]. *)
        let s_refs = add_refs s in
        if not (make_pat id_val s_refs) then
          fatal_no_pos "The value of [%s], [%a], in [%a] does not match [%a]."
            (Bindlib.name_of id) pp id_val pp p pp s;
        (* Now we must match s, which no longer contains any TRef's
           with the LHS of the lemma,*)
        let s = s_refs in
        let sigma =
          match match_pattern (vars,l) s with
          | Some(sigma) -> sigma
          | None        ->
              fatal_no_pos "The term [%a] does not match the LHS [%a]"
                pp s pp l
        in
        let (t,l,r) = Bindlib.msubst bound sigma in

        (* First we work in [id_val], that is, we substitute all
           the occurrences of [l] in [id_val] with [r]. *)
        let id_bind = bind_match l id_val in

        (* [new_id] is the value of [id_val] with [l] replaced
           by [r] and [id_x] is the value of [id_val] with the
           free variable [x]. *)
        let new_id = Bindlib.subst id_bind r in
        let (x, id_x) = Bindlib.unbind id_bind in

        (* Then we replace in pat_l all occurrences of [id]
           with [new_id]. *)
        let pat_r = Bindlib.subst pat new_id in

        (* To get the new goal we replace all occurrences of
          [pat_l] in [g_term] with [pat_r]. *)
        let pred_bind_l = bind_match pat_l g_term in

        (* [new_term] is the type of the new goal meta. *)
        let new_term = Bindlib.subst pred_bind_l pat_r in

        (* Finally we need to build the predicate. First we build
           the term l_x, in a few steps. We substitute all the
           rewrites in new_id with x and we repeat some steps. *)
        let l_x = Bindlib.subst pat id_x in

        (* The last step to build the predicate is to substitute
           [l_x] everywhere we find [pat_l] and bind that x. *)
        let pred = Bindlib.subst pred_bind_l l_x in
        let pred_bind = Bindlib.bind_var x (lift pred) in
        (Bindlib.unbox pred_bind, new_term, t, l, r)

    | Some(RW_TermAsIdInTerm(s,p)) ->
        (* This pattern is essentially a let clause.  We first match the value
           of [pat] with some subterm of the goal, and then rewrite in each of
           the occurences of [id]. *)
        let (id,pat) = Bindlib.unbind p in
        let s = add_refs s in
        let p_s = Bindlib.subst p s in
        (* Try to match p[s/id] with a subterm of the goal. *)
        let p_refs = add_refs p_s in
        if not (make_pat g_term p_refs) then
            fatal_no_pos "No subterm of [%a] matches the pattern [%a]"
              pp g_term pp p_s;
        let p = p_refs in
        let pat_refs = add_refs pat in
        (* Here we have already asserted tat an instance of p[s/id] exists
           so we know that this will match something. The step is repeated
           in order to get the value of [id]. *)
        let sub =
          match match_pattern ([|id|], pat_refs) p with
          | Some(sub) -> sub
          | None      -> assert false
        in
        let id_val = sub.(0) in
        (* This part of the term-building is similar to the previous
           case, as we are essentially rebuilding a term, with some
           subterms that are replaced by new ones. *)
        let sigma =
          match match_pattern (vars, l) id_val with
          | Some(sigma) -> sigma
          | None        ->
              fatal_no_pos
                "The value of X, [%a], does not match the LHS, [%a]"
                pp id_val pp l
        in
        let (t,l,r) = Bindlib.msubst bound sigma in

        (* Now to do some term building. *)
        let p_x = bind_match l p in
        let p_r = Bindlib.subst p_x r in
        let pred_bind = bind_match p g_term in
        let new_term = Bindlib.subst pred_bind p_r in
        let (x, p_x) = Bindlib.unbind p_x in
        let pred_box = lift (Bindlib.subst pred_bind p_x) in
        let pred_bind = Bindlib.(unbox (bind_var x pred_box)) in
        (pred_bind, new_term, t, l, r)

    | Some(RW_InIdInTerm(p)      ) ->
        (* This is very similar to the [RW_IdInTerm] case. Instead of matching
           [id_val] with [l],  we try to match a subterm of [id_val] with [l],
           and then we rewrite this subterm. As a consequence,  we just change
           the way we construct a [pat_r]. *)
        let (id,p) = Bindlib.unbind p in
        let p_refs = add_refs p in
        let id_val =
          match find_subst g_term ([|id|],p_refs) with
          | Some(id_val) -> id_val
          | None         ->
              fatal_no_pos "The pattern [%a] does not match [%a]."
                pp p pp g_term
        in
        let id_val = id_val.(0) in
        let pat = Bindlib.unbox (Bindlib.bind_var id (lift p_refs)) in
        let pat_l = Bindlib.subst pat id_val in
        let sigma =
          match find_subst id_val (vars,l) with
          | Some(sigma) -> sigma
          | None        ->
              fatal_no_pos
                "The value of [%s], [%a], in [%a] does not match [%a]."
                (Bindlib.name_of id) pp id_val pp p pp l
        in
        let (t,l,r) = Bindlib.msubst bound sigma in

        (* Rewrite in id. *)
        let id_bind = bind_match l id_val in
        let id_val = Bindlib.subst id_bind r in
        let (x, id_x) = Bindlib.unbind id_bind in

        (* The new RHS of the pattern is obtained by rewriting in [id_val]. *)
        let r_val = Bindlib.subst pat id_val in
        let pred_bind_l = bind_match pat_l g_term in
        let new_term = Bindlib.subst pred_bind_l r_val in
        let l_x = Bindlib.subst pat id_x in
        let pred_box = lift (Bindlib.subst pred_bind_l l_x) in
        let pred_bind = Bindlib.unbox (Bindlib.bind_var x pred_box) in
        (pred_bind, new_term, t, l, r)
  in

  (* Construct the predicate (context). *)
  let pred =
    Abst(Appl(Symb(fst cfg.symb_T, snd cfg.symb_T), [|a|]), pred_bind)
  in

  (* Construct the new goal and its type. *)
  let goal_type = Appl(Symb(fst cfg.symb_P, snd cfg.symb_P), [|new_term|]) in
  let goal_term = Ctxt.make_meta g_ctxt goal_type in

  (* Build the final term produced by the tactic, and check its type. *)
  let eqind = Symb(fst cfg.symb_eqind, snd cfg.symb_eqind) in
  let term = add_args eqind [|a; l; r; t; pred; goal_term|] in

  (* Debugging data to the log. *)
  log_rewr "Rewriting with:";
  log_rewr "  goal           = [%a]" pp g_type;
  log_rewr "  equality proof = [%a]" pp t;
  log_rewr "  equality type  = [%a]" pp t_type;
  log_rewr "  equality LHS   = [%a]" pp l;
  log_rewr "  equality RHS   = [%a]" pp r;
  log_rewr "  pred           = [%a]" pp pred;
  log_rewr "  new goal       = [%a]" pp goal_type;
  log_rewr "  produced term  = [%a]" pp term;

  (* Return the proof-term. *)
  term

(** [reflexivity ps] applies the reflexivity of equality on the focused  goal.
    If successful, the corresponding proof term is returned. *)
let reflexivity : Proof.t -> term = fun ps ->
  (* Obtain the required symbols from the current signature. *)
  let cfg = Proof.(get_eq_config ps.proof_name ps.proof_builtins) in

  (* Get the type of the focused goal. *)
  let g_type =
    let g =
      try List.hd Proof.(ps.proof_goals) with Failure(_)  ->
        fatal_no_pos "No remaining goals..."
    in
    snd (Goal.get_type g)
  in

  (* Check that the type of [g] is of the form “P (Eq a t t)”. *)
  let (a, l, r)  = get_eq_data cfg (Eval.whnf g_type) in
  if not (Eval.eq_modulo l r) then fatal_no_pos "Cannot apply reflexivity.";

  (* Build the witness. *)
  add_args (Symb(fst cfg.symb_refl, snd cfg.symb_refl)) [|a; l|]

(** [symmetry ps] attempts to use symmetry of equality on the focused goal. If
    successful,  a new goal is generated,  and the corresponding proof term is
    returned. The proof of symmetry is built from the axioms of equality. *)
let symmetry : Proof.t -> term = fun ps ->
  (* Obtain the required symbols from the current signature. *)
  let cfg = Proof.(get_eq_config ps.proof_name ps.proof_builtins) in
  let symb_P = Symb(fst cfg.symb_P, snd cfg.symb_P) in
  let symb_T = Symb(fst cfg.symb_T, snd cfg.symb_T) in
  let symb_eq = Symb(fst cfg.symb_eq, snd cfg.symb_eq) in
  let symb_refl = Symb(fst cfg.symb_refl, snd cfg.symb_refl) in
  let symb_eqind = Symb(fst cfg.symb_eqind, snd cfg.symb_eqind) in

  (* Get the type of the focused goal. *)
  let (g_env, g_type) =
    let g =
      try List.hd Proof.(ps.proof_goals) with Failure(_)  ->
        fatal_no_pos "No remaining goals..."
    in
    Goal.get_type g
  in

  (* Check that the type of [g] is of the form “P (Eq a l r)”. *)
  let (a, l, r) = get_eq_data cfg g_type in

  (* NOTE The proofterm is “eqind a r l M (λx,eq a l x) (refl a l)”. *)

  (* We create a new metavariable (“M” in the above). *)
  let meta_type = Appl(symb_P, [|add_args symb_eq [|a; r; l|]|]) in
  let meta_term = Ctxt.make_meta (Ctxt.of_env g_env) meta_type in

  (* We build the predicate (“λx, eq a r x” in the above). *)
  let pred =
    let x = Bindlib.new_var mkfree "X" in
    let pred = add_args symb_eq [|a; l; Vari(x)|] in
    let pred = Bindlib.unbox (Bindlib.bind_var x (lift pred)) in
    Abst(Appl(symb_T, [|a|]), pred)
  in

  (* We build the proof term. *)
  let refl_a_l = add_args symb_refl [|a; l|] in
  let term = add_args symb_eqind [|a; r; l; meta_term; pred; refl_a_l|] in

  (* Debugging data to the log. *)
  log_rewr "Symmetry with:";
  log_rewr "  goal       = [%a]" pp g_type;
  log_rewr "  new goal   = [%a]" pp meta_type;
  log_rewr "  predicate  = [%a]" pp pred;
  log_rewr "  proof term = [%a]" pp term;

  (* Return the proof-term. *)
  term
