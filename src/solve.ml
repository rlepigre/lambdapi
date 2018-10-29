(** Type-checking and inference. *)

open Extra
open Timed
open Console
open Terms
open Basics
open Print
open Typing

(** Logging function for unification. *)
let log_solv = new_logger 's' "solv" "debugging information for unification"
let log_solv = log_solv.logger

(** Representation of a set of problems. *)
type problems =
  { to_solve  : conv_constrs
  (** List of unification problems that must be put in WHNF first. *)
  ; unsolved  : conv_constrs
  (** List of unsolved unification problems. *)
  ; recompute : bool
  (** Indicates whether unsolved problems should be rechecked. *) }

(** Empty problem. *)
let no_problems : problems =
  {to_solve  = []; unsolved = []; recompute = false}

(** Boolean saying whether user metavariables can be set or not. *)
let can_instantiate : bool ref = ref true

(** [instantiate m ts v] check whether [m] can be instantiated for solving the
    unification problem “m[ts] = v”. The returne boolean tells whether [m] was
    instantiated or not. *)
let instantiate : meta -> term array -> term -> bool = fun m ar v ->
  (!can_instantiate || internal m) && distinct_vars ar && not (occurs m v) &&
  let bv = Bindlib.bind_mvar (to_tvars ar) (lift v) in
  Bindlib.is_closed bv && (set_meta m (Bindlib.unbox bv); true)

(** [solve p] tries to solve the unification problems of [p]. *)
let rec solve : problems -> conv_constrs = fun p ->
  match p.to_solve with
  | [] when p.unsolved = [] -> []
  | [] when p.recompute     -> solve {no_problems with to_solve = p.unsolved}
  | []                      -> p.unsolved
  | (t,u)::to_solve         -> solve_aux t u {p with to_solve}

(** [solve_aux t1 t2 p] tries to solve the unificaton problem given by [p] and
    the constraint [(t1,t2)], starting with the latter. *)
and solve_aux : term -> term -> problems -> conv_constrs = fun t1 t2 p ->
  let (h1, ts1) = Eval.whnf_stk t1 [||] in
  let (h2, ts2) = Eval.whnf_stk t2 [||] in
  if !log_enabled then
    begin
      let t1 = Basics.add_args h1 ts1 in
      let t2 = Basics.add_args h2 ts2 in
      log_solv "solve_aux [%a] [%a]" pp t1 pp t2;
    end;
  let add_to_unsolved () =
    let t1 = Basics.add_args h1 ts1 in
    let t2 = Basics.add_args h2 ts2 in
    if Eval.eq_modulo t1 t2 then solve p
    else solve {p with unsolved = (t1,t2) :: p.unsolved}
  in
  let decompose () =
    solve {p with to_solve = List.add_array2 ts1 ts2 p.to_solve}
  in
  let error () =
    let t1 = Basics.add_args h1 ts1 in
    let t2 = Basics.add_args h2 ts2 in
    fatal_no_pos "[%a] and [%a] are not convertible." pp t1 pp t2
  in
  match (h1, h2) with
  (* Cases in which [ts1] and [ts2] must be empty due to typing / whnf. *)
  | (Type       , Type       )
  | (Kind       , Kind       ) -> solve p

  | (Prod(a1,b1), Prod(a2,b2))
  | (Abst(a1,b1), Abst(a2,b2)) ->
      let (_,b1,b2) = Bindlib.unbind2 b1 b2 in
      solve {p with to_solve = (a1,a2) :: (b1,b2) :: p.to_solve}

  | (Vari(x1)   , Vari(x2)   )
       when Bindlib.eq_vars x1 x2 && Array.length ts1 = Array.length ts2 ->
     decompose ()

  | (Symb(s1,_) , Symb(s2,_) ) ->
     if s1 == s2 then
       let same_length = Array.length ts1 = Array.length ts2 in
       match s1.sym_mode with
       | Const when same_length          -> decompose ()
       | Const                           -> error ()
       | Injec when same_length          -> decompose ()
       | Injec when !(s1.sym_rules) = [] -> error ()
       | Injec                           -> add_to_unsolved ()
       | Defin when !(s1.sym_rules) = [] -> add_to_unsolved ()
       | Defin when same_length          -> add_to_unsolved ()
       | Defin                           -> error ()
     else if !(s1.sym_rules) = [] && !(s2.sym_rules) = [] then error ()
     else add_to_unsolved ()

  | (Meta(m,ts) , _          )
        when Array.length ts1 = 0 && instantiate m ts t2 ->
      solve {p with recompute = true}
  | (_          , Meta(m,ts) )
        when Array.length ts2 = 0 && instantiate m ts t1 ->
      solve {p with recompute = true}

  | (Meta(_,_)  , _          )
  | (_          , Meta(_,_)  ) -> add_to_unsolved ()

  | (Symb(s,_)  , _          )
  | (_          , Symb(s,_)  ) ->
      if !(s.sym_rules) = [] then error () else add_to_unsolved ()

  | (_          , _          ) -> error ()

(** [solve flag problems] attempts to solve [problems],  after having sets the
    value of [can_instantiate] to [flag].  If there is no solution,  the value
    [None] is returned. Otherwise [Some(cs)] is returned,  where the list [cs]
    is a list of unsolved convertibility constraints. *)
let solve : bool -> problems -> conv_constrs option = fun b p ->
  can_instantiate := b;
  try Some (solve p) with Fatal(_,m) ->
    if !log_enabled then log_solv (red "solve: %s") m; None

(** [check ctx t a] tells whether [t] has type [a] in context [ctx]. *)
let check : Ctxt.t -> term -> term -> bool = fun ctx t a ->
  if !log_enabled then log_solv "check [%a] [%a]" pp t pp a;
  let to_solve = Typing.check ctx t a in
  match solve true {no_problems with to_solve} with
  | None     -> false
  | Some(cs) ->
      let fn (a,b) = log_solv (red "Cannot solve [%a] ~ [%a].") pp a pp b in
      if !log_enabled then List.iter fn cs; cs = []

(** [infer_constr ctx t] tries to infer a type [a],  together with unification
    constraints [cs], for the term [t] in context [ctx].  The function returns
    [Some(a,cs)] in case of success, and [None] otherwise. *)
let infer_constr : Ctxt.t -> term -> (conv_constrs*term) option = fun ctx t ->
  if !log_enabled then log_solv "infer_constr [%a]" pp t;
  let (a, to_solve) = Typing.infer ctx t in
  Option.map (fun cs -> (cs, a)) (solve true {no_problems with to_solve})

(** [infer ctx t] tries to infer a type [a] for [t] in the context [ctx].  The
    function returns [Some(a)] in case of success, and [None] otherwise. *)
let infer : Ctxt.t -> term -> term option = fun ctx t ->
  match infer_constr ctx t with
  | None       -> None
  | Some([],a) -> Some(a)
  | Some(cs,_) ->
      let fn (a,b) = log_solv (red "Cannot solve [%a] ~ [%a].") pp a pp b in
      if !log_enabled then List.iter fn cs; None

(** [sort_type ctx t] checks that the type of the term [t] in context [ctx] is
    a sort. If that is not the case, the exception [Fatal] is raised. *)
let sort_type : Ctxt.t -> term -> unit = fun ctx t ->
  if !log_enabled then log_solv "sort_type [%a]" pp t;
  match infer ctx t with
  | None    -> fatal_no_pos "Unable to infer a sort for [%a]." pp t
  | Some(a) ->
  match unfold a with
  | Type | Kind -> ()
  | a           -> fatal_no_pos "[%a] has type [%a] (not a sort)." pp t pp a
