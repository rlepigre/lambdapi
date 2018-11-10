(** Basic operations on terms. *)

open Extra
open Timed
open Terms

(** [to_tvars ar] extracts and array of {!type:tvar} from an array of terms of
    the form {!const:Vari(x)}. The function fails if any elements of [ar] does
    not correspond to a free variable. *)
let to_tvars : term array -> tvar array =
  Array.map (function Vari(x) -> x | _ -> assert false)

(** [count_products a] returns the number of consecutive products at the  head
    of the term [a]. *)
let rec count_products : term -> int = fun t ->
  match unfold t with
  | Prod(_,b) -> 1 + count_products (snd (Bindlib.unbind b))
  | _         -> 0

(** [get_args t] decomposes the {!type:term} [t] into a pair [(h,args)], where
    [h] and [args] are respectively the head of [t] and the array of arguments
    applied to [h] in [t]. The returned [h] cannot be an {!constr:Appl}. *)
let get_args : term -> term * term array = fun t ->
  match unfold t with
  | Appl(t,args) -> (t, args)
  | t            -> (t, [||])

(** [add_args t args] builds the application of [t] to the elements of [args].
    When [args] is empty, the returned value is (physically) equal to [t]. *)
let add_args : term -> term array -> term = fun t args ->
  if Array.length args = 0 then t else
  match unfold t with
  | Appl(t,a) -> Appl(t, Array.append a args)
  | t         -> Appl(t, args)

(** [eq t u] tests the equality of [t] and [u] modulo α-equivalence. Note that
    the behavious of the function is unspecified when [t] or [u] contain terms
    of the form {!const:Patt(i,s,e)} or {!const:TEnv(te,e)} (in the case where
    [te] is not of the form {!const:TE_Some(b)}). *)
let eq : term -> term -> bool = fun a b -> a == b ||
  let exception Not_equal in
  let rec eq l =
    match l with
    | []       -> ()
    | (a,b)::l ->
    match (unfold a, unfold b) with
    | (a          , b          ) when a == b -> eq l
    | (Vari(x1)   , Vari(x2)   ) when Bindlib.eq_vars x1 x2 -> eq l
    | (Type       , Type       )
    | (Kind       , Kind       ) -> eq l
    | (Symb(s1,_) , Symb(s2,_) ) when s1 == s2 -> eq l
    | (Prod(a1,b1), Prod(a2,b2))
    | (Abst(a1,b1), Abst(a2,b2)) -> eq ((a1,a2)::(unbind2 b1 b2)::l)
    | (Appl(t1,a1), Appl(t2,a2)) ->
        if a1 == a2 then eq ((t1,t2)::l)
        else if Array.length a1 = Array.length a2 then
          eq ((t1,t2) :: List.add_array2 a1 a2 l)
        else raise Not_equal
    | (Meta(m1,e1), Meta(m2,e2)) when m1 == m2 ->
        eq (if e1 == e2 then l else List.add_array2 e1 e2 l)
    | (Wild       , _          )
    | (_          , Wild       ) -> eq l
    | (TRef(r)    , b          ) -> r := Some(b); eq l
    | (a          , TRef(r)    ) -> r := Some(a); eq l
    | (Patt(_,_,_), _          )
    | (_          , Patt(_,_,_))
    | (TEnv(_,_)  , _          )
    | (_          , TEnv(_,_)  ) -> assert false
    | (_          , _          ) -> raise Not_equal
  in
  try eq [(a,b)]; true with Not_equal -> false

(** [eq_vari t u] checks that [t] and [u] are both variables, and the they are
    pariwise equal. *)
let eq_vari : term -> term -> bool = fun t u ->
  match (unfold t, unfold u) with
  | (Vari(x), Vari(y)) -> Bindlib.eq_vars x y
  | (_      , _      ) -> false

(** [is_symb s t] tests whether [t] is of the form [Symb(s)]. *)
let is_symb : sym -> term -> bool = fun s t ->
  match unfold t with
  | Symb(r,_) -> r == s
  | _         -> false

(** [iter f t] applies the function [f] to every node of the term [t]. At each
    call, the function is given the list of the free variables in the term, in
    the reverse order they were given. Free variables that were already in the
    term before the call are not included in the list. *)
let iter : (tvar list -> term -> unit) -> term -> unit = fun action t ->
  let rec iter xs t =
    let t = unfold t in
    action xs t;
    match t with
    | Wild
    | TRef(_)
    | Vari(_)
    | Type
    | Kind
    | Symb(_)    -> ()
    | Patt(_,_,ts)
    | TEnv(_,ts)
    | Meta(_,ts) -> Array.iter (iter xs) ts
    | Prod(a,b)
    | Abst(a,b)  -> let (x,b) = Bindlib.unbind b in iter xs a; iter (x::xs) b
    | Appl(t,a)  -> iter xs t; Array.iter (iter xs) a
  in
  iter [] (cleanup t)

(** [iter_meta f t] applies the function [f] to every metavariable in the term
    [t]. As for {!val:eq},  the behaviour of this function is unspecified when
    [t] uses the {!const:Patt} or {!const:TEnv} constructor.  This function is
    implemented using [iter] as it is critical for performances. *)
let rec iter_meta : (meta -> unit) -> term -> unit = fun f t ->
  match unfold t with
  | Patt(_,_,_)
  | TEnv(_,_)
  | Wild
  | TRef(_)    -> assert false
  | Vari(_)
  | Type
  | Kind
  | Symb(_)    -> ()
  | Prod(a,b)
  | Abst(a,b)  -> iter_meta f a; iter_meta f (Bindlib.subst b Kind)
  | Appl(t,a)  -> iter_meta f t; Array.iter (iter_meta f) a
  | Meta(v,ts) -> f v; iter_meta f !(v.meta_type); Array.iter (iter_meta f) ts

(** [occurs m t] tests whether the metavariable [m] occurs in the term [t]. As
    for {!val:eq}, the behaviour of this function is unspecified when [t] uses
    the {!const:Patt} or {!const:TEnv} constructor. *)
let occurs : meta -> term -> bool = fun m t ->
  let fn p = if m == p then raise Exit in
  try iter_meta fn t; false with Exit -> true

(** [get_metas t] returns the list of all the metavariables in [t]. *)
let get_metas : term -> meta list = fun t ->
  let l = Pervasives.ref [] in
  iter_meta (fun m -> Pervasives.(l := m :: !l)) t;
  List.sort_uniq (fun m1 m2 -> m1.meta_key - m2.meta_key) Pervasives.(!l)

(** [distinct_vars a] checks that [a] is made of distinct variables. *)
let distinct_vars : term array -> bool = fun ar ->
  let rec distinct_vars vars i =
    if i < 0 then true else
    match unfold ar.(i) with
    | Vari(x) when List.exists (Bindlib.eq_vars x) vars -> false
    | Vari(x) -> distinct_vars (x::vars) (i-1)
    | _       -> false
  in
  distinct_vars [] (Array.length ar - 1)

(** {2 Conversion of a rule into a "pair" of terms} *)

(** [terms_of_rule r] converts the RHS (right hand side) of the rewriting rule
    [r] into a term.  The bound higher-order variables of the original RHS are
    substituted using [Patt] constructors.  They are thus represented as their
    LHS counterparts. This is a more convenient way of representing terms when
    analysing confluence or termination. *)
let term_of_rhs : rule -> term = fun r ->
  let fn i (name, arity) =
    let make_var i = Bindlib.new_var mkfree (Printf.sprintf "x%i" i) in
    let vars = Array.init arity make_var in
    let p = _Patt (Some(i)) name (Array.map Bindlib.box_var vars) in
    TE_Some(Bindlib.unbox (Bindlib.bind_mvar vars p))
  in
  Bindlib.msubst r.rhs (Array.mapi fn r.ctxt)
