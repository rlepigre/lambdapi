(** Evaluation and conversion. *)

open Extra
open Timed
open Console
open Terms
open Print

(** Logging function for evaluation. *)
let log_eval = new_logger 'r' "eval" "debugging information for evaluation"
let log_eval = log_eval.logger

(** Logging function for equality modulo rewriting. *)
let log_eqmd = new_logger 'e' "eqmd" "debugging information for equality"
let log_eqmd = log_eqmd.logger

(** Representation of a stack for the abstract machine used for evaluation. *)
type stack = term array

type stack_elt = stack * int * bool array option

(* NOTE the elements of the stack may be updated so that the computation of an
   argument may be shared when matching rewriting rules. *)

(** Evaluation step counter. *)
let steps : int Pervasives.ref = Pervasives.ref 0

(** [whnf t] computes a weak head normal form of the term [t]. *)
let rec whnf : term -> term = fun t ->
  if !log_enabled then log_eval "evaluating [%a]" pp t;
  let s = Pervasives.(!steps) in
  let t = unfold t in
  let (u, stk) = whnf_stk t [||] in
  if Pervasives.(!steps) <> s then Basics.add_args u stk else t

(** [whnf_stk t stk] computes the weak head normal form of  [t] applied to the
    argument list (or stack) [stk]. Note that the normalisation is done in the
    sense of [whnf]. *)
and whnf_stk : term -> stack -> term * stack = fun t stk ->
  let st = (unfold t, stk) in
  match st with
  (* Push argument to the stack. *)
  | (Appl(f,u), stk    ) ->
      whnf_stk f (Array.append u stk)
  (* Beta reduction. *)
  | (Abst(_,f), _      ) ->
      let len = Array.length stk in
      if len = 0 then st else
      let t = Bindlib.subst f stk.(0) in
      Pervasives.incr steps;
      whnf_stk t (Array.sub stk 1 (len - 1))
  (* Try to rewrite. *)
  | (Symb(s,_), stk    ) ->
      begin
        match Timed.(!(s.sym_def)) with
        | Some(t) -> Pervasives.incr steps; whnf_stk t stk
        | None    ->
        match find_rule s stk with
        | None        -> st
        | Some(t,stk) -> Pervasives.incr steps; whnf_stk t stk
      end
  (* In head normal form. *)
  | (_        , _      ) -> st

(** [find_rule s stk] attempts to find a reduction rule of [s], that may apply
    under the stack [stk]. If such a rule is found, the machine state produced
    by its application is returned. *)
and find_rule : sym -> stack -> (term * stack) option = fun s stk ->
  let stk_len = Array.length stk in
  let computed = Array.map (fun _ -> false) stk in
  let match_rule r =
    (* First check that we have enough arguments. *)
    if r.arity > stk_len then None else
    (* Substitute the left-hand side of [r] with pattern variables *)
    let env = Array.make (Bindlib.mbinder_arity r.rhs) TE_None in
    (* Match each argument of the lhs with the terms in the stack. *)
    let patt_size = Array.length r.lhs in
    let rec match_args i =
      if i >= patt_size then
        let t = Bindlib.msubst r.rhs env in
        let stk = Array.sub stk patt_size (stk_len - patt_size) in
        Some(t, stk)
      else if matching env r.lhs.(i) (stk, i, Some(computed)) then
        match_args (i+1)
      else
        None
    in
    match_args 0
  in
  List.map_find match_rule Timed.(!(s.sym_rules))

(** [matching ar p t] checks that term [t] matches pattern [p]. The values for
    pattern variables (using the [ITag] node) are stored in [ar], at the index
    they denote. In case several different values are found for a same pattern
    variable, equality modulo is computed to check compatibility. *)
and matching : term_env array -> term -> stack_elt -> bool = fun ar p elt ->
  let (stk, i, computed) = elt in
  let t = stk.(i) in
  if !log_enabled then log_eval "[%a] =~= [%a]" pp p pp (stk.(i));
  let res =
    (* First handle patterns that do not need the evaluated term. *)
    match p with
    | Patt(Some(i),_,[||]) when ar.(i) = TE_None ->
        let b = Bindlib.raw_mbinder [||] [||] 0 mkfree (fun _ -> t) in
        ar.(i) <- TE_Some(b); true
    | Patt(Some(i),_,e   ) when ar.(i) = TE_None ->
        let fn t = match t with Vari(x) -> x | _ -> assert false in
        let vars = Array.map fn e in
        let b = Bindlib.bind_mvar vars (lift t) in
        ar.(i) <- TE_Some(Bindlib.unbox b); Bindlib.is_closed b
    | Patt(None,_,[||]) -> true
    | Patt(None,_,e   ) ->
        let fn t = match t with Vari(x) -> x | _ -> assert false in
        let vars = Array.map fn e in
        Bindlib.is_closed (Bindlib.bind_mvar vars (lift t))
    | _                                 ->
    (* Other cases need the term to be evaluated. *)
    let t =
      match computed with
      | None                 -> stk.(i) <- whnf t; stk.(i)
      | Some(ar) when ar.(i) -> stk.(i)
      | Some(ar)             -> stk.(i) <- whnf t; ar.(i) <- true; stk.(i)
    in
    match (p, t) with
    | (Patt(Some(i),_,e), t            ) -> (* ar.(i) <> TE_None *)
        let b = match ar.(i) with TE_Some(b) -> b | _ -> assert false in
        eq_modulo (Bindlib.msubst b e) t
    | (Abst(_,t1)       , Abst(_,t2)   ) ->
        let (_,t1,t2) = Bindlib.unbind2 t1 t2 in
        matching ar t1 ([|t2|], 0, None)
    | (Appl(t1,u1)      , Appl(t2,u2)  ) ->
        if Array.length u1 <> Array.length u2 then false else
        matching ar t1 ([|t2|], 0, None) &&
        Array.for_all2 (fun u1 u2 -> matching ar u1 ([|u2|], 0, None)) u1 u2
    | (Vari(x1)         , Vari(x2)     ) -> Bindlib.eq_vars x1 x2
    | (Symb(s1,_)       , Symb(s2,_)   ) -> s1 == s2
    | (_                , _            ) -> false
  in
  if !log_enabled then log_eval (r_or_g res "[%a] =~= [%a]") pp p pp t;
  res

(** [eq_modulo a b] tests equality modulo rewriting between [a] and [b]. *)
and eq_modulo : term -> term -> bool = fun a b ->
  if !log_enabled then log_eqmd "[%a] == [%a]" pp a pp b;
  let rec eq_modulo l =
    match l with
    | []                   -> ()
    | (a,b)::l when a == b -> eq_modulo l
    | (a,b)::l             ->
    let (ha, argsa) =
      let (t, stk) = Basics.get_args a in
      whnf_stk t stk
    in
    let (hb, argsb) =
      let (t, stk) = Basics.get_args b in
      whnf_stk t stk
    in
    let continue l =
      if Array.length argsa <> Array.length argsb then raise Exit;
      eq_modulo (List.add_array2 argsa argsb l)
    in
    match (unfold ha, unfold hb) with
    | (a          , b          ) when a == b -> continue l
    | (Patt(_,_,_), _          )
    | (_          , Patt(_,_,_))
    | (TEnv(_,_)  , _          )
    | (_          , TEnv(_,_)  )
    | (Appl(_,_)  , _          )
    | (_          , Appl(_,_)  )
    | (Kind       , _          )
    | (_          , Kind       ) -> assert false
    | (Type       , Type       ) -> continue l
    | (Vari(x1)   , Vari(x2)   ) when Bindlib.eq_vars x1 x2 -> continue l
    | (Symb(s1,_) , Symb(s2,_) ) when s1 == s2 -> continue l
    | (Prod(a1,b1), Prod(a2,b2))
    | (Abst(a1,b1), Abst(a2,b2)) -> continue [(a1,a2); (unbind2 b1 b2)]
    | (Meta(m1,a1), Meta(m2,a2)) when m1 == m2 ->
        continue (List.add_array2 a1 a2 l)
    | (_          , _          ) -> raise Exit
  in
  let res = try eq_modulo [(a,b)]; true with Exit -> false in
  if !log_enabled then log_eqmd (r_or_g res "%a == %a") pp a pp b; res

let whnf : term -> term = fun t ->
  let t = unfold t in
  Pervasives.(steps := 0);
  let u = whnf t in
  if Pervasives.(!steps = 0) then t else u

(** [snf t] computes the strong normal form of the term [t]. *)
let rec snf : term -> term = fun t ->
  let h = whnf t in
  match h with
  | Vari(_)     -> h
  | Type        -> h
  | Kind        -> h
  | Symb(_)     -> h
  | Prod(a,b)   ->
      let (x,b) = Bindlib.unbind b in
      let b = snf b in
      let b = Bindlib.unbox (Bindlib.bind_var x (lift b)) in
      Prod(snf a, b)
  | Abst(a,b)   ->
      let (x,b) = Bindlib.unbind b in
      let b = snf b in
      let b = Bindlib.unbox (Bindlib.bind_var x (lift b)) in
      Abst(snf a, b)
  | Appl(t,a)   -> Appl(snf t, Array.map snf a)
  | Meta(m,ts)  -> Meta(m, Array.map snf ts)
  | Patt(_,_,_) -> assert false
  | TEnv(_,_)   -> assert false
  | Wild        -> assert false
  | TRef(_)     -> assert false

(** [hnf t] computes the head normal form of the term [t]. *)
let rec hnf : term -> term = fun t ->
  match whnf t with
  | Appl(t,a) -> Appl(hnf t, Array.map hnf a)
  | t         -> t

(** Type representing the different evaluation strategies. *)
type strategy = WHNF | HNF | SNF | NONE

(** Configuration for evaluation. *)
type config =
  { strategy : strategy   (** Evaluation strategy.          *)
  ; steps    : int option (** Max number of steps if given. *) }

(** [eval cfg t] evaluates the term [t] according to configuration [cfg]. *)
let eval : config -> term -> term = fun c t ->
  match (c.strategy, c.steps) with
  | (_   , Some(0))
  | (NONE, _      ) -> t
  | (WHNF, None   ) -> whnf t
  | (SNF , None   ) -> snf t
  | (HNF , None   ) -> hnf t
  (* TODO implement the rest. *)
  | (_   , Some(_)) -> wrn None "Number of steps not supported."; t
