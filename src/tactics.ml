(** Toplevel commands. *)

open Extra
open Timed
open Console
open Terms
open Print
open Pos
open Syntax
open Scope

(** Logging function for tactics. *)
let log_tact = new_logger 'i' "tact" "debugging information for tactics"
let log_tact = log_tact.logger

(** [handle_tactic ps tac] tries to apply the tactic [tac] (in the proof state
    [ps]), and returns the new proof state.  This function fails gracefully in
    case of error. *)
let handle_tactic : sig_state -> Proof.t -> p_tactic -> Proof.t =
    fun ss ps tac ->
  (* First handle the tactics that are independant from the goal. *)
  match tac.elt with
  | P_tac_print         ->
      (* Just print the current proof state. *)
      Console.out 1 "%a" Proof.pp ps; ps
  | P_tac_proofterm     ->
      (* Just print the current proof term. *)
      let t = Eval.snf (Meta(Proof.(ps.proof_term), [||])) in
      let name = Proof.(ps.proof_name).elt in
      Console.out 1 "Proof term for [%s]: [%a]\n" name Print.pp t; ps
  | P_tac_focus(i)      ->
      (* Put the [i]-th goal in focus (if possible). *)
      let rec swap i acc gs =
        match (i, gs) with
        | (0, g::gs) -> g :: List.rev_append acc gs
        | (i, g::gs) -> swap (i-1) (g::acc) gs
        | (_, _    ) -> fatal tac.pos "Invalid goal index."
      in
      Proof.{ps with proof_goals = swap i [] ps.proof_goals}
  | _                   ->
  (* Other tactics need to act on the goal / goals. *)
  let (g, gs) =
    match Proof.(ps.proof_goals) with
    | []    -> fatal tac.pos "There is nothing left to prove.";
    | g::gs -> (g, gs)
  in
  let handle_refine : term -> Proof.t = fun t ->
    (* Obtaining the goals environment and type. *)
    let (env, a) = Proof.Goal.get_type g in
    (* Check if the goal metavariable appears in [t]. *)
    let m = Proof.Goal.get_meta g in
    log_tact "refining [%a] with term [%a]" pp_meta m pp t;
    if Basics.occurs m t then fatal tac.pos "Circular refinement.";
    (* Check that [t] is well-typed. *)
    let ctx = Ctxt.of_env env in
    log_tact "proving [%a ⊢ %a : %a]" Ctxt.pp ctx pp t pp a;
    if not (Solve.check ctx t a) then fatal tac.pos "Ill-typed refinement.";
    (* Instantiation. *)
    let vs = Array.of_list (List.map (fun (_,(x,_)) -> x) env) in
    m.meta_value := Some(Bindlib.unbox (Bindlib.bind_mvar vs (lift t)));
    (* New subgoals and focus. *)
    let metas = Basics.get_metas t in
    let new_goals = List.rev_map Proof.Goal.of_meta_decomposed metas in
    Proof.({ps with proof_goals = new_goals @ gs})
  in
  match tac.elt with
  | P_tac_print
  | P_tac_proofterm
  | P_tac_focus(_)      -> assert false (* Handled above. *)
  | P_tac_refine(t)     ->
      (* Scoping the term in the goal's environment. *)
      let env = fst (Proof.Goal.get_type g) in
      let t = fst (Scope.scope_term StrMap.empty ss env t) in
      (* Refine using the given term. *)
      handle_refine t
  | P_tac_intro(xs)     ->
      (* Scoping a sequence of abstraction in the goal's environment. *)
      let env = fst (Proof.Goal.get_type g) in
      let xs = List.map (fun x -> (x, None)) xs in
      let t = Pos.none (P_Abst(xs, Pos.none P_Wild)) in
      let t = fst (Scope.scope_term StrMap.empty ss env t) in
      (* Refine using the built term. *)
      handle_refine t
  | P_tac_apply(t)      ->
      (* Scoping the term in the goal's environment. *)
      let env = fst (Proof.Goal.get_type g) in
      let t0 = fst (Scope.scope_term StrMap.empty ss env t) in
      (* Infer the type of [t0] and count the number of products. *)
      (* NOTE there is room for improvement here. *)
      let nb =
        match Solve.infer (Ctxt.of_env env) t0 with
        | Some(a) -> Basics.count_products a
        | None    -> fatal t.pos "Cannot infer the type of [%a]." Print.pp t0
      in
      (* Refine using [t] applied to [nb] wildcards (metavariables). *)
      (* NOTE it is scoping that handles wildcards as metavariables. *)
      let rec add_wilds t n =
        match n with
        | 0 -> fst (Scope.scope_term StrMap.empty ss env t)
        | _ -> add_wilds (Pos.none (P_Appl(t, Pos.none P_Wild))) (n-1)
      in
      handle_refine (add_wilds t nb)
  | P_tac_simpl         ->
      Proof.({ps with proof_goals = Proof.Goal.simpl g :: gs})
  | P_tac_rewrite(po,t) ->
      (* Scoping the term in the goal's environment. *)
      let env = fst (Proof.Goal.get_type g) in
      let t = fst (Scope.scope_term StrMap.empty ss env t) in
      (* Scoping the rewrite pattern if given. *)
      let po = Option.map (Scope.scope_rw_patt ss env) po in
      (* Calling rewriting, and refining. *)
      handle_refine (Rewrite.rewrite ps po t)
  | P_tac_refl          ->
      handle_refine (Rewrite.reflexivity ps)
  | P_tac_sym           ->
      handle_refine (Rewrite.symmetry ps)
