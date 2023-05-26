Require Export Similar.
Import ListNotations.
Require Import Lia.

(** * A regexp has a finite number of canonical derivatives *)

(** See file Similar.v for the definition of the canonical form *)

(** For proving that, we explicitely generate a list of regexps
    containing (at least) all the derivatives. This list is an
    over-approximation, we'll see later how to be exact in Explore.v *)

Module FiniteDerivs (Letter : FiniteOrderedType).
Include RegSim(Letter).

(** Two helper functions *)

Definition mixcat r l1 l2 :=
 let f '(s,l2b) := canon (Or (Cat s r) (OR.mk l2b)) in
 List.map f (product l1 (sublists l2)).

Definition mixstar r l :=
 let f l := canon (OR.mk (List.map (fun s => Cat s (Star r)) l)) in
 List.map f (sublists l).

Definition mkOr '(r1,r2) := sOr r1 r2.
Definition mkAnd '(r1,r2) := sAnd r1 r2.

(** First, an over-approximation : all canonical derivatives of [r]
    will be in [over_derivs r], but this list may also contain some
    non-derivatives. *)

Fixpoint over_derivs r := match r with
  | Void => [Void]
  | Epsilon => [Void; Epsilon]
  | Letter a => [Void; Epsilon; Letter a]
  | Cat r1 r2 => mixcat r2 (over_derivs r1) (over_derivs r2)
  | Star r' => canon r :: mixstar r' (over_derivs r')
  | Or r1 r2 => map mkOr (product (over_derivs r1) (over_derivs r2))
  | And r1 r2 => map mkAnd (product (over_derivs r1) (over_derivs r2))
  | Not r => map Not (over_derivs r)
  end.

(** The size of this over-approximation *)

Fixpoint derivs_bound r :=
  match r with
  | Void => 1
  | Epsilon => 2
  | Letter _ => 3
  | Cat r1 r2 => (derivs_bound r1) * 2^(derivs_bound r2)
  | Star r => S (2^(derivs_bound r))
  | Or r1 r2 => (derivs_bound r1) * (derivs_bound r2)
  | And r1 r2 => (derivs_bound r1) * (derivs_bound r2)
  | Not r => derivs_bound r
  end.

Lemma derivs_bound_ok r :
 length (over_derivs r) = derivs_bound r.
Proof.
  induction r; simpl in *; firstorder.
  - unfold mixcat. rewrite map_length, product_length, sublists_length. firstorder.
  - unfold mixstar. f_equal. rewrite map_length, sublists_length. firstorder.
  - rewrite map_length, product_length. firstorder.
  - rewrite map_length, product_length. firstorder.
  - rewrite map_length. firstorder.
Qed.

(** The predicate we're trying to establish on [over_derivs] *)

Definition AllDerivsIn r l := forall w, In (canon (r//w)) l.

(** Results about [mixcat] *)

Lemma mixcat_in r r2 l1 l2 :
 In r (mixcat r2 l1 l2) <->
 exists s l2b,
   canon (Or (Cat s r2) (OR.mk l2b)) = r /\ In s l1 /\ Incl l2b l2.
Proof.
  unfold mixcat. firstorder.
  - apply in_map_iff in H. firstorder. destruct x. exists r0, l. apply product_ok in H0. destruct H0. apply sublists_spec in H1. intuition.
  - apply in_map_iff. exists (x,x0). intuition. apply product_ok. intuition. apply sublists_spec. assumption.
Qed.

Lemma mixcat_stable_1 r r2 l1 l2 : Canonical r ->
 In r l1 ->
 In (sCat r (canon r2)) (mixcat r2 l1 l2).
Proof.
  intros. apply mixcat_in. exists r, []. simpl. rewrite sOr_void_r. intuition. f_equal. apply can_canon_id. assumption.
Qed.

Lemma mixcat_stable_2 r r' r2 l1 l2 : Canonical r' ->
 In r (mixcat r2 l1 l2) ->
 In r' l2 ->
 In (sOr r r') (mixcat r2 l1 l2).
Proof.
Admitted.

Lemma mixcat_gen r1 r2 l1 l2 :
 AllDerivsIn r1 l1 ->
 AllDerivsIn r2 l2 ->
 forall w',
 AllDerivsIn (Cat (r1 // w') r2) (mixcat r2 l1 l2).
Proof.
Admitted.

Lemma mixcat_ok r1 r2 l1 l2 :
 AllDerivsIn r1 l1 ->
 AllDerivsIn r2 l2 ->
 AllDerivsIn (Cat r1 r2) (mixcat r2 l1 l2).
Proof.
  intros. apply mixcat_gen with (r1:=r1) (r2:=r2) (w':=[]) (l1:=l1) (l2:=l2) in H.
  - simpl in H. assumption.
  - assumption.
Qed.

(** Results about [mixstar] *)

Lemma mixstar_in r' r l :
 In r' (mixstar r l) <->
 exists l',
   canon (OR.mk (map (fun s => Cat s (Star r)) l')) = r' /\ Incl l' l.
Proof.
  unfold mixstar. firstorder.
  - apply in_map_iff in H. destruct H. exists x. intuition. apply  sublists_spec. assumption.
  - apply in_map_iff. exists x. intuition. apply sublists_spec. assumption.
Qed.

Lemma mixstar_stable_1 r l r' :
  In (canon r') l ->
  In (canon (Cat r' (Star r))) (mixstar r l).
Proof.
  intros. apply mixstar_in. exists [canon r']. simpl. rewrite canon_canon. intuition. apply Incl_singleton. assumption.
Qed.

Lemma mixstar_stable_2 r r1 r2 l :
  In r1 (mixstar r l) ->
  In r2 (mixstar r l) ->
  In (sOr r1 r2) (mixstar r l).
Proof.
Admitted.

Lemma mixstar_gen r l :
 AllDerivsIn r l ->
 forall w',
 AllDerivsIn (Cat (r // w') (Star r)) (mixstar r l).
Proof.
Admitted.

Lemma mixstar_ok r l :
 AllDerivsIn r l ->
 AllDerivsIn (Star r) (canon (Star r) :: mixstar r l).
Proof.
Admitted.

(** Main theorem : our over approximation indeed contains
    all canonical derivatives *)

Lemma finite_derivatives r : AllDerivsIn r (over_derivs r).
Proof.
Admitted.

(** Same result, expressed with [sim] instead of [canon] *)

Definition AllDerivsInMod (R:re->re->Prop) r l :=
  forall w, InModulo R (r//w) l.

Lemma finite_derivatives' r :
  AllDerivsInMod sim r (over_derivs r).
Proof.
Admitted.

(** Finiteness statement based on [equiv] (full regexp equivalence
    based on the languages) instead of [sim] *)

Lemma finite_derivatives_equiv r :
  AllDerivsInMod equiv r (over_derivs r).
Proof.
Admitted.

End FiniteDerivs.
