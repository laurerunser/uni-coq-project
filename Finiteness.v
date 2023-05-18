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
  unfold mixcat. split; intros.
  - apply in_map_iff in H. destruct H, x, H. exists r0, l. apply product_ok in H0. destruct H0. apply sublists_spec in H1. intuition.
  - destruct H, H, H, H0. apply in_map_iff. exists (x,x0). intuition. apply product_ok. intuition. apply sublists_spec. assumption.
Qed.


Lemma mixcat_stable_1 r r2 l1 l2 : Canonical r ->
 In r l1 ->
 In (sCat r (canon r2)) (mixcat r2 l1 l2).
Proof.
  induction r; simpl; intros; apply mixcat_in.
  - exists Void, []. intuition.
  - exists Epsilon, []. simpl. intuition. unfold sOr, sCat. case RE.eqb_spec; intuition.
  - exists (Letter t), []. simpl. intuition. unfold sOr, sCat. case RE.eqb_spec; intuition.
  - exists (Cat r1 r3), []. simpl. intuition. unfold sOr. simpl. case RE.eqb_spec.
    + intro. rewrite <- e. f_equiv. apply can_canon_id in H4, H6. rewrite H4, H6. unfold sCat. case RE.eqb_spec; intuition. simpl. case RE.eqb_spec; intuition. case RE.eqb_spec. intro; intuition. case RE.eqb_spec. intro; intuition. intro; intuition.
    + intro. f_equiv. apply can_canon_id in H4, H6. unfold sCat. case RE.eqb_spec. intro. intuition congruence. intro. simpl. case RE.eqb_spec. intro. intuition congruence. intro. case RE.eqb_spec. intuition congruence. intro. case RE.eqb_spec. intuition congruence. intro. intuition congruence.
  - exists (Star r), []. simpl. intuition. unfold sOr. simpl. case RE.eqb_spec.
    + intro. rewrite <- e. f_equiv. unfold sStar. apply can_canon_id in H3. case RE.eqb_spec. intro. intuition congruence. intro. simpl. case RE.eqb_spec. intuition congruence. intuition congruence.
    + intro. f_equiv. apply can_canon_id in H3. unfold sStar. case RE.eqb_spec. intuition congruence. intro. simpl. case RE.eqb_spec. intuition congruence. intuition congruence.
  - exists (Or r1 r3), []. simpl. intuition. rewrite sOr_void_r. f_equiv. rewrite <- canon_or with(r:=r1)(s:=r3). apply can_canon_id. simpl. intuition.
  - exists (And r1 r3), []. simpl. intuition. apply can_canon_id in H2, H4. rewrite sOr_void_r. f_equiv. unfold sAnd. case RE.eqb_spec.  intuition congruence. intro. simpl. case RE.eqb_spec. intuition congruence. intuition congruence.
  - exists (Not r), []. simpl. intuition. rewrite sOr_void_r. f_equiv. apply can_canon_id in H. intuition congruence.
Qed.

Lemma mixcat_stable_2 r r' r2 l1 l2 : Canonical r' ->
 In r (mixcat r2 l1 l2) ->
 In r' l2 ->
 In (sOr r r') (mixcat r2 l1 l2).
Proof.
  induction r; simpl; intros; apply mixcat_in; apply mixcat_in in H0; destruct H0, H0.
  - exists x, [r']. intuition. unfold sOr. case RE.eqb_spec.
    + apply can_canon_id in H. intro. simpl in *. apply sOr_void in H2.  destruct H2.
      * rewrite H2. rewrite sOr_void_l. assumption.
      * apply sCat_can; apply canon_can.
      * apply canon_can.
    + intuition.
    + apply Incl_singleton. assumption.
  - eexists. eexists. intuition. revert H2. simpl. unfold sOr. case RE.eqb_spec.
    + unfold sCat. case RE.eqb_spec.
      * simpl. intro. intro. intro. case RE.eqb_spec.
        -- case RE.eqb_spec.
          ++ intro. case RE.eqb_spec.
            ** intro. case RE.eqb_spec.
              --- intro. case RE.eqb_spec; rewrite e1 in e3; discriminate.
              --- intro. case RE.eqb_spec.
                +++ intro. case RE.eqb_spec; rewrite e2 in e3; discriminate.
                +++ intro. case RE.eqb_spec.
                  *** intro. simpl. intro. destruct e4, e0. induction x0.
                    ---- simpl in H2. discriminate.
                    ---- apply IHx0.
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
Admitted.

(** Results about [mixstar] *)

Lemma mixstar_in r' r l :
 In r' (mixstar r l) <->
 exists l',
   canon (OR.mk (map (fun s => Cat s (Star r)) l')) = r' /\ Incl l' l.
Proof.
Admitted.

Lemma mixstar_stable_1 r l r' :
  In (canon r') l ->
  In (canon (Cat r' (Star r))) (mixstar r l).
Proof.
Admitted.

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
