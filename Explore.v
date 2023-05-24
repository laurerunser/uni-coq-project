Require Export Finiteness.
Import ListNotations.
Require Import Lia.

(** * Generating the exact set of derivatives of a regexp *)

(** In Finiteness.v, we've built an over-approximation of these
    derivatives. Now, let's be exact. *)

Module RegExplore (Letter : FiniteOrderedType).
Include FiniteDerivs(Letter).

Implicit Type a : Letter.t.

(** From a given regexp r, the set of all [canon (r/a)] for all
    possible letters a. *)

Definition allderiv1 r :=
  list2set (List.map (fun a => canon (r/a)) Letter.enumeration).

Lemma allderiv1_in r x :
  REs.In x (allderiv1 r) <-> exists a, x = canon (r/a).
Proof.
  split; intros.
  - apply list2set_in, in_map_iff in H. destruct H. exists x0. intuition.
  - apply list2set_in, in_map_iff. destruct H. exists x0. intuition. apply Letter.enumeration_spec.
Qed.

(** We proceed via a graph exploration. Nodes are regexps, edges are
    letters, there is an edge [a] from [r] to [s] if [canon (r/a) = s].
    We start with our initial regexp, and we stop when nothing new could
    be reached. Note: this graph is actually the automata recognizing
    our regexp, but we do not build it explicitely here.

    - [n] is the depth of our search, to convince Coq we'll stop someday
    - [explored] is a set of derivatives we've finished visiting :
      all their derivatives by a letter are in [explored] or [seen]
    - [seen] is a set of derivatives we still have to handle :
      we haven't checked yet whether their own derivatives are new or not.
*)

Fixpoint explore n explored seen :=
  match n with
  | 0 => REs.empty (* abort *)
  | S n =>
    let seen' := REs.diff seen explored in
    match REs.choose seen' with
    | None => explored (* finished *)
    | Some x =>
      explore n (REs.add x explored)
                (REs.union (allderiv1 x) (REs.remove x seen'))
    end
  end.

Definition try_exact_derivs r n :=
  explore n REs.empty (REs.singleton (canon r)).

(** Normally, we launch explore with [derivs_bound], to be sure to
    converges. But this bound could be horribly slow to compute... *)

Definition slow_exact_derivs r :=
  try_exact_derivs r (S (derivs_bound r)).

(** Pragmatic approach : 100 loops are usually enough.
    If not, we restart with the full bound and wait... *)

Definition exact_derivs r :=
  let s := try_exact_derivs r 100 in
  if REs.is_empty s then slow_exact_derivs r (* 100 wasn't enough *)
  else s.

Definition Deriv r r' := exists w, r' = canon (r//w).
Definition DerivSet r set := forall r', REs.In r' set -> Deriv r r'.
Definition ExactDerivSet r set := forall r', REs.In r' set <-> Deriv r r'.
Definition Hereditary set1 set2 :=
  forall r a, REs.In r set1 -> REs.In (canon (r/a)) set2.

Global Instance : Proper (eq ==> REs.Equal ==> iff) DerivSet.
Proof.
 intros r r' <- set set' E. unfold DerivSet. now setoid_rewrite E.
Qed.

Global Instance : Proper (REs.Equal ==> REs.Equal ==> iff) Hereditary.
Proof.
 intros set1 set1' E1 set2 set2' E2. unfold Hereditary.
 setoid_rewrite E1; setoid_rewrite E2; easy.
Qed.

Lemma a_set_equation x explored seen :
  REs.Equal
    (REs.union (REs.add x explored)
               (REs.union (allderiv1 x)
                          (REs.remove x (REs.diff seen explored))))
    (REs.union (allderiv1 x) (REs.add x (REs.union explored seen))).
Proof.
 intro y. generalize (allderiv1_in x y). REsdec.
Qed.

Definition PreCondition r explored seen :=
  let all := REs.union explored seen in
  REs.In (canon r) all /\
  DerivSet r all /\
  Hereditary explored all.

Lemma PreCondition_init r :
  PreCondition r REs.empty (REs.singleton (canon r)).
Proof.
  unfold PreCondition, DerivSet, Hereditary. firstorder.
  - REsdec.
  - revert H. REsP.FM.set_iff. exists []. intuition.
  - revert H. REsP.FM.set_iff. auto.
Qed.

Lemma PreCondition_next r explored seen x :
  let seen' := REs.diff seen explored in
  REs.In x seen' ->
  PreCondition r explored seen ->
  PreCondition r (REs.add x explored)
                 (REs.union (allderiv1 x) (REs.remove x seen')).
Proof.
  unfold PreCondition, DerivSet, Deriv, Hereditary. intuition.
  - rewrite a_set_equation. REsdec.
  - revert H2. REsP.FM.set_iff. rewrite allderiv1_in. intro. destruct H2, H2.
    2,4: apply H0; REsdec.
    + apply H0. rewrite <- H2. revert H. REsP.FM.set_iff. intuition.
    + destruct H2, H0 with x.
      * revert H. REsP.FM.set_iff. intuition.
      * subst. exists (x1++[x0]). rewrite canon_deriv1, deriv_app. reflexivity.
  - apply REs.add_spec in H2. intuition.
    + subst. REsP.FM.set_iff. right. left. rewrite allderiv1_in. exists a. reflexivity.
    + apply a_set_equation. REsP.FM.set_iff. right. right. apply REsP.FM.union_1. intuition.
Qed.

(** Here it could help to proceed by induction over the [rev] of some word.
    Feel free to add any intermediate lemmas that might help you. *)

Lemma hereditary_all_derivs r s set :
  REs.In (canon r) set ->
  Hereditary set set ->
  Deriv r s -> REs.In s set.
Proof.
  unfold Hereditary, Deriv. firstorder. revert H H1. revert r. induction x; intuition; subst.
  - assumption.
  - eapply H0 in H. rewrite canon_deriv1_canon in H. apply IHx in H; intuition.
Qed.

Lemma explore_partial_spec r n explored seen :
 PreCondition r explored seen ->
 let out := explore n explored seen in
 REs.Empty out \/ ExactDerivSet r out.
Proof.
  unfold ExactDerivSet, DerivSet, Hereditary. revert explored seen. induction n.
  - intuition.
  - intros. simpl. case REs.choose eqn:Hcase.
    + eapply PreCondition_next in H.
      * apply IHn in H. eassumption.
      * apply REs.choose_spec1. assumption.
    + assert(H1: REs.Empty (REs.diff seen explored) -> REs.Equal (REs.union explored seen) explored). { REsdec. } apply REs.choose_spec2, H1 in Hcase. unfold PreCondition in H. rewrite Hcase in H. right. intuition. unfold DerivSet in H. eapply hereditary_all_derivs; eassumption.
Qed.

Lemma explore_converges_n0_aux r explored seen : PreCondition r explored seen  -> incl (REs.elements (REs.union explored seen)) (over_derivs r).
Proof.
  intro. unfold incl. intros. apply REs_elements_spec, H in H0. destruct H0. subst. revert H. revert explored seen. induction r; simpl; intros.
  - rewrite deriv_void. auto.
  - destruct (deriv_epsilon x); simpl in *; intuition; [rewrite <- H0 | rewrite <- H1]; auto.
  - destruct (deriv_letter t x); simpl in *; intuition; [rewrite <- H0 | rewrite <- H1 | rewrite <- H0]; auto.
  - rewrite <- (rev_involutive x). induction (rev x); simpl.
    + apply mixcat_in. exists (canon r1), []. intuition.
      * simpl. rewrite sOr_void_r, canon_canon. reflexivity.
      * apply finite_derivatives with (r:=r1) (w:=[]).
    + apply finite_derivatives with (r:=Cat r1 r2) (w:=rev l++[a]).
  - rewrite <- (rev_involutive x). induction (rev x); simpl.
    + auto.
    + apply finite_derivatives with (r:=Star r) (w:=rev l++[a]).
  - rewrite (deriv_or r1 r2). apply in_map_iff. exists ((canon (r1 // x)), (canon (r2 // x))). intuition. apply product_ok. split; [eapply IHr1 | eapply IHr2]; apply PreCondition_init.
  - rewrite (deriv_and r1 r2). apply in_map_iff. exists ((canon (r1 // x)), (canon (r2 // x))). intuition. apply product_ok. split; [eapply IHr1 | eapply IHr2]; apply PreCondition_init.
  - rewrite (deriv_not r). apply in_map_iff. exists (canon (r // x)). intuition. eapply IHr, PreCondition_init.
Qed.

Lemma REs_elements_nodup r: NoDup (REs.elements r).
Proof.
  apply Sorted_NoDup, REs.elements_spec2.
Qed.

Lemma explore_converges_n0 r explored seen : PreCondition r explored seen ->
 REs.cardinal explored <= derivs_bound r.
Proof.
  intro. apply explore_converges_n0_aux in H. rewrite <- derivs_bound_ok. apply Nat.le_trans with (REs.cardinal (REs.union explored seen)).
  - apply REsP.subset_cardinal. REsdec.
  - rewrite REs.cardinal_spec. apply NoDup_incl_length.
    + apply REs_elements_nodup.
    + assumption.
Qed.

Lemma explore_converges r n explored seen :
 derivs_bound r < n + REs.cardinal explored ->
 PreCondition r explored seen ->
 ~REs.Empty (explore n explored seen).
Proof.
  revert explored seen. induction n; intros; intro; simpl in *.
  - apply explore_converges_n0 in H0. lia.
  - case REs.choose eqn:Hcase.
    + eapply PreCondition_next in H0.
      * apply IHn with (explored:=REs.add e explored) (seen:=REs.union (allderiv1 e) (REs.remove e (REs.diff seen explored))).
        -- rewrite REsP.add_cardinal_2.
          ++ lia.
          ++ apply REs.choose_spec1, REs.diff_spec in Hcase. intuition.
        -- eassumption.
        -- assumption.
      * apply REs.choose_spec1. assumption.
    +  unfold PreCondition in H0. intuition. apply REsP.empty_is_empty_1 in H2.
      * REsdec.
      * rewrite REsP.empty_union_1; intuition. apply REs.choose_spec2 in Hcase. REsdec.
Qed.

Lemma explore_spec r n explored seen :
 derivs_bound r < n + REs.cardinal explored ->
 PreCondition r explored seen ->
 ExactDerivSet r (explore n explored seen).
Proof.
  intros. apply explore_converges with (seen:=seen) in H; intuition. apply explore_partial_spec with (n:=n) in H0. destruct H0; intuition.
Qed.

Lemma slow_exact_derivs_spec r :
  ExactDerivSet r (slow_exact_derivs r).
Proof.
  unfold slow_exact_derivs, try_exact_derivs. apply explore_spec.
  - lia.
  - apply PreCondition_init.
Qed.

Lemma exact_derivs_spec r :
  ExactDerivSet r (exact_derivs r).
Proof.
  unfold exact_derivs. case REs.is_empty eqn:Hcase.
  - apply slow_exact_derivs_spec.
  - unfold try_exact_derivs in *. destruct (explore_partial_spec r 100 REs.empty (REs.singleton (canon r))); intuition.
    + apply PreCondition_init.
    + rewrite <- REs.is_empty_spec in H. congruence.
Qed.

Lemma exact_derivs_alt r :
  REs.Equal (exact_derivs r) (slow_exact_derivs r).
Proof.
  unfold REs.Equal. split; intros.
  - apply slow_exact_derivs_spec. apply exact_derivs_spec. assumption.
  - apply exact_derivs_spec. apply slow_exact_derivs_spec. assumption.
Qed.

Lemma exact_derivs_init r : REs.In (canon r) (exact_derivs r).
Proof.
  apply exact_derivs_spec. exists []. reflexivity.
Qed.

(** The exact count of derivatives of [r] not identified by [=~=] *)

Definition derivs_sim_nb r := REs.cardinal (exact_derivs r).

Lemma derivs_sim_nb_nz r : derivs_sim_nb r <> 0.
Proof.
  unfold derivs_sim_nb. assert(H: REs.Subset (REs.singleton (canon r)) (exact_derivs r)). { unfold REs.Subset. intros. apply REs.singleton_spec in H. rewrite H. apply exact_derivs_init. } apply REsP.subset_cardinal in H. rewrite REsP.singleton_cardinal in H. lia.
Qed.

(** Any list of derivatives without duplicates
    is smaller than [exact_derivs]. *)

Definition DerivList r l := forall r', In r' l -> Deriv r r'.

Lemma derivs_smaller r l :
  NoDup l -> DerivList r l -> length l <= derivs_sim_nb r.
Proof.
  unfold derivs_sim_nb, DerivList. intros. rewrite REs.cardinal_spec. apply NoDup_incl_length.
  - assumption.
  - unfold incl. intros. destruct (exact_derivs_spec r a). apply REs_elements_spec. auto.
Qed.

(** Any complete list of derivatives is larger than [exact_derivs]. *)

Lemma derivs_larger r l :
  AllDerivsIn r l -> derivs_sim_nb r <= length l.
Proof.
  unfold AllDerivsIn. intros. unfold derivs_sim_nb. rewrite REs.cardinal_spec. apply NoDup_incl_length.
  - apply REs_elements_nodup.
  - unfold incl. intros. destruct (exact_derivs_spec r a). apply REs_elements_spec, H1 in H0. destruct H0. rewrite H0. apply H.
Qed.

(** In particular, the first bound on derivatives is (way) larger
    than [derivs_sim_nb]. *)

Lemma exact_below_bound r : derivs_sim_nb r <= derivs_bound r.
Proof.
  rewrite <- derivs_bound_ok. apply derivs_larger, finite_derivatives.
Qed.

(** Same results using [sim] instead of [canon]. *)

Lemma InToInA r l: In (canon r) (map canon l) -> InA sim r l.
Proof.
  induction l; intros; simpl in *.
  - apply InA_nil. auto.
  - destruct H.
    + apply InA_cons_hd. apply canon_spec. congruence.
    + apply InA_cons. right. apply IHl. assumption.
Qed.

Lemma NoDupA_sim_canon l : NoDupA sim l -> NoDup (map canon l).
Proof.
  induction l; simpl; intros.
  - apply NoDup_nil.
  - apply NoDup_cons.
    + intro. inversion H. apply InToInA in H0. contradiction.
    + apply IHl. inversion H. assumption.
Qed.

Lemma derivs_sim_smaller r l :
 NoDupA sim l -> (forall r', In r' l -> exists w, r' =~= r//w) ->
 length l <= derivs_sim_nb r.
Proof.
  intros. apply NoDupA_sim_canon, derivs_smaller with (r:=r) in H.
  - rewrite map_length in H. assumption.
  - unfold DerivList. intros. apply in_map_iff in H1. destruct H1,H1. apply H0 in H2. destruct H2. exists x0. rewrite <- H1. apply canon_spec. assumption.
Qed.

Lemma derivs_sim_larger r l :
 AllDerivsInMod sim r l -> derivs_sim_nb r <= length l.
Proof.
  intros. unfold derivs_sim_nb. rewrite REs.cardinal_spec. rewrite <- map_length with (f:=canon) at 1. apply NoDup_incl_length.
  - apply REs_elements_nodup.
  - unfold incl. intros. destruct (exact_derivs_spec r a). apply REs_elements_spec, H1 in H0. destruct H0. rewrite H0. destruct H with x. destruct H3. apply canon_spec in H3. rewrite H3. apply in_map. assumption.
Qed.

End RegExplore.
