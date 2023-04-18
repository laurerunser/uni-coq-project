Require Export Bool List Equalities Orders Setoid Morphisms.
Import ListNotations.

(** * Languages are sets of words over some type of letters *)

Module Lang (Letter : Typ).

Definition word := list Letter.t.
Definition t := word -> Prop.

Declare Scope lang_scope.
Bind Scope lang_scope with t.
Delimit Scope lang_scope with lang.
Local Open Scope lang_scope.

Implicit Type a : Letter.t.
Implicit Type w x y z : word.
Implicit Type L : t.

Definition eq L L' := forall x, L x <-> L' x.

Definition void : t := fun _ => False.
Definition epsilon : t := fun w => w = [].
Definition singleton a : t := fun w => w = [a].

Definition cat L L' : t :=
  fun x => exists y z, x = y++z /\ L y /\ L' z.

Definition union L L' : t := fun w => L w \/ L' w.

Definition inter L L' : t := fun w => L w /\ L' w.

Fixpoint power L n : t :=
  match n with
  | 0 => epsilon
  | S n' => cat L (power L n')
  end.

(** Kleene's star *)

Definition star L : t := fun w => exists n, power L n w.

(** language complement *)

Definition comp L : t := fun w => ~(L w).

(** Languages : notations **)

Module Notations.
Infix "==" := Lang.eq (at level 70).
Notation "∅" := void : lang_scope. (* \emptyset *)
Notation "'ε'" := epsilon : lang_scope. (* \epsilon *)
Coercion singleton : Letter.t >-> Lang.t.
Infix "·" := cat (at level 35) : lang_scope. (* \cdot *)
Infix "∪" := union (at level 50) : lang_scope. (* \cup *)
Infix "∩" := inter (at level 40) : lang_scope. (* \cap *)
Infix "^" := power : lang_scope.
Notation "L ★" := (star L) (at level 30) : lang_scope. (* \bigstar *)
Notation "¬ L" := (comp L) (at level 65): lang_scope. (* \neg *)
End Notations.
Import Notations.

(** Technical stuff to be able to rewrite with respect to "==" *)

Global Instance : Equivalence eq.
Proof. firstorder. Qed.

Global Instance cat_eq : Proper (eq ==> eq ==> eq) cat.
Proof. firstorder. Qed.
Global Instance inter_eq : Proper (eq ==> eq ==> eq) inter.
Proof. firstorder. Qed.
Global Instance union_eq : Proper (eq ==> eq ==> eq) union.
Proof. firstorder. Qed.
Global Instance comp_eq : Proper (eq ==> eq) comp.
Proof. firstorder. Qed.
Global Instance power_eq : Proper (eq ==> Logic.eq ==> eq) power.
Proof.
 intros x x' Hx n n' <-. induction n; simpl; now rewrite ?IHn, ?Hx.
Qed.

Global Instance cat_eq' : Proper (eq ==> eq ==> Logic.eq ==> iff) cat.
Proof. intros x x' Hx y y' Hy w w' <-. now apply cat_eq. Qed.
Global Instance inter_eq' : Proper (eq ==> eq ==> Logic.eq ==> iff) inter.
Proof. intros x x' Hx y y' Hy w w' <-. now apply inter_eq. Qed.
Global Instance union_eq' : Proper (eq ==> eq ==> Logic.eq ==> iff) union.
Proof. intros x x' Hx y y' Hy w w' <-. now apply union_eq. Qed.
Global Instance comp_eq' : Proper (eq ==> Logic.eq ==> iff) comp.
Proof. intros x x' Hy w w' <-. now apply comp_eq. Qed.
Global Instance power_eq' : Proper (eq ==> Logic.eq ==> Logic.eq ==> iff) power.
Proof. intros x x' Hx n n' <- w w' <-. now apply power_eq. Qed.

Global Instance star_eq : Proper (eq ==> eq) star.
Proof.
 intros x x' Hx w. unfold star. now setoid_rewrite <- Hx.
Qed.

Global Instance star_eq' : Proper (eq ==> Logic.eq ==> iff) star.
Proof. intros x x' Hx w w' <-. now apply star_eq. Qed.

(** Languages : misc properties *)

Lemma cat_void_l L : ∅ · L == ∅.
Proof.
  firstorder.
Qed.

Lemma cat_void_r L :  L · ∅ == ∅.
Proof.
  firstorder.
Qed.

Lemma cat_eps_l L : ε · L == L.
Proof.
  split; intros.
  - do 3 destruct H. destruct H0. rewrite H0 in H. simpl in H. congruence.
  - exists [], x. intuition congruence.
Qed.

Lemma cat_eps_r L : L · ε == L.
Proof.
  split; intros.
  - do 3 destruct H. destruct H0. red in H1. rewrite H1 in H. rewrite app_nil_r in H. congruence.
  - exists x, []. rewrite app_nil_r. intuition congruence.
Qed.

Lemma cat_assoc L1 L2 L3 : (L1 · L2) · L3 == L1 · (L2 · L3).
Proof.
  split; intros; do 3 destruct H; destruct H0; [do 3 destruct H0 | do 3 destruct H1]; destruct H2.
  - exists x2, (x3++x1). intuition.
    + rewrite app_assoc. congruence.
    + firstorder.
  - exists (x0++x2), x3. intuition.
    + rewrite app_assoc_reverse. congruence.
    + firstorder.
Qed.

Lemma star_eqn L : L★ == ε ∪ L · L ★.
Proof.
  split; intros.
  - destruct H, x0; firstorder.
  - destruct H.
    + exists 0. assumption.
    + do 3 destruct H. destruct H0, H1. exists (S x2). firstorder.
Qed.

Lemma star_void : ∅ ★ == ε.
Proof.
  split; intros.
  - destruct H, x0; firstorder.
  - exists 0. assumption.
Qed.

Lemma power_eps n : ε ^ n == ε.
Proof.
  split; intros.
  - induction n.
    + assumption.
    + do 3 destruct H. destruct H0. rewrite H0 in H. simpl in H. rewrite <- H in H1. auto.
  - induction n.
    + assumption.
    + exists [], []. intuition congruence.
Qed.

Lemma star_eps : ε ★ == ε.
Proof.
  split; intros.
  - destruct H, x0.
    + assumption.
    + apply power_eps in H. assumption.
  - exists 0. assumption.
Qed.

Lemma power_app n m y z L :
 (L^n) y -> (L^m) z -> (L^(n+m)) (y++z).
Proof.
  revert m y z. induction n; intros.
  - rewrite H. auto.
  - do 3 destruct H. destruct H1. exists x, (x0 ++ z). firstorder. rewrite app_assoc. congruence.
Qed.

Lemma star_star L : (L★)★ == L★.
Proof.
  split; intros.
  - destruct H. revert x H. induction x0; intros.
    + exists 0. assumption.
    + do 3 destruct H. do 2 destruct H0. apply IHx0 in H1. destruct H1. rewrite H. exists (x3+x4). apply power_app with (n:=x3)(m:=x4)(y:=x1)(z:=x2); assumption.
 - exists 1, x, []. rewrite app_nil_r. firstorder.
Qed.

Lemma cat_star L : (L★)·(L★) == L★.
Proof.
  split; intros; destruct H.
  - do 2 destruct H. do 2 destruct H0. destruct H1. exists (x2 + x3). rewrite H. apply power_app; assumption.
  -  exists [], x. firstorder. exists 0. firstorder.
Qed.

(** ** Derivative of a language : definition **)

Definition derivative L w : t := fun x => L (w++x).

Global Instance derivative_eq : Proper (eq ==> Logic.eq ==> eq) derivative.
Proof. intros L L' HL w w' <-. unfold derivative. intro. apply HL. Qed.

(** ** Derivative of a language : properties **)

Lemma derivative_app L w w' :
  derivative L (w++w') == derivative (derivative L w) w'.
Proof.
  unfold derivative. split; intros; [rewrite app_assoc | rewrite <- app_assoc]; assumption.
Qed.

Lemma derivative_cat_null L L' a : L [] ->
  derivative (L · L') [a] == (derivative L [a] · L') ∪ derivative L' [a].
Proof.
  unfold derivative. split; intros; destruct H0.
  - do 2 destruct H0. destruct H1, x0.
    + right. simpl in *. congruence.
    + left. rewrite <- 2 app_comm_cons in H0. injection H0. intros. rewrite H3, H4. firstorder.
  - do 2 destruct H0. exists ([a]++x0), x1. rewrite <- app_assoc. intuition congruence.
  - exists [], ([a]++x). auto.
Qed.

Lemma derivative_cat_nonnull L L' a : ~L [] ->
  derivative (L · L') [a] == derivative L [a] · L'.
Proof.
  unfold derivative. split; intros; do 3 destruct H0; destruct H1.
  - destruct x0.
    + contradiction.
    + rewrite <- 2 app_comm_cons in H0. injection H0. intros. rewrite H3, H4. firstorder.
  - unfold cat. exists ([a]++x0), x1. rewrite <- app_assoc. intuition congruence.
Qed.

Lemma derivative_star L a :
  derivative (L★) [a] == (derivative L [a]) · (L★).
Proof.
  unfold derivative. split; intro; destruct H.
  - induction x0.
    + discriminate.
    + do 3 destruct H. destruct H0, x1.
      * simpl in *. rewrite <- H in H1; apply IHx0, H1.
      * rewrite <- 2 app_comm_cons in H. injection H. intros. rewrite H2, H3. firstorder.
  - do 2 destruct H. destruct H0, H1. exists (S x2), ([a]++x0), x1. rewrite <- app_assoc. intuition congruence.
Qed.

End Lang.
