(* S K combinators *)
Inductive expr :=
| var : nat -> expr (* var 0 denotes variable 0, var 1 denotes variable 1, etc *)
| S : expr
| K : expr
| app : expr -> expr -> expr.

Notation " a [+] b " := (app a b) (at level 50, left associativity).

Inductive steps : expr -> expr -> Prop :=
| steps_S : forall x y z, steps (S [+] x [+] y [+] z) (x [+] z [+] (y [+] z))
| steps_K : forall x y, steps (K [+] x [+] y) x
| steps_app_l : forall x y z, steps x y -> steps (x [+] z) (y [+] z)
| steps_app_r : forall x y z, steps x y -> steps (z [+] x) (z [+] y).

Notation " a ~> b " := (steps a b) (at level 55, left associativity).

Lemma steps_Kx_cases : forall x c, K [+] x ~> c -> exists x', (x ~> x' /\ c = K [+] x').
Proof.
  intros.
  inversion H. subst. inversion H3. subst.
  exists y. auto.
Qed.

Lemma steps_Sx_cases : forall x c, S [+] x ~> c -> exists x', (x ~> x' /\ c = S [+] x').
Proof.
  intros.
  inversion H. subst. inversion H3. subst.
  exists y. auto.
Qed.

Lemma steps_Sxy_cases : forall x y c, S [+] x [+] y ~> c ->
                                      ((exists x', x ~> x' /\ c = S [+] x' [+] y) \/
                                       (exists y', y ~> y' /\ c = S [+] x [+] y')).
Proof.
  intros.
  inversion H. subst.
  apply steps_Sx_cases in H3.
  destruct H3; subst.
  destruct H0. 
  left. exists x0. split. auto. subst. auto. subst.
  right. exists y0. auto.
Qed.

Definition is_normal c := forall c', ~ c ~> c'.

Inductive steps_star : expr -> expr -> Prop :=
| steps_none : forall c, steps_star c c
| steps_once : forall c1 c2, c1 ~> c2 -> steps_star c1 c2
| steps_many : forall c1 c2 c3, c1 ~> c2 -> steps_star c2 c3 -> steps_star c1 c3.

Notation " a ~>* b " := (steps_star a b) (at level 55, left associativity).

Theorem steps_star_trans : forall c1 c2 c3, (c1 ~>* c2) -> (c2 ~>* c3) -> (c1 ~>* c3).
Proof.
  intros.

  induction H.
  *
    assumption.
  *
    eapply steps_many.
    apply H.
    apply H0.
  *
    eapply steps_many.
    apply H.
    apply IHsteps_star.
    apply H0.
Qed.

Theorem steps_star_app_l : forall c1 c2 c3, (c1 ~>* c2) -> (c1 [+] c3) ~>* (c2 [+] c3).
Proof.
  intros.
  induction H.
  *
    apply steps_none.
  *
    eapply steps_once.
    apply steps_app_l.
    apply H.
  *
    eapply steps_many.
    apply steps_app_l.
    apply H.
    apply IHsteps_star.
Qed.

Theorem steps_star_app_r : forall c1 c2 c3, (c1 ~>* c2) -> (c3 [+] c1) ~>* (c3 [+] c2).
Proof.
  intros.
  induction H.
  *
    apply steps_none.
  *
    eapply steps_once.
    apply steps_app_r.
    apply H.
  *
    eapply steps_many.
    apply steps_app_r.
    apply H.
    apply IHsteps_star.
Qed.

Inductive contains_var (n : nat) : expr -> Prop :=
| contains_here : contains_var n (var n)
| contains_left : forall c1 c2, contains_var n c1 -> contains_var n (c1 [+] c2)
| contains_right : forall c1 c2, contains_var n c2 -> contains_var n (c1 [+] c2).

Notation "  n 'IN' c " := (contains_var n c) (at level 60, no associativity).

Definition is_const c := forall n, ~ n IN c.

Lemma is_const_S : is_const S.
Proof.
  unfold is_const.
  unfold not.
  intros.
  inversion H.
Qed.

Lemma is_const_K : is_const K.
Proof.
  unfold is_const.
  unfold not.
  intros.
  inversion H.
Qed.

Theorem not_is_const_var : forall n, ~is_const (var n).
Proof.
  intros.
  unfold is_const.
  unfold not. intros.
  apply (H n). clear H.
  constructor.
Qed.

Theorem contains_var_app_iff : forall n c1 c2, n IN (c1 [+] c2) <-> n IN c1 \/ n IN c2.
Proof.
  intros.
  split.
  *
    intros.
    inversion H; subst.
    left. auto.
    right. auto.
  *
    intros.
    destruct H.
    apply contains_left. auto.
    apply contains_right. auto.
Qed.

Theorem not_contains_var_app_iff : forall n c1 c2, ~ n IN (c1 [+] c2) <-> ~ n IN c1 /\ ~ n IN c2.
Proof.
  intros.
  split.
  intros.
  *
    split;
    unfold not;
    intros;
    apply H.
    apply contains_left. auto.
    apply contains_right. auto.
  *
    intros.
    destruct H.
    unfold not. intros.
    inversion H1; subst; contradiction.
Qed.
    
Theorem contains_var_var_iff : forall n m, n IN var m <-> m = n.
Proof.
  intros.
  split.
  *
    intros.
    inversion H. subst. auto.
  *
    intros.
    subst. constructor.
Qed.

Theorem not_contains_var_var_iff : forall n m, ~n IN var m <-> m <> n.
Proof.
  intros.
  split.
  *
    intros.
    unfold not. intros.
    subst.
    apply H.
    constructor.
  *
    intros.
    unfold not.
    intros.
    apply H.
    apply contains_var_var_iff. auto.
Qed.

Theorem is_const_app_iff : forall c1 c2, is_const (c1 [+] c2) <-> is_const c1 /\ is_const c2.
Proof.
  intros.
  split.
  intros.
  split.
  unfold is_const.
  intros.
  unfold is_const in H.
  generalize (H n). intros.
  apply not_contains_var_app_iff in H0. apply H0.
  unfold is_const.
  intros.
  unfold is_const in H.
  generalize (H n). intros.
  apply not_contains_var_app_iff in H0. apply H0.
  intros.
  unfold is_const.
  intros. unfold not. intros.
  unfold is_const in H. unfold not in H. destruct H.
  apply contains_var_app_iff in H0.
  destruct H0.
  eapply H. apply H0.
  eapply H1. apply H0.
Qed.
