Require Import SKI.expr.

Inductive lsteps : expr -> expr -> Prop :=
| lsteps_steps : forall c1 c2, c1 ~> c2 -> lsteps c1 c2
| lsteps_app : forall a1 a2 b1 b2, (lsteps a1 a2) -> (lsteps b1 b2) -> (lsteps (a1 [+] b1) (a2 [+] b2))
| lsteps_id : forall c, lsteps c c.

Notation " a l~> b " := (lsteps a b) (at level 55, left associativity).

Inductive lsteps_star : expr -> expr -> Prop :=
| lsteps_none : forall c, lsteps_star c c
| lsteps_once : forall c1 c2, c1 l~> c2 -> lsteps_star c1 c2
| lsteps_many : forall c1 c2 c3, c1 l~> c2 -> lsteps_star c2 c3 -> lsteps_star c1 c3.

Notation " a l~>* b " := (lsteps_star a b) (at level 55, left associativity).

Theorem lsteps_star_trans : forall c1 c2 c3, c1 l~>* c2 -> c2 l~>* c3 -> c1 l~>* c3.
Proof.
  intros.
  induction H.
  *
    auto.
  *
    eapply lsteps_many.
    apply H. auto.
  *
    eapply lsteps_many.
    apply H.
    apply IHlsteps_star. auto.
Qed.
    
Lemma lsteps_imp_steps_star : forall c1 c2, c1 l~> c2 -> (c1 ~>* c2).
Proof.
  intros.
  induction H.
  *
    apply steps_once. auto.
  *
    eapply steps_star_trans.
    apply steps_star_app_l. apply IHlsteps1.
    apply steps_star_app_r. apply IHlsteps2.
  *
    apply steps_none.
Qed.

Lemma steps_star_imp_lsteps_star : forall c1 c2, c1 ~>* c2 -> c1 l~>* c2.
Proof.
  intros.
  induction H.
  *
    apply lsteps_none.
  *
    apply lsteps_once. apply lsteps_steps. auto.
  *
    eapply lsteps_many.
    apply lsteps_steps.
    apply H. auto.
Qed.

Lemma lsteps_star_imp_steps_star : forall c1 c2, c1 l~>* c2 -> c1 ~>* c2.
Proof.
  intros.
  induction H.
  *
    apply steps_none.
  *
    apply lsteps_imp_steps_star.
    auto.
  *
    eapply steps_star_trans.
    apply lsteps_imp_steps_star. apply H.
    apply IHlsteps_star.
Qed.

Theorem lsteps_app_cases : forall a b c, a [+] b l~> c ->
   (
     (exists x y, a = (S [+] x [+] y) /\ c = x [+] b [+] (y [+] b)) \/ (* steps_S *)
     (exists x, a = (K [+] x) /\ c = x) \/ (* steps_K *)
     (exists a' b', ((a l~> a') /\ (b l~> b') /\ c = (a' [+] b'))) \/ (* lsteps_app*)
     (c = a [+] b) (* lsteps_id *)
   ).
Proof.
  intros.
  inversion H; subst.
  *
    inversion H0; subst.
    left.
    exists x, y.
    split; auto.

    right. left.
    exists c. split; auto.

    right. right. left.
    exists y, b. split; auto. apply lsteps_steps. auto.
    split; auto. apply lsteps_id.

    right. right. left.
    exists a, y.
    split; auto. apply lsteps_id.
    split; auto. apply lsteps_steps. auto.

  *
    right. right. left.
    exists a2, b2.
    split; auto.
  *
    right. right. right. auto.
Qed.

Lemma lsteps_var_cases : forall c n, var n l~> c -> c = var n.
Proof.
  intros.
  inversion H.
  subst.
  inversion H0. subst. auto.
Qed.

Lemma lsteps_K_cases : forall c, K l~> c -> c = K.
Proof.
  intros.
  inversion H. subst. inversion H0. auto.
Qed.

Lemma lsteps_S_cases : forall c, S l~> c -> c = S.
Proof.
  intros.
  inversion H. subst. inversion H0. auto.
Qed.

Lemma lsteps_Sx_cases :
  forall x c, S [+] x l~> c ->
              (exists x', x l~> x' /\ c = S [+] x').
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst. inversion H4.
  exists y. split. apply lsteps_steps. auto. auto.
  inversion H2; subst. inversion H0.
  exists b2. split; auto.
  exists x. split; auto. apply lsteps_id.
Qed.

Lemma lsteps_Sxy_cases :
  forall x y c, S [+] x [+] y l~> c ->
                (exists x' y', x l~> x' /\ y l~> y' /\ c = S [+] x' [+] y').
Proof.
  intros.
  inversion H; subst.
  *
    apply steps_Sxy_cases in H0.
    destruct H0. destruct H0. destruct H0.
    exists x0, y. split. apply lsteps_steps. auto.
    split. apply lsteps_id. auto.

    destruct H0. destruct H0.
    exists x, x0.
    split. apply lsteps_id.
    split. apply lsteps_steps. auto. auto.
  *
    apply lsteps_Sx_cases in H2.
    destruct H2. destruct H0. subst.
    exists x0, b2.
    split. auto. split. auto. auto.
  *
    exists x, y.
    split. apply lsteps_id.
    split. apply lsteps_id. auto.
Qed.
  
Lemma lsteps_Kx_cases :
  forall x c, K [+] x l~> c ->
              (exists x', x l~> x' /\ c = K [+] x').
Proof.
  intros.
  inversion H; subst.
  *
    apply steps_Kx_cases in H0.
    destruct H0.
    destruct H0.
    rewrite H1.
    exists x0. split.
    apply lsteps_steps. auto. auto.
  *
    apply lsteps_K_cases in H2. subst.
    exists b2. split; auto.
  *
    exists x.
    split.
    apply lsteps_id. auto.
Qed.

Definition is_lsteps_diamond c := forall c1 c2, (c l~> c1) -> (c l~> c2) -> (exists c3, c1 l~> c3 /\ c2 l~> c3).
Definition is_lsteps_star_diamond c := forall c1 c2, (c l~>* c1) -> (c l~>* c2) -> (exists c3, c1 l~>* c3 /\ c2 l~>* c3).
Definition is_steps_star_diamond c := forall c1 c2, (c ~>* c1) -> (c ~>* c2) -> (exists c3, c1 ~>* c3 /\ c2 ~>* c3).

Theorem lsteps_confluent : forall c, is_lsteps_diamond c.
Proof.
  intros.
  induction c.
  *
    unfold is_lsteps_diamond.
    intros.
    apply lsteps_var_cases in H.
    apply lsteps_var_cases in H0.
    subst.
    exists (var n). split; apply lsteps_id.
  *
    unfold is_lsteps_diamond.
    intros.
    apply lsteps_S_cases in H.
    apply lsteps_S_cases in H0.
    subst.
    exists S. split; apply lsteps_id.
  *
    unfold is_lsteps_diamond.
    intros.
    apply lsteps_K_cases in H.
    apply lsteps_K_cases in H0.
    subst.
    exists K. split; apply lsteps_id.
  *
    unfold is_lsteps_diamond.
    intros.

    apply lsteps_app_cases in H. destruct H.
    apply lsteps_app_cases in H0. destruct H0.

    **
      destruct H. destruct H. destruct H.
      destruct H0. destruct H0. destruct H0.
      subst.
      inversion H0. subst.
      exists (x1 [+] c2 [+] (x2 [+] c2)).
      split; apply lsteps_id.
    **
      destruct H. destruct H. destruct H.
      destruct H0. destruct H0. destruct H0.
      subst.
      inversion H0. subst.
      destruct H0. destruct H. destruct H. destruct H.
      destruct H0. subst.

      apply lsteps_Sxy_cases in H.
      destruct H. destruct H. destruct H. destruct H1.
      subst.
      exists (x3 [+] x2 [+] (x4 [+] x2)).
      split.
      apply lsteps_app. apply lsteps_app. auto. auto.
      apply lsteps_app. auto. auto.
      apply lsteps_steps. apply steps_S.
      rewrite H. clear H.
      exists (x [+] c2 [+] (x0 [+] c2)).
      split. apply lsteps_id.
      apply lsteps_steps. apply steps_S.
    **
      destruct H. destruct H. destruct H. subst.
      inversion H0. subst.
      inversion H. subst.
      exists c3. split; apply lsteps_id.
      subst.
      apply steps_Kx_cases in H4. destruct H4. destruct H1.
      subst.
      exists x0. split. apply lsteps_steps. auto.
      apply lsteps_steps. apply steps_K. subst.
      exists x. split. apply lsteps_id.
      apply lsteps_steps. apply steps_K. subst.
      apply lsteps_Kx_cases in H2. destruct H2. destruct H.
      subst.
      exists x0. split. auto. apply lsteps_steps. apply steps_K.
      subst.
      exists x.
      split. apply lsteps_id. apply lsteps_steps. apply steps_K.
      destruct H. destruct H. destruct H. destruct H. destruct H1.
      subst.
      apply lsteps_app_cases in H0.
      destruct H0. destruct H0. destruct H0. destruct H0.
      subst.
      apply lsteps_Sxy_cases in H.
      destruct H. destruct H. destruct H. destruct H. destruct H0.
      subst.
      exists (c0 [+] x0 [+] (x4 [+] x0)).
      split. apply lsteps_steps. apply steps_S.
      apply lsteps_app. apply lsteps_app. apply lsteps_steps. auto. auto.
      apply lsteps_app. auto. auto.
      destruct H0. subst.
      exists (a2 [+] b2 [+] x0 [+] (x4 [+] x0)).
      split. apply lsteps_steps. apply steps_S.
      apply lsteps_app. apply lsteps_app. apply lsteps_app. auto. auto. auto.
      apply lsteps_app. auto. auto.
      destruct H0. subst.
      exists (c [+] x0 [+] (x4 [+] x0)).
      split. apply lsteps_steps. apply steps_S.
      apply lsteps_app. apply lsteps_app. apply lsteps_id. auto.
      apply lsteps_app. auto. auto.
      destruct H0. destruct H0. destruct H0. subst.
      apply lsteps_Kx_cases in H. destruct H. destruct H. subst.
      exists x2. split. apply lsteps_steps. apply steps_K. auto.
      destruct H0. destruct H0. destruct H0. destruct H0. destruct H2. subst.
      assert (exists c1', x l~> c1' /\ x1 l~> c1').
      apply IHc1. auto. auto.
      assert (exists c2', x0 l~> c2' /\ x2 l~> c2').
      apply IHc2. auto. auto.
      destruct H3. destruct H3.
      destruct H4. destruct H4.
      exists (x3 [+] x4).
      split; apply lsteps_app; auto.
      subst.
      exists (x [+] x0).
      split. apply lsteps_id.
      apply lsteps_app; auto.
      subst.
      exists c3. split. auto.
      apply lsteps_id.
Qed.

Lemma lsteps_star_confluent0 : forall a b, a l~>* b ->
                                           (forall a', a l~> a' -> exists b', a' l~>* b' /\ b l~>* b').
Proof.
  intros a b H.
  induction H.
  *
    (* a <- c *)
    intros.
    exists a'.
    split.
    apply lsteps_none.
    apply lsteps_once. auto.
  *
    intros.
    assert (is_lsteps_diamond c1) by apply lsteps_confluent.
    destruct (H1 c2 a'); auto.
    destruct H2.
    exists x.
    split.
    apply lsteps_once. auto.
    eapply lsteps_many.
    apply H2. apply lsteps_none.
  *
    intros.
    assert (is_lsteps_diamond c1) by apply lsteps_confluent.
    destruct (H2 c2 a'); auto.
    destruct H3.
    apply IHlsteps_star in H3. destruct H3. destruct H3.
    exists x0.
    split.
    eapply lsteps_many. apply H4. auto.
    auto.
Qed.

Theorem lsteps_star_confluent : forall c, is_lsteps_star_diamond c.
Proof.
  intros.
  unfold is_lsteps_star_diamond.
  intros c1 c2 H.
  generalize c2. clear c2.

  induction H.
  *
    intros.
    exists c2.
    split. auto. apply lsteps_none.
  *
    intros.
    eapply lsteps_star_confluent0.
    apply H0. auto.
  *
    intros.
    assert (exists c4, c2 l~>* c4 /\ c0 l~>* c4). {
      eapply lsteps_star_confluent0.
      apply H1. auto.
    }
    destruct H2.
    destruct H2.
    apply IHlsteps_star in H2.
    destruct H2. destruct H2.
    exists x0.
    split. auto.
    eapply lsteps_star_trans.
    apply H3. apply H4.
Qed.
      
Theorem steps_star_confluent : forall c, is_steps_star_diamond c.
Proof.
  intros.
  unfold is_steps_star_diamond.
  intros.
  assert (is_lsteps_star_diamond c) by apply lsteps_star_confluent.
  unfold is_lsteps_star_diamond in H1.
  assert (c l~>* c1). {
    apply steps_star_imp_lsteps_star.
    auto.
  }
  assert (c l~>* c2). {
    apply steps_star_imp_lsteps_star.
    auto.
  }
  destruct (H1 _ _ H2 H3).
  destruct H4.
  exists x.
  split.
  apply lsteps_star_imp_steps_star.
  auto.
  apply lsteps_star_imp_steps_star.
  auto.
Qed.

Theorem steps_star_normal_cases : forall c, is_normal c -> forall x, c ~>* x -> c = x.
Proof.
  intros.
  inversion H0; subst.
  *
    auto.
  *
    apply H in H1.
    inversion H1.
  *
    apply H in H1.
    inversion H1.
Qed.
  
Theorem unique_normal_form : forall c c1 c2, c ~>* c1 -> c ~>* c2 -> is_normal c1 -> is_normal c2 -> c1 = c2.
Proof.
  intros.
  assert (exists x, c1 ~>* x /\ c2 ~>* x). {
    destruct (steps_star_confluent c c1 c2 H H0).
    exists x. auto.
  }
  destruct H3.
  destruct H3.
  apply steps_star_normal_cases in H3.
  apply steps_star_normal_cases in H4.
  subst.
  auto.
  auto.
  auto.
Qed.
