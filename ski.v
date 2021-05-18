Require Import Lia.
Require Import Nat.
Require Import List.
Import Coq.Arith.Wf_nat. (* needed for "lt_wf_ind" *)


(* S K combinators *)
Inductive cexpr :=
| var : nat -> cexpr (* var 0 denotes variable 0, var 1 denotes variable 1, etc *)
| S : cexpr
| K : cexpr
| app : cexpr -> cexpr -> cexpr.

Notation " a [+] b " := (app a b) (at level 50, left associativity).

Fixpoint cexpr_size c : nat :=
  match c with
  | var _ => 1
  | S => 1
  | K => 1
  | app c1 c2 => cexpr_size c1 + cexpr_size c2
  end.

Inductive contains_var (n : nat) : cexpr -> Prop :=
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

Fixpoint bcontains_var (n : nat) (c : cexpr) : bool :=
  match c with
  | var m => m =? n
  | S => false
  | K => false
  | c1 [+] c2 => orb (bcontains_var n c1) (bcontains_var n c2)
  end.

Notation "n 'bIN' c" := (bcontains_var n c) (at level 60, no associativity).

Definition is_bconst c := forall n, (n bIN c = false).

Theorem bcontains_var_app_true_iff : forall n c1 c2, n bIN (c1 [+] c2) = true <-> n bIN c1 = true \/ n bIN c2 = true.
Proof.
  intros.
  split.
  *
    intros.
    simpl in H.
    apply Bool.orb_true_iff. auto.
  *
    intros.
    simpl.
    apply Bool.orb_true_iff. auto.
Qed.

Theorem bcontains_var_app_false_iff : forall n c1 c2, n bIN (c1 [+] c2) = false <-> n bIN c1 = false /\ n bIN c2 = false.
Proof.
  intros.
  split.
  *
    intros.
    simpl in H.
    apply Bool.orb_false_iff. auto.
  *
    intros.
    simpl.
    apply Bool.orb_false_iff. auto.
Qed.

Theorem bcontains_var_contains_var : forall n c, n IN c <-> n bIN c = true.
Proof.
  intros.
  split.
  *
    intros.
    induction c.
    **
      unfold bcontains_var.
      inversion H.
      rewrite PeanoNat.Nat.eqb_eq.
      reflexivity.
    **
      inversion H.
    **
      inversion H.
    **
      rewrite bcontains_var_app_true_iff.
      apply contains_var_app_iff in H.
      destruct H.
      left. apply IHc1. auto.
      right. apply IHc2. auto.
  *
    intros.
    induction c.
    **
      rewrite contains_var_var_iff.
      simpl in H.
      apply PeanoNat.Nat.eqb_eq. auto.
    **
      inversion H.
    **
      inversion H.
    **
      apply contains_var_app_iff.
      apply bcontains_var_app_true_iff in H.
      destruct H.
      left. apply IHc1. auto.
      right. apply IHc2. auto.
Qed.

Theorem not_bcontains_var_contains_var : forall n c, n bIN c = false <-> ~ n IN c.
Proof.
  intros.
  split.
  *
    intros.
    unfold not.
    intros.
    apply bcontains_var_contains_var in H0.
    rewrite H in H0.
    inversion H0.
  *
    intros.
    unfold not in H.

    destruct (Bool.bool_dec (bcontains_var n c) false).
    **
      assumption.
    **
      apply Bool.not_false_is_true in n0.
      apply bcontains_var_contains_var in n0.
      apply H in n0.
      inversion n0.
Qed.

Theorem not_contains_var_app_iff : forall n c1 c2, ~ n IN (c1 [+] c2) <-> ~ n IN c1 /\ ~ n IN c2.
Proof.
  intros.
  split.
  *
    intros.
    rewrite <- not_bcontains_var_contains_var in H.
    apply bcontains_var_app_false_iff in H.
    destruct H.
    split.
    **
      rewrite <- not_bcontains_var_contains_var. auto.
    **
      rewrite <- not_bcontains_var_contains_var. auto.
  *
    intros.
    rewrite <- not_bcontains_var_contains_var in H.
    rewrite <- not_bcontains_var_contains_var in H.
    rewrite <- not_bcontains_var_contains_var.
    destruct H.
    simpl. rewrite H. rewrite H0. auto.
Qed.

Theorem is_bconst_is_const : forall c, is_const c <-> is_bconst c.
Proof.
  intros.
  split.
  intros. unfold is_bconst. intros.
  apply not_bcontains_var_contains_var. apply H.
  intros. unfold is_const. intros.
  apply not_bcontains_var_contains_var. apply H.
Qed.

Theorem var_not_contains_neq : forall n m, n <> m -> ~ n IN var m.
Proof.
  intros.
  unfold not. intros.
  inversion H0. apply H in H2. auto.
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
  intros.
  rewrite is_bconst_is_const in H.
  rewrite is_bconst_is_const in H.
  destruct H.
  rewrite <- not_bcontains_var_contains_var.
  simpl.
  rewrite H. rewrite H0. auto.
Qed.
    
Inductive steps : cexpr -> cexpr -> Prop :=
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

Inductive steps_star : cexpr -> cexpr -> Prop :=
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

(* lsteps is csteps with an additional reduction rule *)
(* this is a technical device used to prove Church Rosser *)
(* Inductive lexpr := *)
(* | lvar : nat -> lexpr   *)
(* | lS : lexpr *)
(* | lK : lexpr *)
(* | lapp : lexpr -> lexpr -> lexpr. *)

(* Notation " a [[+]] b " := (lapp a b) (at level 50, left associativity). *)
 
Inductive lsteps : cexpr -> cexpr -> Prop :=
| lsteps_steps : forall c1 c2, c1 ~> c2 -> lsteps c1 c2
| lsteps_app : forall a1 a2 b1 b2, (lsteps a1 a2) -> (lsteps b1 b2) -> (lsteps (a1 [+] b1) (a2 [+] b2))
| lsteps_id : forall c, lsteps c c.

(* | lsteps_S : forall x y z, lsteps (lS [[+]] x [[+]] y [[+]] z) (x [[+]] z [[+]] (y [[+]] z)) *)
(* | lsteps_K : forall x y, lsteps (lK [[+]] x [[+]] y) x *)
(* | lsteps_app_l : forall x y z, lsteps x y -> lsteps (x [[+]] z) (y [[+]] z) *)
(* | lsteps_app_r : forall x y z, lsteps x y -> lsteps (z [[+]] x) (z [[+]] y) *)
(* | lsteps_id : forall x, lsteps x x *)
(* | lsteps_special : forall x y z1 z2, lsteps z1 z2 -> lsteps ((x [[+]] z1) [[+]] (y [[+]] z1)) ((x [[+]] z2) [[+]] (y [[+]] z2)). *)

Notation " a l~> b " := (lsteps a b) (at level 55, left associativity).

Inductive lsteps_star : cexpr -> cexpr -> Prop :=
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

Lemma app_cx_ne_c : forall c x, c [+] x <> c.
Proof.
  intro c.
  induction c; try (unfold not; intros; inversion H).
  rewrite H1 in H. subst.
  unfold not in IHc1. eapply IHc1. apply H.
Qed.

Lemma app_xc_ne_c : forall c x, x [+] c <> c.
Proof.
  intro c.
  induction c; try (unfold not; intros; inversion H).
  rewrite H2 in H. subst.
  unfold not in IHc2. eapply IHc2. apply H.
Qed.

Theorem cexpr_dec : forall c1 c2 : cexpr, c1 = c2 \/ c1 <> c2.
Proof.
  intro c.
  induction c.
  *
    intros.
    destruct c2.
    destruct (PeanoNat.Nat.eq_dec n0 n).
    subst. left. auto.
    right. unfold not. intro. inversion H.
    subst. apply n1. auto.
    right. unfold not. intros. inversion H.
    right. unfold not. intros. inversion H.
    right. unfold not. intros. inversion H.
  *
    intros.
    destruct c2.
    right. unfold not. intros. inversion H.
    left. auto.
    right. unfold not. intros. inversion H.
    right. unfold not. intros. inversion H.
  *
    intros.
    destruct c2.
    right. unfold not. intros. inversion H.
    right. unfold not. intros. inversion H.
    left. auto.
    right. unfold not. intros. inversion H.
  *
    intros.
    destruct (IHc1 c0).
    destruct (IHc2 c0).
    subst.
    right.
    apply app_cx_ne_c.

    subst.
    right.
    apply app_cx_ne_c.

    destruct c0.
    right. unfold not. intro contra. inversion contra.
    right. unfold not. intro contra. inversion contra.
    right. unfold not. intro contra. inversion contra.
    
    destruct (IHc1 c0_1);
    destruct (IHc2 c0_2); subst.
    left. auto.
    right. unfold not. intro contra. inversion contra. subst. apply H1. auto.
    right. unfold not. intro contra. inversion contra. subst. apply H0. auto.
    right. unfold not. intro contra. inversion contra. subst. apply H0. auto.
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

Definition is_normal c := forall c', ~ c ~> c'.

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

Theorem steps_star_eq : forall c1 c2 c3, c1 ~>* c2 -> c2 = c3 -> c1 ~>* c3.
Proof.
  intros.
  subst.
  assumption.
Qed.

Definition fmap := nat -> option cexpr.
Definition fmap_empty : fmap := fun n => None.
Definition fmap_assn (f: fmap) (n: nat) (c: cexpr) :=
  fun m => if m =? n then Some c else f m.
Definition fmap_del (f: fmap) (n: nat) :=
  fun m => if m =? n then None else f m.

Notation "'--'" := (fmap_empty).
Notation "n '<<-' c ',' f" := (fmap_assn f n c)
                                (at level 100, c at next level, right associativity).


Fixpoint csubst (c : cexpr) (f: fmap) :=
  match c with
  | var m => match f m with
             | Some c => c
             | None => var m
             end
  | (c1 [+] c2) => (csubst c1 f) [+] (csubst c2 f)
  | S => S
  | K => K
  end.

Notation " e <-- f " := (csubst e f) (at level 65, left associativity).

Definition merge_fmap f1 f2 : nat -> option cexpr :=
  fun n =>
    match f1 n with
    | Some c => Some (c <-- f2)
    | None => f2 n
    end.

Notation " f1 # f2 " := (merge_fmap f1 f2) (at level 50, left associativity).

Theorem subst_subst_merge : forall c f1 f2, (c <-- f1 <-- f2) = (c <-- f1 # f2).
Proof.
  intros.
  induction c.
  *
    simpl.
    unfold merge_fmap.
    destruct (f1 n).
    **
      reflexivity.
    **
      reflexivity.
  *
    reflexivity.
  *
    reflexivity.
  *
    simpl.
    rewrite IHc1.
    rewrite IHc2.
    reflexivity.
Qed.

Definition disjoint_cexpr_fmap (c : cexpr) (f: fmap) :=
  forall n, n IN c -> f n = None.

Theorem subst_disjoint : forall c f, disjoint_cexpr_fmap c f -> (c <-- f) = c.
Proof.
  intros.
  induction c.
  *
    simpl.
    unfold disjoint_cexpr_fmap in H.
    rewrite H.
    reflexivity.
    apply contains_here.
  *
    simpl.
    reflexivity.
  *
    simpl.
    reflexivity.
  *
    simpl.
    rewrite IHc1.
    rewrite IHc2.
    reflexivity.

    unfold disjoint_cexpr_fmap.
    intros.
    unfold disjoint_cexpr_fmap in H.
    apply H.
    apply contains_right. assumption.

    unfold disjoint_cexpr_fmap.
    intros.
    unfold disjoint_cexpr_fmap in H.
    apply H.
    apply contains_left. assumption.
Qed.

Theorem subst_const : forall c f, is_const c -> c <-- f = c.
Proof.
  intros.
  apply subst_disjoint.
  unfold disjoint_cexpr_fmap.
  intros.
  apply H in H0.
  contradiction H0.
Qed.

Theorem subst_split : forall n c1 c f,
    is_const c1 -> (f n = Some c1) -> (c <-- f) = (c <-- (n <<- c1, --)) <-- (fmap_del f n).
Proof.
  intros.
  induction c.
  *
    destruct (PeanoNat.Nat.eq_dec n0 n).
    **
      simpl.
      subst.
      rewrite H0.
      unfold fmap_assn.
      rewrite <- EqNat.beq_nat_refl.
      unfold fmap_del.
      unfold fmap_empty.
      symmetry.
      apply subst_const. auto. 
    **
      simpl.
      rewrite <- PeanoNat.Nat.eqb_neq in n1.
      unfold fmap_assn.
      rewrite n1.
      unfold fmap_del.
      simpl.
      rewrite n1.
      reflexivity.
  *
    simpl. reflexivity.
  *
    simpl. reflexivity.
  *
    simpl.
    rewrite IHc1.
    rewrite IHc2.
    reflexivity.
Qed.

Theorem subst_app_distr :  forall c1 c2 f, (c1 [+] c2 <-- f) = (c1 <-- f) [+] (c2 <-- f).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem steps_subst : forall v1 v2, v1 ~> v2 -> forall f, (v1 <-- f) ~> (v2 <-- f).
Proof.
  intros v1 v2 H.
  induction H; intros.
  *
    simpl.
    apply steps_S.
  *
    simpl.
    apply steps_K.
  *
    simpl.
    apply steps_app_l.
    apply IHsteps.
  *
    simpl.
    apply steps_app_r.
    apply IHsteps.
Qed.

Theorem steps_star_subst : forall v1 v2, v1 ~>* v2 -> forall f, (v1 <-- f) ~>* (v2 <-- f).
Proof.
  intros.
  induction H.
  *
    apply steps_none.
  *
    apply steps_once.
    apply steps_subst.
    assumption.
  *
    eapply steps_many.
    apply steps_subst.
    apply H.
    assumption.
Qed.

Definition I : cexpr := S [+] K [+] K.

Theorem is_normal_I : is_normal I.
Proof.
  unfold is_normal.
  unfold not.
  intros.
  apply steps_Sxy_cases in H.
  destruct H.
  destruct H.
  destruct H.
  inversion H.
  destruct H.
  destruct H.
  inversion H.
Qed.

Theorem steps_star_I : forall c, (I [+] c) ~>* c.
Proof.
  intro.
  unfold I.

  eapply steps_many.
  apply steps_S.

  eapply steps_once.
  apply steps_K.
Qed.

Fixpoint alpha_elim (v : cexpr) (n: nat) : cexpr :=
  match v with
  | var m => if (eqb m n) then I else K [+] var m
  | S => (K [+] S)
  | K => (K [+] K)
  | c1 [+] c2 => S [+] (alpha_elim c1 n) [+] (alpha_elim c2 n)
  end.

Notation "α( n ) * c" := (alpha_elim c n) (at level 30, left associativity).

Theorem steps_star_alpha_elim :
  forall c n, (α(n) * c) [+] var n ~>* c.
Proof.
  intros.
  induction c.
  *
    destruct (PeanoNat.Nat.eq_decidable n n0).
    **
      simpl.
      subst.
      rewrite <- EqNat.beq_nat_refl.
      apply steps_star_I.
    **
      simpl.
      apply PeanoNat.Nat.eqb_neq in H.
      rewrite PeanoNat.Nat.eqb_sym. 
      rewrite H.
      apply steps_once.
      apply steps_K.
  *
    simpl.
    apply steps_once.
    apply steps_K.
  *
    simpl.
    apply steps_once.
    apply steps_K.
  *
    simpl.
    eapply steps_many.
    apply steps_S.

    eapply steps_star_trans.
    apply steps_star_app_l.
    apply IHc1.
    apply steps_star_app_r.
    apply IHc2.
Qed.

Theorem alpha_elim_intros_no_vars : forall c n,
    ~ n IN c -> forall m, ~ n IN α( m ) * c.
Proof.
  intros.
  induction c.
  *
    simpl.
    destruct (n0 =? m).
    **
      rewrite <- not_bcontains_var_contains_var.
      simpl.
      reflexivity.
    **
      rewrite <- not_bcontains_var_contains_var in H.
      simpl in H.
      rewrite <- not_bcontains_var_contains_var.
      simpl.
      assumption.
  *
    simpl.
    rewrite <- not_bcontains_var_contains_var.
    simpl.
    reflexivity.
  *
    rewrite <- not_bcontains_var_contains_var.
    simpl.
    reflexivity.
  *
    simpl.
    rewrite not_contains_var_app_iff.
    rewrite not_contains_var_app_iff in H.
    destruct H.
    apply IHc1 in H. clear IHc1.
    apply IHc2 in H0. clear IHc2.
    split.
    rewrite not_contains_var_app_iff.
    split.
    apply not_bcontains_var_contains_var. auto.
    auto. auto.
Qed.

Theorem alpha_elim_removes_var :    
  forall c n, ~ n IN α(n)*c.
Proof.
  intros.
  rewrite <- not_bcontains_var_contains_var.
  induction c.
  *
    intros.
    destruct (PeanoNat.Nat.eq_decidable n0 n).
    **
      subst.
      simpl.
      rewrite <- EqNat.beq_nat_refl.
      simpl.
      reflexivity.
    **
      apply PeanoNat.Nat.eqb_neq in H.
      simpl. rewrite H. simpl. auto.
  *
    intros.
    auto.
  *
    intros.
    auto.
  *
    intros.
    simpl.
    rewrite Bool.orb_false_iff.
    split.
    apply IHc1.
    apply IHc2.
Qed.

Fixpoint compile_nary_subterm (first_elim : nat) (num_elims : nat) (c : cexpr) :=
  match num_elims with
  | 0 => c
  | Datatypes.S n => alpha_elim (compile_nary_subterm (Datatypes.S first_elim) n c) first_elim
  end.

Lemma compile_nary_subterm_fold :
  forall n m c, alpha_elim (compile_nary_subterm (1+n) m c) n = compile_nary_subterm n (1+m) c.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem compile_nary_subterm_intros_no_vars : forall c x, ~ x IN c -> forall m n, ~ x IN (compile_nary_subterm n m c).
  intros.
  generalize n. clear n.
  induction m.
  *
    intros.
    simpl.
    assumption.
  *
    intros.
    simpl.
    apply alpha_elim_intros_no_vars.
    apply IHm.
Qed.

Theorem compile_nary_subterm_removes_vars : forall c m n k, k < m -> ~ (n + k) IN (compile_nary_subterm n m c).
Proof.
  intros c m.
  induction m.
  *
    intros.
    inversion H.
  *
    intros.
    destruct k.
    **
      assert (n + 0 = n)%nat by lia.
      rewrite H0.
      simpl.
      apply alpha_elim_removes_var.
    **
      simpl.
      apply alpha_elim_intros_no_vars.
      assert (n + Datatypes.S k = (1 + n) + k)%nat by lia.
      rewrite H0.
      apply IHm.
      lia.
Qed.

Theorem steps_star_compile_nary_subterm : forall m n c,
    compile_nary_subterm n (1 + m) c [+] var n ~>* compile_nary_subterm (1 + n) m c.
Proof.
  intros.
  destruct m.
  *
    simpl.
    apply steps_star_alpha_elim.
  *
    intros.
    eapply steps_star_alpha_elim.
Qed.    

(* transforms c to c + v[0] + v[1] + ... + v[n-1] *)
Fixpoint add_vars (c : cexpr) (n : nat) :=
  match n with
  | 0 => c
  | Datatypes.S n' => (add_vars c n') [+] var n'
  end.

Lemma add_vars_fold : forall c n, add_vars c n [+] var n = add_vars c (1+n).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma steps_star_add_vars_compile_nary_subterm :
  forall n m c, add_vars (compile_nary_subterm 0 (1 + n + m) c) (1 + n) ~>* compile_nary_subterm (1 + n) m c.
Proof.
  intros n.
  induction n.
  *
    intros.
    apply steps_star_alpha_elim.
  *
    intros.
    simpl.
    rewrite compile_nary_subterm_fold.
    rewrite compile_nary_subterm_fold.
    eapply steps_star_trans.
    apply steps_star_app_l.
    rewrite add_vars_fold.
    assert (1 + n + (1 + m) = 1 + (1 + (n + m)))%nat by lia.
    rewrite <- H.
    apply IHn.
    apply steps_star_compile_nary_subterm.
Qed.

(* Definition compile_3ary (c : cexpr) := alpha_elim (alpha_elim (alpha_elim c 2) 1) 0. *)
Definition compile_nary (n : nat) (c : cexpr) := compile_nary_subterm 0 n c.

Theorem steps_star_compile_nary : forall n c, add_vars (compile_nary (Datatypes.S n) c) (Datatypes.S n) ~>* c.
Proof.
  intros.
  destruct n.
  *
    simpl.
    apply steps_star_alpha_elim.
  *
    unfold compile_nary.
    eapply steps_star_eq.
    Check steps_star_add_vars_compile_nary_subterm.
    assert (1 + (1 + n) + 0 = Datatypes.S (Datatypes.S n))%nat by lia.
    rewrite <- H at 1.
    apply (steps_star_add_vars_compile_nary_subterm _ 0).
    simpl.
    reflexivity.
Qed.

Theorem compile_nary_intros_no_vars : forall m c n,
    ~ n IN c -> ~ n IN (compile_nary m c).
Proof.
  intros.
  unfold compile_nary.
  apply compile_nary_subterm_intros_no_vars.
  assumption.
Qed.

Theorem compile_nary_removes_vars : forall n m, m < n -> (forall c, ~ m  IN (compile_nary n c)).
Proof.
  intros.
  unfold compile_nary.
  assert (m = 0 + m)%nat by lia.
  rewrite H0.
  apply compile_nary_subterm_removes_vars.
  assumption.
Qed.

Definition fmap_ub (f : fmap) (ub : nat) := forall n, ub <= n -> f n = None.
Definition fmap_1ary (x : cexpr) := (0 <<- x, --).
Definition fmap_2ary (x y : cexpr) := (0 <<- x, 1 <<- y, --).
Definition fmap_3ary (x y z : cexpr) := (0 <<- x, 1 <<- y, 2 <<- z, --).

Lemma fmap_1ary_ub (x : cexpr) : fmap_ub (fmap_1ary x) 1.
Proof.
  unfold fmap_ub.
  intros.
  unfold fmap_1ary.

  destruct n.
  assert (1 = 0)%nat as X by lia.
  inversion X.

  induction n; auto.
Qed.

Lemma fmap_2ary_ub (x y : cexpr) : fmap_ub (fmap_2ary x y) 2.
Proof.
  unfold fmap_ub.
  intros.
  unfold fmap_2ary.

  destruct n.
  assert (1 = 0)%nat as X by lia.
  inversion X.

  destruct n.
  assert (1 = 0)%nat as X by lia.
  inversion X.

  induction n; auto.
Qed.

Lemma fmap_3ary_ub (x y z : cexpr) : fmap_ub (fmap_3ary x y z) 3.
Proof.
  unfold fmap_ub.
  intros.
  unfold fmap_3ary.

  destruct n.
  assert (1 = 0)%nat as X by lia.
  inversion X.

  destruct n.
  assert (1 = 0)%nat as X by lia.
  inversion X.

  destruct n.
  assert (1 = 0)%nat as X by lia.
  inversion X.

  induction n; auto.
Qed.

Lemma compile_nary_disjoint_fmap_lb :
  forall n f, fmap_ub f n -> forall c, disjoint_cexpr_fmap (compile_nary n c) f.
Proof.
  intros.
  unfold disjoint_cexpr_fmap.
  intros.

  assert (n <= n0). {
    assert (n0 < n \/ n <= n0) by lia.
    destruct H1.
    apply compile_nary_removes_vars in H0.
    inversion H0.
    assumption.
    assumption.
  }
  
  apply H.
  assumption.
Qed.

Theorem steps_star_compile_1ary : forall c x, compile_nary 1 c [+] x ~>* (c <-- (fmap_1ary x)).
Proof.
  intros.
  assert ((compile_nary 1 c) [+] x = (add_vars (compile_nary 1 c) 1) <-- (fmap_1ary x)). {
    simpl.
    unfold csubst.
    fold csubst.
    rewrite subst_disjoint. reflexivity.
    apply compile_nary_disjoint_fmap_lb.
    apply fmap_1ary_ub.
  }

  rewrite H.
  apply steps_star_subst.
  apply steps_star_compile_nary.
Qed.

Theorem steps_star_compile_2ary : forall c x y, compile_nary 2 c [+] x [+] y ~>* (c <-- (fmap_2ary x y)).
Proof.
  intros.
  assert ((compile_nary 2 c) [+] x [+] y = (add_vars (compile_nary 2 c) 2) <-- (fmap_2ary x y)). {
    simpl.
    unfold csubst.
    fold csubst.
    rewrite subst_disjoint. reflexivity.
    apply compile_nary_disjoint_fmap_lb.
    apply fmap_2ary_ub.
  }

  rewrite H.
  apply steps_star_subst.
  apply steps_star_compile_nary.  
Qed.

Theorem steps_star_compile_3ary c x y z : (compile_nary 3 c) [+] x [+] y [+] z ~>* (c <-- (fmap_3ary x y z)).
Proof.
  assert (compile_nary 3 c [+] x [+] y [+] z = (add_vars (compile_nary 3 c) 3) <-- (fmap_3ary x y z)). {
    simpl.
    unfold csubst.
    fold csubst.
    rewrite subst_disjoint. reflexivity.
    apply compile_nary_disjoint_fmap_lb.
    apply fmap_3ary_ub.
  }

  rewrite H.
  apply steps_star_subst.
  apply steps_star_compile_nary.
Qed.
  
(* Deriving B M T basis from S K I *)
Definition T : cexpr := S [+] (K [+] (S [+] I)) [+] K.

Theorem is_const_T : is_const T.
Proof.
  unfold T.
  unfold I.
  generalize is_const_S. intros.
  generalize is_const_K. intros.
  rewrite is_const_app_iff.
  rewrite is_const_app_iff.
  rewrite is_const_app_iff.
  rewrite is_const_app_iff. 
  rewrite is_const_app_iff.
  rewrite is_const_app_iff.
  split; auto. split; auto.
Qed.

Theorem steps_star_T : forall x y, (T [+] x [+] y) ~>* (y [+] x).
Proof.
  intros.
  unfold T.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_once.
  apply steps_S.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_once.
  apply steps_K.

  eapply steps_star_trans.
  apply steps_once.
  apply steps_S.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_I.

  apply steps_star_app_r.
  apply steps_once.
  apply steps_K.
Qed.

Definition B : cexpr := S [+] (K [+] S) [+] K.

Theorem is_const_B : is_const B.
Proof.
  unfold B.
  rewrite is_const_app_iff.
  rewrite is_const_app_iff.
  rewrite is_const_app_iff.

  generalize is_const_S. intros.
  generalize is_const_K. intros.

  auto.
Qed.

Theorem steps_star_B : forall x y z, B [+] x [+] y [+] z ~>* x [+] (y [+] z).
Proof.
  intros.
  unfold B.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_once.
  apply steps_S.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_once.
  apply steps_K.

  eapply steps_star_trans.
  apply steps_once.
  apply steps_S.

  apply steps_star_app_l.
  apply steps_once.
  apply steps_K.
Qed.

Definition M : cexpr := S [+] I [+] I.

Theorem steps_star_M : forall x, M [+] x ~>* x [+] x.
Proof.
  intros.
  unfold M.

  eapply steps_star_trans.
  apply steps_once.
  apply steps_S.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_I.

  apply steps_star_app_r.
  apply steps_star_I.
Qed.

(* Some more useful combinators *)
Definition C : cexpr := B [+] (T [+] (B [+] B [+] T)) [+] (B [+] B [+] T).

Theorem is_const_C : is_const C.
Proof.
  unfold C.
  rewrite is_const_app_iff.
  rewrite is_const_app_iff.
  rewrite is_const_app_iff.
  rewrite is_const_app_iff.
  rewrite is_const_app_iff.
  generalize is_const_B. intros.
  generalize is_const_T. intros.
  split; auto.
Qed.
  
Theorem steps_star_C : forall x y z, C [+] x [+] y [+] z ~>* x [+] z [+] y.
Proof.
  intros.
  unfold C.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_star_B.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_star_T.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_star_B.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_B.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_T.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_star_B.

  eapply steps_star_trans.
  apply steps_star_B.

  apply steps_star_T.
Qed.

(* L combinator is useful for recursion *)
Definition L : cexpr := C [+] B [+] M.

Theorem steps_star_L : forall x y, L [+] x [+] y ~>* x [+] (y [+] y).
Proof.
  intros.
  unfold L.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_C.

  eapply steps_star_trans.
  apply steps_star_B.

  apply steps_star_app_r.
  apply steps_star_M.
Qed.

Definition sage c := L [+] c [+] (L [+] c).

Theorem sage_intros_no_vars : forall c n, ~ n IN c -> ~ n IN (sage c).
Proof.
  intros.
  apply not_bcontains_var_contains_var.
  apply not_bcontains_var_contains_var in H.
  simpl.
  rewrite H.
  simpl.
  reflexivity.
Qed.

Theorem steps_star_sage : forall c, sage c ~>* c [+] (sage c).
Proof.
  intros.
  unfold sage.
  apply steps_star_L.
Qed.

Definition V : cexpr := B [+] C [+] T.

Theorem is_const_V : is_const V.
Proof.
  unfold V.
  rewrite is_const_app_iff.
  rewrite is_const_app_iff.
  split.
  split.
  apply is_const_B.
  apply is_const_C.
  apply is_const_T.
Qed.

Theorem steps_star_V : forall x y z, V [+] x [+] y [+] z ~>* z [+] x [+] y.
Proof.
  intros.
  unfold V.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_star_B.

  eapply steps_star_trans.
  apply steps_star_C.

  apply steps_star_app_l.
  apply steps_star_T.
Qed.

(* TRUE and FALSE combinators *)
Definition t : cexpr := K.

Theorem is_normal_t : is_normal t.
Proof.
  unfold is_normal.
  unfold not.
  intros.
  inversion H.
Qed.

Theorem steps_star_t : forall p q, t [+] p [+] q ~>* p.
Proof.
  intros.
  unfold t.
  apply steps_once.
  apply steps_K.
Qed.

Theorem is_const_t : is_const t.
Proof.
  unfold is_const.
  intros.
  apply not_bcontains_var_contains_var.
  simpl. auto.
Qed.

Definition f : cexpr := K [+] I.

Theorem is_normal_f : is_normal f.
Proof.
  unfold is_normal.
  unfold not.
  intros.
  inversion H; subst.
  inversion H3.
  apply is_normal_I in H3. auto.
Qed.

Theorem is_const_f : is_const f.
Proof.
  unfold is_const.
  intros.
  apply not_bcontains_var_contains_var.
  simpl. auto.
Qed.

Theorem steps_star_f : forall p q, f [+] p [+] q ~>* q.
Proof.
  intros.
  unfold f.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_once.
  apply steps_K.

  apply steps_star_I.
Qed.

(* Modeling the non-negative integers *)

Definition nxt : cexpr := V [+] f.
Definition prv : cexpr := T [+] f.
Definition zro : cexpr := I.

Fixpoint rep (n: nat) :=
  match n with
  | 0 => zro
  | Datatypes.S m => nxt [+] (rep m)
  end.

Theorem is_const_prv : is_const prv.
Proof.
  unfold is_const.
  intros.
  apply not_bcontains_var_contains_var.
  simpl. reflexivity.
Qed.

Theorem is_const_nxt : is_const nxt.
Proof.
  unfold is_const.
  intros.
  apply not_bcontains_var_contains_var.
  simpl. reflexivity.
Qed.

Theorem is_const_zro : is_const zro.
Proof.
  unfold is_const.
  intros.
  apply not_bcontains_var_contains_var.
  simpl. reflexivity.
Qed.

Theorem is_const_rep_n : forall n, is_const (rep n).
Proof.
  intros.
  induction n.
  *
    unfold is_const.
    intros.
    apply not_bcontains_var_contains_var.
    simpl. auto.
  *
    unfold is_const.
    intros.
    apply not_bcontains_var_contains_var.
    simpl. auto.
    apply not_bcontains_var_contains_var.
    apply IHn.
Qed.
  
Theorem steps_star_prv_nxt : forall n, prv [+] (rep (1 + n)) ~>* rep n.
Proof.
  intros.
  simpl.
  unfold prv.
  eapply steps_star_trans.
  apply steps_star_T.
  unfold nxt.
  eapply steps_star_trans.
  apply steps_star_V.
  apply steps_star_f.
Qed.

Definition eq_zro : cexpr := T [+] t.

Theorem is_const_eq_zro : is_const eq_zro.
Proof.
  unfold is_const.
  intros.
  rewrite <- not_bcontains_var_contains_var.
  auto.
Qed.

Theorem steps_star_eq_zro_Sn : forall n, eq_zro [+] rep (Datatypes.S n) ~>* f.
Proof.
  intros.
  unfold eq_zro.
  eapply steps_star_trans.
  apply steps_star_T.
  simpl.
  unfold nxt.
  eapply steps_star_trans.
  apply steps_star_V.
  apply steps_star_t.
Qed.

Theorem steps_star_eq_zro_0 : eq_zro [+] rep 0 ~>* t.
Proof.
  intros.
  unfold eq_zro.
  eapply steps_star_trans.
  apply steps_star_T.
  apply steps_star_I.
Qed.

Definition add_m_n_action := eq_zro [+] var 1 [+] var 2 [+] (nxt [+] (var 0 [+] (prv [+] var 1) [+] var 2)).
Definition add_m_n_preop := compile_nary 3 add_m_n_action.
Definition add_m_n_op := sage add_m_n_preop.

Theorem is_const_add_m_n_op : is_const add_m_n_op.
Proof.
  unfold is_const.
  intros.
  unfold add_m_n_op.
  unfold add_m_n_preop.
  apply sage_intros_no_vars.
  assert (n < 3 \/ 3 <= n) as cases by lia.
  destruct cases.
  *
    apply compile_nary_removes_vars.
    auto.
  *
    apply compile_nary_intros_no_vars.
    apply not_bcontains_var_contains_var.
    destruct n. assert (1 = 0)%nat as X by lia. inversion X.
    destruct n. assert (1 = 0)%nat as X by lia. inversion X.
    destruct n. assert (1 = 0)%nat as X by lia. inversion X.
    simpl. reflexivity.
Qed.

Lemma steps_star_add_m_n_op : forall x y, add_m_n_op [+] x [+] y ~>* eq_zro [+] x [+] y [+] (nxt [+] (add_m_n_op [+] (prv [+] x) [+] y)).
Proof.
  intros.
  unfold add_m_n_op.
  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_star_sage.
  unfold add_m_n_preop.
  eapply steps_star_trans.
  apply steps_star_compile_3ary.
  unfold add_m_n_action at 1.
  Opaque eq_zro.
  Opaque nxt.
  Opaque prv.
  simpl.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  apply steps_none.
  apply is_const_prv.
  apply is_const_nxt.
  apply is_const_eq_zro.
Qed.

Theorem add_m_n_spec : forall x y, add_m_n_op [+] rep x [+] rep y ~>* rep (x + y).
Proof.
  intro x.
  induction x.
  *
    intros.
    eapply steps_star_trans.
    apply steps_star_add_m_n_op.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_l.
    apply steps_star_eq_zro_0.
    eapply steps_star_trans.
    eapply steps_star_t.
    simpl.
    apply steps_none.
  *
    intros.
    eapply steps_star_trans.
    apply steps_star_add_m_n_op.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_l.
    apply steps_star_eq_zro_Sn.
    eapply steps_star_trans.
    apply steps_star_f.
    simpl.
    apply steps_star_app_r.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_r.
    apply steps_star_prv_nxt.
    apply IHx.
Qed.
  
Definition mul_m_n_action := eq_zro [+] var 1 [+] zro [+] (add_m_n_op [+] (var 0 [+] (prv [+] var 1) [+] var 2) [+] var 2).
Definition mul_m_n_preop := compile_nary 3 mul_m_n_action.
Definition mul_m_n_op := sage mul_m_n_preop.

Theorem is_const_mul_m_n_op : is_const mul_m_n_op.
  unfold is_const.
  intros.
  unfold add_m_n_op.
  unfold add_m_n_preop.
  apply sage_intros_no_vars.
  assert (n < 3 \/ 3 <= n) as cases by lia.
  destruct cases.
  *
    apply compile_nary_removes_vars.
    auto.
  *
    apply compile_nary_intros_no_vars.
    apply not_bcontains_var_contains_var.
    destruct n. assert (1 = 0)%nat as X by lia. inversion X.
    destruct n. assert (1 = 0)%nat as X by lia. inversion X.
    destruct n. assert (1 = 0)%nat as X by lia. inversion X.
    simpl. reflexivity.
Qed.

Theorem steps_star_mul_m_n_op : forall x y, mul_m_n_op [+] x [+] y ~>* eq_zro [+] x [+] zro [+] (add_m_n_op [+] (mul_m_n_op [+] (prv [+] x) [+] y) [+] y).
Proof.
  intros.
  unfold mul_m_n_op.
  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_star_sage.
  unfold mul_m_n_preop.
  
  eapply steps_star_trans.
  apply steps_star_compile_3ary.

  unfold mul_m_n_action.

  Opaque eq_zro.
  Opaque nxt.
  Opaque prv.
  Opaque add_m_n_op.
  Opaque sage.
  Opaque zro.

  simpl.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  apply steps_none.
  apply is_const_prv.
  apply is_const_add_m_n_op.
  apply is_const_zro.
  apply is_const_eq_zro.
Qed.

Theorem mul_m_n_spec : forall x y, mul_m_n_op [+] rep x [+] rep y ~>* rep (x*y).
Proof.
  intro x.
  induction x.
  *
    intros.
    eapply steps_star_trans.
    apply steps_star_mul_m_n_op.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_l.
    apply steps_star_eq_zro_0.
    eapply steps_star_trans.
    eapply steps_star_t.
    simpl.
    apply steps_none.
  *
    intros.
    eapply steps_star_trans.
    apply steps_star_mul_m_n_op.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_l.
    apply steps_star_eq_zro_Sn.
    eapply steps_star_trans.
    apply steps_star_f.
    simpl.

    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_r.

    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_r.
    apply steps_star_prv_nxt.
    
    apply IHx.
    eapply steps_star_trans.
    apply add_m_n_spec.

    assert (x  * y + y = y + x * y) by lia.
    rewrite H.
    apply steps_none.
Qed.

Definition pow_m_n_action := eq_zro [+] var 2 [+] rep 1 [+] (mul_m_n_op [+] (var 0 [+] var 1 [+] (prv [+] var 2)) [+] var 1).
Definition pow_m_n_preop := compile_nary 3 pow_m_n_action.
Definition pow_m_n_op := sage pow_m_n_preop.

Theorem is_const_pow_m_n_op : is_const pow_m_n_op.
  unfold is_const.
  intros.
  unfold pow_m_n_op.
  unfold mul_m_n_preop.
  apply sage_intros_no_vars.
  assert (n < 3 \/ 3 <= n) as cases by lia.
  destruct cases.
  *
    apply compile_nary_removes_vars.
    auto.
  *
    apply compile_nary_intros_no_vars.
    apply not_bcontains_var_contains_var.
    destruct n. assert (1 = 0)%nat as X by lia. inversion X.
    destruct n. assert (1 = 0)%nat as X by lia. inversion X.
    destruct n. assert (1 = 0)%nat as X by lia. inversion X.
    simpl. reflexivity.
Qed.

Theorem steps_star_pow_m_n_op : forall x y,
    pow_m_n_op [+] x [+] y ~>* eq_zro [+] y [+] rep 1 [+] (mul_m_n_op [+] (pow_m_n_op [+] x [+] (prv [+] y)) [+] x).
Proof.
  intros.
  unfold pow_m_n_op.
  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_star_sage.
  unfold pow_m_n_preop.
  
  eapply steps_star_trans.
  apply steps_star_compile_3ary.

  unfold pow_m_n_action.

  Opaque eq_zro.
  Opaque nxt.
  Opaque prv.
  Opaque mul_m_n_op.
  Opaque sage.
  Opaque zro.

  simpl.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  apply steps_none.
  apply is_const_mul_m_n_op.
  apply is_const_zro.
  apply is_const_nxt.
  apply is_const_eq_zro.
Qed.

Theorem pow_m_n_spec : forall x y, pow_m_n_op [+] rep x [+] rep y ~>* rep (x ^ y).
Proof.
  intros.
  generalize x. clear x.
  induction y.
  *
    intros.
    eapply steps_star_trans.
    apply steps_star_pow_m_n_op.
    eapply steps_star_trans.
    eapply steps_star_app_l.
    eapply steps_star_app_l.
    apply steps_star_eq_zro_0.
    eapply steps_star_trans.
    apply steps_star_t.
    simpl.
    apply steps_none.
  *
    intros.
    eapply steps_star_trans.
    apply steps_star_pow_m_n_op.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_l.
    apply steps_star_eq_zro_Sn.
    eapply steps_star_trans.
    apply steps_star_f.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_r.
    apply steps_star_app_r.
    apply steps_star_prv_nxt.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_r.
    apply IHy.
    eapply steps_star_trans.
    apply mul_m_n_spec.
    simpl.
    rewrite PeanoNat.Nat.mul_comm.
    apply steps_none.
Qed.

Definition gt_m_n_action := eq_zro [+] var 1 [+] f [+] (eq_zro [+] var 2 [+] t [+] (var 0 [+] (prv [+] var 1) [+] (prv [+] var 2))).
Definition gt_m_n_preop := compile_nary 3 gt_m_n_action.
Definition gt_m_n_op := sage gt_m_n_preop.

Theorem is_const_gt_m_n_op : is_const gt_m_n_op.
  unfold is_const.
  intros.
  unfold gt_m_n_op.
  unfold gt_m_n_preop.
  apply sage_intros_no_vars.
  assert (n < 3 \/ 3 <= n) as cases by lia.
  destruct cases.
  *
    apply compile_nary_removes_vars.
    auto.
  *
    apply compile_nary_intros_no_vars.
    apply not_bcontains_var_contains_var.
    destruct n. assert (1 = 0)%nat as X by lia. inversion X.
    destruct n. assert (1 = 0)%nat as X by lia. inversion X.
    destruct n. assert (1 = 0)%nat as X by lia. inversion X.
    simpl. reflexivity.
Qed.

Theorem steps_star_gt_m_n_op : forall x y,
    gt_m_n_op [+] x [+] y ~>* eq_zro [+] x [+] f [+] (eq_zro [+] y [+] t [+] (gt_m_n_op [+] (prv [+] x) [+] (prv [+] y))).
Proof.
  intros.
  unfold gt_m_n_op.
  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_star_sage.
  unfold gt_m_n_preop.
  
  eapply steps_star_trans.
  apply steps_star_compile_3ary.

  unfold gt_m_n_action.

  Opaque eq_zro.
  Opaque nxt.
  Opaque prv.
  Opaque sage.
  Opaque compile_nary.
  Opaque zro.
  Opaque t.
  Opaque f.
  
  simpl.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  apply steps_none.

  apply is_const_t.
  apply is_const_f.
  apply is_const_eq_zro.
Qed.

Theorem gt_m_n_spec1 : forall m n, m > n -> gt_m_n_op [+] rep m [+] rep n ~>* t.
Proof.
  intro m.
  induction m.
  *
    intros.
    inversion H.
  *
    intros.
    eapply steps_star_trans.
    apply steps_star_gt_m_n_op.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_l.
    apply steps_star_eq_zro_Sn.
    eapply steps_star_trans.
    apply steps_star_f.
    destruct n.
    **
      eapply steps_star_trans.
      apply steps_star_app_l.
      apply steps_star_app_l.
      apply steps_star_eq_zro_0.
      apply steps_star_t.
    **
      eapply steps_star_trans.
      apply steps_star_app_r.
      apply steps_star_app_r.
      apply steps_star_prv_nxt.
      eapply steps_star_trans.
      apply steps_star_app_r.
      apply steps_star_app_l.
      apply steps_star_app_r.
      apply steps_star_prv_nxt.
      eapply steps_star_trans.
      apply steps_star_app_r.
      apply IHm.
      lia.
      eapply steps_star_trans.
      apply steps_star_app_l.
      apply steps_star_app_l.
      apply steps_star_eq_zro_Sn.
      apply steps_star_f.
Qed.

Theorem gt_m_n_spec2 : forall m n, m <= n -> gt_m_n_op [+] rep m [+] rep n ~>* f.
Proof.
  intro m.
  induction m.
  *
    intros.
    eapply steps_star_trans.
    apply steps_star_gt_m_n_op.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_l.
    apply steps_star_eq_zro_0.
    apply steps_star_t.
  *
    intros.
    eapply steps_star_trans.
    apply steps_star_gt_m_n_op.
    destruct n.
    **
      assert (1 = 0) as contra by lia.
      inversion contra.
    **
      eapply steps_star_trans.
      apply steps_star_app_l.
      apply steps_star_app_l.
      apply steps_star_eq_zro_Sn.
      eapply steps_star_trans.
      apply steps_star_f.
      eapply steps_star_trans.
      eapply steps_star_app_l.
      eapply steps_star_app_l.
      apply steps_star_eq_zro_Sn.
      eapply steps_star_trans.
      apply steps_star_f.
      eapply steps_star_trans.
      apply steps_star_app_l.
      apply steps_star_app_r.
      apply steps_star_prv_nxt.
      eapply steps_star_trans.
      apply steps_star_app_r.
      apply steps_star_prv_nxt.
      apply IHm.
      lia.
Qed.

Theorem gt_m_n_spec1rev : forall m n, gt_m_n_op [+] rep m [+] rep n ~>* t -> m > n.
Proof.
  intros.
  assert (m > n \/ m <= n) as cases by lia.
  destruct cases.
  auto.
  apply gt_m_n_spec2 in H0.
  assert (t = f). {
    eapply unique_normal_form.
    apply H. apply H0.
    apply is_normal_t.
    apply is_normal_f.
  }
  inversion H1.
Qed.

Theorem gt_m_n_spec2rev : forall m n, gt_m_n_op [+] rep m [+] rep n ~>* f -> m <= n.
Proof.
  intros.
  assert (m > n \/ m <= n) as cases by lia.
  destruct cases.
  auto.
  apply gt_m_n_spec1 in H0.
  assert (t = f). {
    eapply unique_normal_form.
    apply H0. apply H.
    apply is_normal_t.
    apply is_normal_f.
  }
  inversion H1.
  auto.
Qed.

Definition eq_m_n_action := gt_m_n_op [+] var 0 [+] var 1 [+] f [+] (gt_m_n_op [+] var 1 [+] var 0 [+] f [+] t).
Definition eq_m_n_op := compile_nary 2 eq_m_n_action.

Theorem is_const_eq_m_n_op : is_const eq_m_n_op.
Proof.
  unfold is_const.
  intros.
  unfold eq_m_n_op.

  assert (n < 2 \/ 2 <= n) as contra by lia.
  destruct contra.

  *
    apply compile_nary_removes_vars.
    auto.
  *
    apply compile_nary_intros_no_vars.
    unfold eq_m_n_action.
    Opaque gt_m_n_op.
    apply not_bcontains_var_contains_var.
    unfold bcontains_var. fold bcontains_var.
    destruct n. assert (1 = 0) as contra by lia. inversion contra.
    destruct n. assert (1 = 0) as contra by lia. inversion contra.
    simpl.

    assert (is_bconst gt_m_n_op). {
      apply is_bconst_is_const.
      apply is_const_gt_m_n_op.
    }
    rewrite H0. clear H0.

    Transparent f. Transparent t.
    simpl. auto.
Qed.

Theorem steps_star_eq_m_n_op : forall m n, eq_m_n_op [+] m [+] n ~>* gt_m_n_op [+] m [+] n [+] f [+] (gt_m_n_op [+] n [+] m [+] f [+] t).
Proof.
  intros.
  eapply steps_star_trans.
  unfold eq_m_n_op.
  apply steps_star_compile_2ary.
  unfold eq_m_n_action.
  rewrite subst_app_distr.
  rewrite subst_app_distr.
  rewrite subst_app_distr.
  rewrite subst_app_distr.
  Opaque gt_m_n_op. Opaque t. Opaque f.
  simpl.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  apply steps_none.
  apply is_const_t.
  apply is_const_f.
  apply is_const_gt_m_n_op.
Qed.

Theorem eq_m_n_spec1 : forall m, eq_m_n_op [+] rep m [+] rep m ~>* t.
Proof.
  intros.
  eapply steps_star_trans.
  apply steps_star_eq_m_n_op.
  eapply steps_star_trans.
  eapply steps_star_app_l.
  eapply steps_star_app_l.
  apply gt_m_n_spec2. auto.
  eapply steps_star_trans.
  apply steps_star_f.
  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply gt_m_n_spec2. auto.
  apply steps_star_f.
Qed.

Theorem eq_m_n_spec2 : forall m n, m <> n -> eq_m_n_op [+] rep m [+] rep n ~>* f.
Proof.
  intros.
  assert ((m < n) \/ (n < m)) by lia.
  destruct H0.
  *
    eapply steps_star_trans.
    apply steps_star_eq_m_n_op.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_l.
    apply gt_m_n_spec2. lia.
    eapply steps_star_trans.
    apply steps_star_f.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_l.
    apply gt_m_n_spec1. auto.
    apply steps_star_t.
  *
    eapply steps_star_trans.
    apply steps_star_eq_m_n_op.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_l.
    apply gt_m_n_spec1. lia.
    eapply steps_star_trans.
    apply steps_star_t.
    apply steps_none.
Qed.

(* under this definition, length of 0 is indeterminate *)
Definition nat_has_length m len := (m = 0 /\ len = 1) \/ (m <> 0 /\ 10^(pred len) <= m < 10^len).

Lemma pow_gt_0 : forall m n, m <> 0 -> 0 < m^n.
Proof.
  intros.
  assert (m^n <> 0).
  apply PeanoNat.Nat.pow_nonzero. auto.
  lia.
Qed.
  
Theorem has_unique_nat_length m n1 n2 : (nat_has_length m n1) /\ (nat_has_length m n2) -> n1 = n2.
Proof.
  intros.
  destruct H.

  unfold nat_has_length in H0.
  unfold nat_has_length in H.

  destruct H; destruct H0.

  *
    destruct H. subst.
    destruct H0. subst. auto.
  *
    destruct H. subst.
    destruct H0. exfalso. apply H. auto.
  *
    destruct H0. subst.
    destruct H. exfalso. apply H. auto.
  *
    destruct H.
    destruct H0.
    
    assert (10^(pred n2) < 10^n1). {
      eapply PeanoNat.Nat.le_lt_trans.
      destruct H2.
      apply l.
      destruct H1.
      apply H3.
    }
    rewrite <- PeanoNat.Nat.pow_lt_mono_r_iff in H3.

    assert (10^(pred n1) < 10^n2). {
      eapply PeanoNat.Nat.le_lt_trans.
      destruct H1.
      apply l.
      destruct H2.
      apply H4.
    }
    rewrite <- PeanoNat.Nat.pow_lt_mono_r_iff in H4.
    lia. lia. lia.
Qed.

Fixpoint nat_length n :=
  match n with
  | 0 => 1
  | Datatypes.S n' =>
    let predlen := nat_length n' in
    if Datatypes.S n' =? 10^predlen then Datatypes.S predlen else predlen
  end.

(* Compute (nat_length 1). = 1 *)
(* Compute (nat_length 12). = 2 *)
(* Compute (nat_length 123). = 3 *)

Lemma nat_length_neq_0 : forall n, nat_length n <> 0.
Proof.
  induction n. simpl. lia.
  unfold nat_length. fold nat_length.
  destruct (Datatypes.S n =? 10^(nat_length n)). lia. auto.
Qed.

Theorem nat_length_spec : forall m, nat_has_length m (nat_length m).
Proof.
  intros.
  induction m.
  *
    unfold nat_has_length.
    left. auto.
  *
    unfold nat_has_length.
    right.
    unfold nat_has_length in IHm.
    destruct IHm.
    **
      destruct H. subst.
      split. auto.
      simpl. lia.
    **
      assert (0 = 0) as H0 by lia.
      assert (Datatypes.S m = 10^(nat_length m) \/ Datatypes.S m <> 10^(nat_length m)) by lia.
      destruct H1.
      ***
        unfold nat_length. fold nat_length. rewrite H1.
        rewrite <- EqNat.beq_nat_refl.
        rewrite <- pred_Sn.
        split.
        apply PeanoNat.Nat.pow_nonzero. auto.
        split.
        apply PeanoNat.Nat.pow_le_mono_r. auto. auto.
        apply PeanoNat.Nat.pow_lt_mono_r. lia. lia.
      ***
        split. lia.
        unfold nat_length. fold nat_length.
        rewrite <- PeanoNat.Nat.eqb_neq in H1.
        rewrite H1. auto.
        split. lia.
        rewrite PeanoNat.Nat.eqb_neq in H1.
        lia.
Qed.

Theorem nat_length_div10 : forall n, 10 <= n -> 1 + nat_length(n / 10) = nat_length n.
Proof.
  intros.
  apply (has_unique_nat_length n).
  split.
  *
    unfold nat_has_length.
    right.

    generalize (nat_length_spec (n/10)). intros.
    unfold nat_has_length in H0.
    destruct H0. destruct H0.
    rewrite PeanoNat.Nat.div_small_iff in H0.
    assert (1 = 0) as contra by lia. inversion contra. lia.

    destruct H0.
    destruct H1.

    split; try lia.
    split.

    assert (10 ^ pred (1 + nat_length (n / 10)) = 10*10^(pred (nat_length (n / 10)))). {
      rewrite (PeanoNat.Nat.add_1_l (nat_length (n/10))).
      rewrite <- pred_Sn.
      rewrite <- PeanoNat.Nat.pow_succ_r; try lia.
      rewrite PeanoNat.Nat.succ_pred. auto.
      apply nat_length_neq_0.
    }
    rewrite H3. clear H3.

    intros.
    eapply (PeanoNat.Nat.mul_le_mono_nonneg_l _ _ 10) in H1.
    eapply PeanoNat.Nat.le_trans.
    apply H1.

    assert (n = (n * 10)/10). {
      rewrite PeanoNat.Nat.div_mul. auto.
      lia.
    }
    rewrite H3 at 2.
    clear H3.

    rewrite <- (PeanoNat.Nat.mul_comm 10 n).
    apply PeanoNat.Nat.div_mul_le. lia. lia.

    rewrite (PeanoNat.Nat.div_mod n 10) at 1; try lia.
    rewrite (PeanoNat.Nat.add_1_l (nat_length (n/10))).
    rewrite PeanoNat.Nat.pow_succ_r; try lia.

    assert (n mod 10 < 10). {
      apply PeanoNat.Nat.mod_upper_bound. lia.
    }

    lia.
  *
    apply nat_length_spec.
Qed.

Theorem nat_length_apow10 : forall n a, a <> 0 -> nat_length(a * 10^n) = nat_length a + n.
Proof.
  intros.
  generalize (nat_length_spec a). intros.
  unfold nat_has_length in H0.
  destruct H0. destruct H0. subst. exfalso. apply H. auto.
  destruct H0.
  assert (nat_has_length (a*10^n) (nat_length a + n)). {
    unfold nat_has_length.
    right.
    split.
    apply PeanoNat.Nat.neq_mul_0.
    split. auto. apply PeanoNat.Nat.pow_nonzero.
    auto.

    assert (pred(nat_length a + n) = pred(nat_length a) + n). {
      assert (nat_length a <> 0).
      apply nat_length_neq_0.
      destruct (nat_length a).
      exfalso. apply H2. auto.
      lia.
    }
    rewrite H2.
    rewrite PeanoNat.Nat.pow_add_r.
    split.
    apply Mult.mult_le_compat_r.
    destruct H1. auto.
    destruct H1.
    rewrite PeanoNat.Nat.pow_add_r.
    apply Mult.mult_lt_compat_r. auto. 
    apply pow_gt_0. lia.
  }

  generalize (nat_length_spec (a*10^n)). intros.
  eapply has_unique_nat_length.
  assert (a*10^n <> 0). {
    apply PeanoNat.Nat.neq_mul_0.
    split. auto.
    apply PeanoNat.Nat.pow_nonzero. lia.
  }
  split. apply H3. auto.
Qed.

(* Fixpoint nat_length n := *)
(*   match n with *)
(*   | 0 => 0 *)
(*   | Datatypes.S n' => *)
(*     let predlen := nat_length n' in *)
(*     if Datatypes.S n' =? 10^predlen then Datatypes.S predlen else predlen *)
(*   end. *)

Definition predlen := (var 0 [+] (prv [+] var 1)).
Definition nat_length_action := eq_zro [+] var 1 [+] rep 1 [+] (eq_m_n_op [+] var 1 [+] (pow_m_n_op [+] rep 10 [+] predlen) [+] (nxt [+] predlen) [+] predlen).
Definition nat_length_preop := compile_nary 2 nat_length_action.
Definition nat_length_op := sage nat_length_preop.

Theorem is_const_nat_length_op : is_const nat_length_op.
Proof.
  unfold is_const.
  intros.
  unfold nat_length_op.
  apply sage_intros_no_vars.
  unfold nat_length_preop.

  assert (n < 2 \/ 2 <= n) as cases by lia.
  destruct cases.

  apply compile_nary_removes_vars. auto.

  destruct n. assert (1 = 0) as contra by lia. inversion contra.
  destruct n. assert (1 = 0) as contra by lia. inversion contra.

  apply compile_nary_intros_no_vars. unfold nat_length_action.


  Opaque eq_zro.
  Opaque eq_m_n_op.
  Opaque pow_m_n_op.
  Opaque predlen.
  Opaque nxt.
  Opaque rep.

  apply not_bcontains_var_contains_var.
  simpl.

  assert (is_bconst eq_zro). {
    apply is_bconst_is_const.
    apply is_const_eq_zro.
  }

  rewrite H0. clear H0.

  assert (forall n', is_bconst (rep n')). {
    intros.
    apply is_bconst_is_const.
    apply is_const_rep_n.
  }

  rewrite H0. clear H0.

  assert (is_bconst nxt). {
    apply is_bconst_is_const.
    apply is_const_nxt.
  }

  rewrite H0. clear H0.

  assert (is_bconst pow_m_n_op). {
    apply is_bconst_is_const.
    apply is_const_pow_m_n_op.
  }

  rewrite H0. clear H0.

  simpl.

  assert (is_bconst eq_m_n_op). {
    apply is_bconst_is_const.
    apply is_const_eq_m_n_op.
  }

  rewrite H0. clear H0.

  assert (is_bconst (rep 10)). {
    apply is_bconst_is_const.
    apply is_const_rep_n.
  }

  rewrite H0. clear H0.

  simpl.

  Transparent predlen.
  unfold predlen.
  simpl.

  Transparent prv. Transparent f. simpl. auto.
Qed.

Theorem steps_star_nat_length_op : forall n,
    nat_length_op [+] n ~>*
                  let pl := (nat_length_op [+] (prv [+] n)) in
                  eq_zro [+] n [+] rep 1 [+] (eq_m_n_op [+] n [+] (pow_m_n_op [+] rep 10 [+] pl) [+] (nxt [+] pl) [+] pl).
Proof.
  intros.
  simpl.

  eapply steps_star_trans.
  unfold nat_length_op.
  apply steps_star_app_l.
  apply steps_star_sage.
  unfold nat_length_preop.
  eapply steps_star_trans.
  apply steps_star_compile_2ary.
  fold nat_length_op.
  assert (sage (compile_nary 2 nat_length_action) = nat_length_op) as foldit. {
    unfold nat_length_op.
    unfold nat_length_preop. reflexivity.
  }
  rewrite foldit. clear foldit.

  unfold nat_length_action.
  unfold predlen.
  Opaque eq_zro.
  Opaque eq_m_n_op.
  Opaque pow_m_n_op.
  Opaque rep.
  Opaque nxt.
  Opaque prv.
  Opaque nat_length_op.

  simpl.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  apply steps_none.

  apply is_const_nxt.
  apply is_const_prv.
  apply is_const_rep_n.
  apply is_const_pow_m_n_op.
  apply is_const_eq_m_n_op.
  apply is_const_rep_n.
  apply is_const_eq_zro.
Qed.

Theorem nat_length_op_spec : forall n, nat_length_op [+] rep n ~>* rep (nat_length n).
Proof.
  intros.
  induction n.
  *
    eapply steps_star_trans.
    apply steps_star_nat_length_op. simpl.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_l.
    apply steps_star_eq_zro_0.
    apply steps_star_t.
  *
    eapply steps_star_trans.
    apply steps_star_nat_length_op.
    Opaque nat_length.
    simpl.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_l.
    apply steps_star_eq_zro_Sn.
    eapply steps_star_trans.
    apply steps_star_f.
    eapply steps_star_trans.
    apply steps_star_app_r.
    apply steps_star_app_r.
    apply steps_star_prv_nxt.

    eapply steps_star_trans.
    apply steps_star_app_r.
    apply IHn.

    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_r.
    apply steps_star_app_r.
    apply steps_star_app_r.
    apply steps_star_prv_nxt.

    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_r.
    apply steps_star_app_r.
    apply IHn.

    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_l.
    apply steps_star_app_r.
    apply steps_star_app_r.
    apply steps_star_app_r.
    apply steps_star_prv_nxt.

    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_l.
    apply steps_star_app_r.
    apply steps_star_app_r.
    apply IHn.

    eapply steps_star_trans.
    eapply steps_star_app_l.
    eapply steps_star_app_l.
    eapply steps_star_app_r.
    
    apply pow_m_n_spec.

    destruct (PeanoNat.Nat.eq_decidable (Datatypes.S n) (10^(nat_length n))).
    **
      Transparent nat_length.
      unfold nat_length. fold nat_length.
      assert (Datatypes.S n =? 10 ^ nat_length n = true). {
        apply PeanoNat.Nat.eqb_eq. auto.
      }
      rewrite H0.
      rewrite H.
      eapply steps_star_trans.
      apply steps_star_app_l.
      apply steps_star_app_l.
      apply eq_m_n_spec1.
      apply steps_star_t.
    **
      Transparent nat_length.
      unfold nat_length. fold nat_length.
      assert (Datatypes.S n =? 10 ^ nat_length n = false). {
        apply PeanoNat.Nat.eqb_neq. auto.
      }
      rewrite H0.

      eapply steps_star_trans.
      apply steps_star_app_l.
      apply steps_star_app_l.
      apply eq_m_n_spec2. auto.
      apply steps_star_f.
Qed.

(* little-endian concat *)
Definition concat10 a b : nat := a + b*10^(nat_length a).

Theorem nat_has_length_concat10 : forall n1 n2, n2 <> 0 -> nat_has_length (concat10 n1 n2) ((nat_length n1) + (nat_length n2)).
Proof.
  intros.
  unfold nat_has_length.
  right.
  split.
  unfold concat10.
  unfold not. intros.
  intros.
  apply Plus.plus_is_O in H0.
  destruct H0.
  rewrite PeanoNat.Nat.eq_mul_0 in H1.
  destruct H1. contradiction.
  generalize (PeanoNat.Nat.pow_nonzero 10 (nat_length n1)). intros.
  apply H2. lia. auto.

  generalize (nat_length_spec n1). intros.
  generalize (nat_length_spec n2). intros.
  unfold nat_has_length in H0.
  unfold nat_has_length in H1.
  unfold concat10.

  destruct H0. destruct H0. subst.
  destruct H1. destruct H0. contradiction.
  destruct H0. rewrite H2.

  assert (nat_length n2 <> 0). {
    apply nat_length_neq_0.
  }

  assert (pred(1 + nat_length n2) = pred(nat_length n2) + 1). {
    lia.
  }
  rewrite H4.
  rewrite PeanoNat.Nat.pow_add_r.
  rewrite PeanoNat.Nat.pow_add_r.

  rewrite PeanoNat.Nat.pow_1_r.
  rewrite plus_O_n.
  split.
  apply Mult.mult_le_compat_r. apply H1.
  rewrite PeanoNat.Nat.mul_comm.
  apply Mult.mult_lt_compat_l. apply H1. lia.

  destruct H1. destruct H1. subst. contradiction.

  destruct H0. destruct H1.

  split.
  assert (pred(nat_length n1 + nat_length n2) = pred(nat_length n2) + nat_length n1). {
    assert (nat_length n2 <> 0) by apply nat_length_neq_0.
    lia.
  }
  rewrite H4.
  rewrite PeanoNat.Nat.pow_add_r.
  assert (10 ^ pred (nat_length n2) * 10 ^ nat_length n1 <= n2 * 10 ^ nat_length n1). {
    apply Mult.mult_le_compat_r. apply H3.
  }

  eapply PeanoNat.Nat.le_trans.
  apply H5.
  rewrite <- plus_O_n at 1.
  apply PeanoNat.Nat.add_le_mono_r. lia.

  eapply PeanoNat.Nat.lt_le_trans.
  apply PeanoNat.Nat.add_lt_mono_r. apply H2.

  rewrite PeanoNat.Nat.pow_add_r.
  assert (10^nat_length n1 + n2 * 10 ^ nat_length n1 = (10^(nat_length n1) * (1 + n2))). {
    rewrite PeanoNat.Nat.mul_add_distr_l.
    rewrite PeanoNat.Nat.mul_1_r. lia.
  }
  rewrite H4.
  apply PeanoNat.Nat.mul_le_mono_pos_l. lia.
  lia.
Qed.

Theorem nat_length_concat10 : forall n1 n2, n2 <> 0 -> nat_length (concat10 n1 n2) = (nat_length n1) + (nat_length n2).
Proof.
  intros.
  generalize (nat_has_length_concat10 n1 n2 H). intros.
  eapply has_unique_nat_length.
  split.
  apply nat_length_spec.
  auto.
Qed.

(* Compute (concat10 12 3). *)
(* Compute (concat10 12 13). *)

Definition concat10_action := add_m_n_op [+] var 0 [+] (mul_m_n_op [+] var 1 [+] (pow_m_n_op [+] rep 10 [+] (nat_length_op [+] var 0 ))).
Definition concat10_op := compile_nary 2 concat10_action.

Theorem is_const_concat10_op : is_const concat10_op.
Proof.
  unfold is_const.
  unfold concat10_op.
  intros.

  assert (n < 2 \/ 2 <= n) by lia.
  destruct H.
  *
    apply compile_nary_removes_vars.
    auto.
  *
    apply compile_nary_intros_no_vars.
    unfold concat10_action.
    apply not_bcontains_var_contains_var.
    Opaque add_m_n_op.
    Opaque pow_m_n_op.
    Opaque rep.
    Opaque nat_length_op.
    destruct n. assert (1 = 0) as contra by lia. inversion contra.
    destruct n. assert (1 = 0) as contra by lia. inversion contra.
    simpl.
    assert (is_bconst add_m_n_op). apply is_bconst_is_const. apply is_const_add_m_n_op.
    rewrite H0. clear H0.
    assert (is_bconst pow_m_n_op). apply is_bconst_is_const. apply is_const_pow_m_n_op.
    rewrite H0. clear H0.
    assert (is_bconst (rep 10)). apply is_bconst_is_const. apply is_const_rep_n.
    rewrite H0. clear H0.
    assert (is_bconst mul_m_n_op). apply is_bconst_is_const. apply is_const_mul_m_n_op.
    rewrite H0. clear H0.
    assert (is_bconst nat_length_op). apply is_bconst_is_const. apply is_const_nat_length_op.
    rewrite H0. clear H0.
    simpl. auto.
Qed.

Theorem steps_star_concat10_op : forall m n, concat10_op [+] m [+] n ~>*
                                                         add_m_n_op [+] m [+] (mul_m_n_op [+] n [+] (pow_m_n_op [+] rep 10 [+] (nat_length_op [+] m ))).
Proof.
  intros.
  unfold concat10_op.
  eapply steps_star_trans.
  apply steps_star_compile_2ary.
  unfold concat10_action.
  Opaque add_m_n_op.
  Opaque pow_m_n_op.
  Opaque rep.
  simpl.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  apply steps_none.
  apply is_const_nat_length_op.
  apply is_const_rep_n.
  apply is_const_pow_m_n_op.
  apply is_const_mul_m_n_op.
  apply is_const_add_m_n_op.
Qed.
  
Theorem concat10_spec : forall m n, concat10_op [+] rep m [+] rep n ~>* rep (concat10 m n).
Proof.
  intros.
  eapply steps_star_trans.
  apply steps_star_concat10_op.
  eapply steps_star_trans.
  apply steps_star_app_r.
  apply steps_star_app_r.
  apply steps_star_app_r.
  apply nat_length_op_spec.
  eapply steps_star_trans.
  apply steps_star_app_r.
  apply steps_star_app_r.
  apply pow_m_n_spec.
  eapply steps_star_trans.
  apply steps_star_app_r.
  apply mul_m_n_spec.
  eapply steps_star_trans.
  apply add_m_n_spec.
  unfold concat10.
  apply steps_none.
Qed.

(* Godel Numbering *)
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

(* input is a little-endian digit reprentation *)
Fixpoint digits_to_nat l idx :=
  match l with
  | nil => 0
  | d :: l' => (10^idx * d) + (digits_to_nat l' (1 + idx))
  end.

Lemma digits_to_nat_mul10 : forall l n, 10*(digits_to_nat l n) = digits_to_nat l (Datatypes.S n).
Proof.
  intro l.
  induction l.
  *
    simpl. auto.
  *
    unfold digits_to_nat. fold digits_to_nat.
    intros.
    rewrite PeanoNat.Nat.mul_add_distr_l.
    rewrite PeanoNat.Nat.mul_assoc.
    rewrite PeanoNat.Nat.pow_succ_r.
    rewrite IHl.
    assert (Datatypes.S (1 + n) = 1 + Datatypes.S n) by lia.
    rewrite H. reflexivity.
    lia.
Qed.
    
Lemma digits_to_nat_pow10 : forall l n m, digits_to_nat l (m + n) = 10^m * digits_to_nat l n.
Proof.
  induction m.
  *
    simpl. lia.
  *
    assert (Datatypes.S m + n = Datatypes.S (m + n)) by lia.
    rewrite H. clear H.
    generalize (digits_to_nat_mul10 l (m+n)). intros.
    rewrite <- H.
    rewrite IHm.
    rewrite PeanoNat.Nat.mul_assoc.
    rewrite PeanoNat.Nat.pow_succ_r.
    reflexivity.
    lia.
Qed.

Lemma digits_to_nat_nth_all_eq_0 : forall l, (forall k, nth k l 0 = 0) -> digits_to_nat l 0 = 0.
Proof.
  intros.
  induction l.
  *
    simpl. auto.
  *
    simpl. 
    rewrite <- plus_n_O.
    generalize (H 0). intros.
    simpl in H0. subst.
    simpl.
    rewrite <- digits_to_nat_mul10.
    rewrite IHl. lia.
    intros.
    generalize (H (1 + k)). intros.
    simpl in H0. auto.
Qed.

Definition nth_all_eq l1 l2 := (forall k, nth k l1 0 = nth k l2 0).

Lemma digits_to_nat_nth_all_eq : forall l1 l2, nth_all_eq l1 l2 -> digits_to_nat l1 0 = digits_to_nat l2 0.
Proof.
  unfold nth_all_eq.
  intro l1.
  induction l1.
  *
    intros.
    simpl.
    symmetry.
    apply digits_to_nat_nth_all_eq_0.
    intros.
    eapply PeanoNat.Nat.eq_trans.
    symmetry.
    apply H.
    simpl. destruct k; auto.
  *
    intros.
    destruct l2.
    **
      eapply PeanoNat.Nat.eq_trans.
      apply digits_to_nat_nth_all_eq_0.
      intros.
      eapply PeanoNat.Nat.eq_trans.
      apply H. simpl. destruct k; auto.
      simpl. auto.
    **
      simpl.
      generalize (H 0). intros.
      simpl in H0. subst.
      rewrite <- digits_to_nat_mul10.
      rewrite <- digits_to_nat_mul10.
      erewrite (IHl1 l2). auto.
      intros.
      generalize (H (1+k)). intros.
      simpl in H0. auto.
Qed.
      
Definition list_ub l n := forall k, In k l -> k <= n.

Lemma list_ub_equiv : forall l n, (list_ub l n <-> (forall k, nth k l 0 <= n)).
Proof.
  intros.
  split.
  *
    generalize n. clear n.
    induction l.
    **
      simpl. destruct k; lia.
    **
      destruct k; simpl.
      unfold list_ub in H.
      apply H. constructor. auto.
      apply IHl.
      unfold list_ub.
      intros.
      unfold list_ub in H.
      apply H.
      right. auto.
  *
    generalize n. clear n.
    induction l.
    **
      intros.
      unfold list_ub. intros. inversion H0.
    **
      intros.
      unfold list_ub.
      intros.
      destruct H0.
      generalize (H 0). intros. simpl in H1.
      lia.
      apply IHl.
      intros.
      generalize (H (1+k0)). intros. simpl in H1. auto. auto.
Qed.

Lemma list_ub_also : forall l n, list_ub l n -> forall l', nth_all_eq l l' -> list_ub l' n.
Proof.
  intros.
  rewrite list_ub_equiv in H.
  rewrite list_ub_equiv.
  intros.
  unfold nth_all_eq in H0.
  rewrite <- H0. apply H.
Qed.

Lemma digits_to_nat_max l : list_ub l 9 -> digits_to_nat l 0 < 10^(length l).
Proof.
  induction l.
  *
    simpl. auto.
  *
    intros.
    simpl digits_to_nat.
    rewrite <- digits_to_nat_mul10.
    rewrite <- plus_n_O.
    assert (a <= 9). apply H. unfold In. auto.
    assert (length(a::l) = Datatypes.S (length l)).
    simpl. auto.
    rewrite H1.
    rewrite PeanoNat.Nat.pow_succ_r; try lia.
    assert (a + 10*digits_to_nat l 0 < 10 * (1 + digits_to_nat l 0)) by lia.
    eapply PeanoNat.Nat.lt_le_trans. apply H2.
    apply Mult.mult_le_compat_l.
    apply IHl.
    unfold list_ub.
    intros.
    apply H. right. auto.
Qed.

Definition digits_represent l n := (length l = nat_length n) /\ (list_ub l 9) /\ (digits_to_nat l 0 = n).

Theorem exists_digits_rep : forall n, exists l, digits_represent l n.
Proof.
  intros.
  apply (lt_wf_ind n (fun n' => exists l, digits_represent l n')). clear n.
  intros.
  
  assert (n < 10 \/ 10 <= n) by lia.
  destruct H0.
  *
    exists [n].
    unfold digits_represent.
    unfold list_ub.
    split.
    **
      simpl.
      generalize (nat_length_spec n). intros.
      unfold nat_has_length in H1.
      destruct H1.
      destruct H1. auto.
      destruct H1.
      assert (10^(pred (nat_length n)) < 10). {
        eapply PeanoNat.Nat.le_lt_trans.
        destruct H2. apply l. auto.
      }
      rewrite <- PeanoNat.Nat.pow_1_r in H3.
      rewrite <- PeanoNat.Nat.pow_lt_mono_r_iff in H3.
      generalize (nat_length_neq_0 n). intros.
      lia. lia.
    **
      split. intros.
      assert (n = k). {
        inversion H1. auto.
        inversion H2.
      }
      subst. lia.

      simpl. lia.
  *
    generalize (PeanoNat.Nat.div_mod n 10).
    intros.
    assert (10 <> 0) by lia.
    apply H1 in H2. clear H1.
    assert (n / 10 < n) by lia.
    apply H in H1.
    destruct H1.
    unfold digits_represent in H1. destruct H1. destruct H3.
    assert (digits_to_nat x 1 = 10*(n/10)).
    generalize (digits_to_nat_mul10 x 0). intros.
    assert (10 * digits_to_nat x 0 = 10 * (n / 10)). {
      rewrite H4. auto.
    }
    rewrite H5 in H6. clear H5.
    auto.
    rewrite <- H5 in H2. clear H5. clear H4.
    exists (n mod 10 :: x).
    unfold digits_represent.
    split.

    simpl.
    rewrite H1.
    rewrite nat_length_div10. auto. auto.
    split.

    unfold list_ub in H3.
    unfold list_ub.
    intros.
    inversion H4.
    assert (k < 10).
    rewrite <- H5.
    apply PeanoNat.Nat.mod_upper_bound.
    lia. lia.
    apply H3. auto.
    unfold digits_to_nat. fold digits_to_nat.
    rewrite <- plus_n_O.
    rewrite PeanoNat.Nat.pow_0_r.
    rewrite PeanoNat.Nat.mul_1_l. lia.
Qed.

Definition get_digit n m := (m / 10^n) mod 10.

Lemma get_digit_digits_to_nat : forall l, (list_ub l 9) -> forall n, get_digit n (digits_to_nat l 0) = nth n l 0.
Proof.
  intro l.
  unfold get_digit.
  induction l.
  *
    intros.
    unfold digits_to_nat.
    rewrite PeanoNat.Nat.div_small.
    simpl. destruct n; auto.
    apply pow_gt_0. lia.
  *
    intros.
    assert (n = 0 \/ n <> 0) as cases by lia.
    destruct cases.
    **
      subst.
      unfold digits_to_nat.
      fold digits_to_nat.
      rewrite PeanoNat.Nat.pow_0_r.
      rewrite PeanoNat.Nat.mul_1_l.
      rewrite PeanoNat.Nat.div_1_r.
      rewrite PeanoNat.Nat.add_0_r.
      rewrite <- PeanoNat.Nat.add_mod_idemp_r.
      unfold nth.
      assert (digits_to_nat l 1 mod 10 = 0). {
        rewrite <- digits_to_nat_mul10.
        rewrite PeanoNat.Nat.mul_comm.
        apply PeanoNat.Nat.mod_mul.
        lia.
      }
      rewrite H0.
      rewrite PeanoNat.Nat.add_0_r.
      apply PeanoNat.Nat.mod_small.
      assert (a <= 9).
      apply H. constructor. auto. lia. lia.
    **
      destruct n.
      exfalso. apply H0. auto. clear H0.
      unfold digits_to_nat. fold digits_to_nat.
      rewrite PeanoNat.Nat.pow_0_r.
      rewrite PeanoNat.Nat.mul_1_l.
      rewrite PeanoNat.Nat.add_0_r.
      rewrite <- digits_to_nat_mul10.
      rewrite PeanoNat.Nat.mul_comm.
      rewrite PeanoNat.Nat.pow_succ_r.
      rewrite <- PeanoNat.Nat.div_div.
      rewrite PeanoNat.Nat.div_add.
      assert (a / 10 = 0). {
        apply PeanoNat.Nat.div_small.
        assert (a <= 9).
        apply H. constructor. auto.
        lia.
      }
      rewrite H0. clear H0.
      rewrite PeanoNat.Nat.add_0_l.
      rewrite IHl. simpl. reflexivity.
      unfold list_ub in IHl.
      unfold list_ub in H.
      unfold list_ub.
      intros.
      apply H.
      unfold In. right. apply H0.
      lia. lia.
      apply PeanoNat.Nat.pow_nonzero. lia.
      lia.
Qed.

Theorem digits_rep_also : forall n l, digits_represent l n -> forall l', length l' = nat_length n -> nth_all_eq l l' -> digits_represent l' n.
Proof.
  intros.
  unfold digits_represent. split. subst. auto.
  split.
  eapply list_ub_also.
  unfold digits_represent in H. destruct H. destruct a.
  apply l0. auto.
  generalize (digits_to_nat_nth_all_eq l).
  intros.
  rewrite <- H2.
  apply H. auto.
Qed.  

Theorem digits_rep_explicit : forall n l, digits_represent l n -> (forall k, nth k l 0 = get_digit k n).
Proof.
  intros.
  unfold digits_represent in H.
  destruct H. destruct H0.
  rewrite <- H1.
  rewrite get_digit_digits_to_nat. auto.
  auto.
Qed.

Theorem digits_rep_explicit_rev : forall n l, (forall k, nth k l 0 = get_digit k n) /\ (length l = nat_length n) -> digits_represent l n.
Proof.
  intros.
  generalize (exists_digits_rep n). intros.
  destruct H0.
  apply (digits_rep_also n x H0 l). destruct H. auto.
  generalize (digits_rep_explicit n x H0). intros.
  clear H0.
  unfold nth_all_eq.
  intros.
  rewrite H1.
  destruct H.
  rewrite H. auto.
Qed.

Lemma not_digits_rep_nil : forall n, ~ digits_represent nil n.
Proof.
  intros.
  unfold not. intros.
  unfold digits_represent in H.
  destruct H.
  simpl in H.
  apply (nat_length_neq_0 n). auto.
Qed.

Lemma nth_all_eq_eq : forall (l1 l2 : list nat), (forall k d, nth k l1 d = nth k l2 d) -> l1 = l2.
Proof.
  intro l1.
  induction l1.
  *
    intros.
    destruct l2. auto.
    generalize (H 0 0). intros. simpl in H0.
    generalize (H 0 1). intros. simpl in H1.
    subst. inversion H1.
  *
    intros.
    destruct l2.
    generalize (H 0 0). intros. simpl in H0.
    generalize (H 0 1). intros. simpl in H1.
    subst. inversion H1.
    generalize (H 0 0). intros. simpl in H0. subst.
    assert (l1 = l2).
    apply IHl1.
    intros.
    generalize (H (1+k) d). intros.
    simpl in H0. auto. subst. auto.
Qed.

Theorem digits_rep_unique : forall n l1 l2, digits_represent l1 n -> digits_represent l2 n -> l1 = l2.
Proof.
  intros.
  apply nth_all_eq_eq.
  intros.
  assert (k < length l1 \/ length l1 <= k) as cases by lia.
  destruct cases.
  *
    assert (nth k l1 d = nth k l1 0). {
      apply nth_indep. auto.
    }

    assert (nth k l2 d = nth k l2 0). {
      apply nth_indep.
      unfold digits_represent in H0.
      unfold digits_represent in H.
      destruct H0.
      destruct H.
      rewrite H0.
      rewrite <- H. auto.
    }

    rewrite H2. clear H2.
    rewrite H3. clear H3.

    erewrite  digits_rep_explicit.
    erewrite  digits_rep_explicit.
    auto.
    apply H0. apply H.
  *
    rewrite nth_overflow.
    rewrite nth_overflow.
    auto.
    destruct H. destruct H0.
    rewrite H0. rewrite <- H. auto.
    auto.
Qed.

Fixpoint range start count :=
  match count with
  | 0 => nil
  | Datatypes.S count' => start :: (range (Datatypes.S start) count')
  end.

Lemma range_length start count :  length (range start count) = count.
Proof.
  generalize start. clear start.
  induction count.
  *
    simpl. auto.
  *
    intros.
    simpl.
    rewrite IHcount. auto.
Qed.

Lemma range_nth start count k : k  < count -> forall d, nth k (range start count) d = start + k.
Proof.
  intro.
  generalize H. clear H.
  generalize k. clear k.
  generalize start. clear start.
  induction count.
  *
    intros. inversion H.
  *
    intros.
    unfold range. fold range.
    destruct k.
    simpl. lia.
    simpl.
    rewrite IHcount. lia. lia.
Qed.
  
Definition nat_to_digits n := map (fun d => get_digit d n) (range 0 (nat_length n)).

Compute (nat_to_digits 1230).

Theorem nat_to_digits_length n : length (nat_to_digits n) = nat_length n.
Proof.
  unfold nat_to_digits.
  rewrite map_length.
  apply range_length.
Qed.

Theorem nat_to_digits_spec : forall n, digits_represent (nat_to_digits n) n.
Proof.
  intros.
  generalize (nat_to_digits_length n). intros.
  
  apply digits_rep_explicit_rev.
  intros.
  split; auto.

  intros.
  assert ((k < length(nat_to_digits n)) \/ (length(nat_to_digits n) <= k)) by lia.
  destruct H0.
  *
    generalize (map_nth (fun d : nat => get_digit d n) (range 0 (nat_length n)) 0 k). intros.
    assert (nth k (map (fun d : nat => get_digit d n) (range 0 (nat_length n))) (get_digit 0 n) = nth k (map (fun d : nat => get_digit d n) (range 0 (nat_length n))) 0). {
      apply nth_indep. apply H0.
    }
    unfold nat_to_digits.
    rewrite <- H2.
    rewrite H1.
    rewrite range_nth.
    simpl. auto. lia.
  *
    rewrite nth_overflow; auto.
    rewrite H in H0.
    unfold get_digit.
    assert (n < 10^k).
    generalize (nat_length_spec n).
    intros.
    unfold nat_has_length in H1.
    destruct H1.
    destruct H1.
    subst.
    assert (1 <= 10^k). {
      Search (_^_ <> 0).
      generalize (PeanoNat.Nat.pow_nonzero 10 k). intros.
      lia.
    }
    eapply PeanoNat.Nat.lt_le_trans.
    apply PeanoNat.Nat.lt_0_1. auto.
    destruct H1. destruct H2.
    eapply PeanoNat.Nat.lt_le_trans.
    apply H3.
    apply PeanoNat.Nat.pow_le_mono_r. auto. auto.
    assert (n / 10^k = 0).
    apply PeanoNat.Nat.div_small. auto.
    rewrite H2. auto.
Qed.

Theorem app_represents_cat10 : forall l1 n1 l2 n2,
    digits_represent l1 n1 -> digits_represent l2 n2 -> n2 <> 0 -> digits_represent (l1 ++ l2) (concat10 n1 n2).
Proof.
  intros.
  unfold concat10.
  apply digits_rep_explicit_rev.
  split.
  intros.
  assert (k < length l1 \/ length l1 <= k) by lia.
  destruct H2.
  rewrite app_nth1; auto.
  unfold get_digit.
  
  assert (k + (length l1 - k) = length l1) by lia.
  assert (length l1 = nat_length n1). {
    destruct H. auto.
  }
  rewrite <- H4.
  rewrite <- H3.
  rewrite PeanoNat.Nat.pow_add_r.
  assert (n2 * (10 ^ k * 10 ^ (length l1 - k)) = (n2 * 10 ^ (length l1 - k))*10^k) by lia.
  rewrite H5.
  rewrite PeanoNat.Nat.div_add.
  rewrite <- PeanoNat.Nat.add_mod_idemp_r.
  assert (length l1 - k = 1 + (length l1 - k - 1)) by lia. rewrite H6.
  rewrite PeanoNat.Nat.pow_succ_r.
  assert (n2 * (10 * 10 ^ (length l1 - k - 1)) = (n2 * 10 ^ (length l1 - k - 1))*10) by lia.
  rewrite H7.
  rewrite PeanoNat.Nat.mod_mul.
  rewrite <- plus_n_O.
  auto.
  apply digits_rep_explicit. auto. lia. lia. lia.
  apply (PeanoNat.Nat.pow_nonzero). lia.
  rewrite app_nth2; auto.
  unfold get_digit.
  assert (k = (length l1 + (k - length l1))) by lia.
  rewrite H3 at 2.
  unfold digits_represent in H.
  destruct H.
  rewrite <- H.
  rewrite PeanoNat.Nat.pow_add_r.
  rewrite <- PeanoNat.Nat.div_div.
  rewrite PeanoNat.Nat.div_add.
  assert (n1 / 10^(length l1) = 0). {
    rewrite H.
    apply PeanoNat.Nat.div_small.
    generalize (nat_length_spec n1). intros.
    unfold nat_has_length in H4.
    destruct H5. destruct H5. subst.
    simpl. lia.
    destruct H5. apply H6.
  }
  rewrite H5.
  rewrite plus_O_n.
  apply digits_rep_explicit.
  auto.
  apply PeanoNat.Nat.pow_nonzero. lia.
  apply PeanoNat.Nat.pow_nonzero. lia.
  apply PeanoNat.Nat.pow_nonzero. lia.
  rewrite app_length.
  unfold digits_represent in H.
  destruct H.
  unfold digits_represent in H0.
  destruct H0.
  rewrite H.
  rewrite H0.

  generalize (nat_length_concat10 n1 n2). intros.
  apply H4 in H1. clear H4.
  rewrite <- H1. auto.
Qed.

Corollary digits_to_nat_concat10 : forall l1 n1 l2 n2,
    digits_represent l1 n1 -> digits_represent l2 n2 -> n2 <> 0 -> (concat10 n1 n2) = digits_to_nat (l1 ++ l2) 0.
Proof.
  intros.
  generalize (app_represents_cat10 l1 n1 l2 n2 H H0 H1). intros.
  unfold digits_represent in H2.
  destruct H2. destruct H3. auto.
Qed.

Theorem nat_length_app : forall l1 n1 l2 n2,
    digits_represent l1 n1 -> digits_represent l2 n2 -> n2 <> 0 ->
    nat_length (digits_to_nat (l1 ++ l2) 0) = length l1 + length l2.
Proof.
  intros.
  assert (digits_represent (l1 ++ l2) (concat10 n1 n2)). 
  apply app_represents_cat10; auto.
  unfold digits_represent in H2.
  destruct H2. destruct H3.
  rewrite H4.
  rewrite app_length in H2. auto.
Qed.

Fixpoint godel_digits (c : cexpr) : list nat :=
  match c with
  | S => [ 1 ]
  | K => [ 2 ]
  | app c1 c2 => [3] ++ (godel_digits c1) ++ (godel_digits c2) ++ [4]
  | var n => [ 5 ]
  end.

(* let l be the godel_digits of a term c, possibly followed by any other digits *)
(* l = godel_list c ++ other *)
(* prefix_term_length l 0 0 = length godel_list *)
Fixpoint prefix_term_length l acc opens :=
  match l with
  | 3 :: l' => prefix_term_length l' (Datatypes.S acc) (Datatypes.S opens)
  | 4 :: l' => if opens =? 1 then (Datatypes.S acc) else prefix_term_length l' (Datatypes.S acc) (pred opens)
  | _ :: l' => if opens =? 0 then 1 else prefix_term_length l' (Datatypes.S acc) opens
  | nil => acc
  end.

Lemma prefix_term_length_spec : forall c l acc opens,
    prefix_term_length (godel_digits c ++ l) acc (Datatypes.S opens) = prefix_term_length l (acc + length(godel_digits c)) (Datatypes.S opens).
Proof.
  intro.
  induction c.
  *
    intros. simpl.
    assert (Datatypes.S acc = acc + 1) by lia. rewrite H.
    reflexivity.
  *
    intros. simpl.
    assert (Datatypes.S acc = acc + 1) by lia. rewrite H.
    reflexivity.
  *
    intros. simpl.
    assert (Datatypes.S acc = acc + 1) by lia. rewrite H.
    reflexivity.
  *
    intros.
    unfold godel_digits. fold godel_digits.
    simpl.
    Search ((_ ++ _) ++ _).
    rewrite <- app_assoc.
    rewrite IHc1.
    rewrite <- app_assoc.
    rewrite IHc2.
    simpl.
    rewrite app_length.
    rewrite app_length.
    simpl.
    assert (Datatypes.S (Datatypes.S (acc + length (godel_digits c1) + length (godel_digits c2))) =
            acc + Datatypes.S (length (godel_digits c1) + (length (godel_digits c2) + 1))) by lia.
    rewrite H.
    reflexivity.
Qed.

(* if l = godel_digits (c1 [+] c2) *)
(* this function computes length of godel_digits (c1) *)
Fixpoint left_term_length l :=
  match l with
  | 3 :: l' => prefix_term_length l' 0 0
  | _ => 0
  end.

Theorem left_term_length_spec : forall c1 c2, left_term_length (godel_digits (c1 [+] c2)) = length (godel_digits c1).
Proof.
  intros.
  destruct c1; simpl; auto.
  rewrite <- app_assoc.
  rewrite prefix_term_length_spec. simpl.
  rewrite <- app_assoc.
  rewrite prefix_term_length_spec. simpl.
  rewrite app_length.
  rewrite app_length. simpl.
  assert (Datatypes.S (length (godel_digits c1_1) + length (godel_digits c1_2)) =
          length (godel_digits c1_1) + (length (godel_digits c1_2) + 1)) by lia.
  rewrite H.
  reflexivity.
Qed.

Definition has_unambiguous_parse l := forall c1, is_const c1 /\ l = godel_digits c1 -> forall c2, l = godel_digits c2 -> c1 = c2.

Theorem list_prefixes_equal : forall lx ly lx' ly' : list nat, length lx = length lx' -> lx ++ ly = lx' ++ ly' -> lx = lx'.
Proof.
  intro lx.
  induction lx.
  *
    intros.
    destruct lx'. auto.
    simpl in H. inversion H.
  *
    intros.
    destruct lx'.
    simpl in H. inversion H.
    assert (a = n). {
      inversion H0. subst. auto.
    }
    subst.
    simpl in H.
    inversion H. clear H.
    assert (lx = lx'). {
      eapply IHlx.
      auto.
      rewrite <- app_comm_cons in H0.
      rewrite <- app_comm_cons in H0.
      inversion H0. apply H1.
    }
    rewrite H. auto.
Qed.

Check lt_wf_ind.
Theorem all_unambiguous_parse : forall l, has_unambiguous_parse l.
Proof.
  intros.
  remember (length l).
  generalize Heqn. clear Heqn.
  generalize l. clear l.
  apply (lt_wf_ind n).
  clear n.
  intros.
  unfold has_unambiguous_parse.
  intros.
  destruct H0.
  destruct c1.
  *
    generalize (not_is_const_var n0). intros.
    contradiction.
  *
    subst.
    destruct c2; simpl in H1; inversion H1. auto.
  *
    subst.
    destruct c2; simpl in H1; inversion H1. auto.
  *
    subst.
    assert (exists c2_1 c2_2, c2 = c2_1 [+] c2_2). {
      remember c2.
      rewrite Heqc in H1.
      destruct c2; simpl in H1; inversion H1.
      exists c2_1, c2_2. auto.
    }
    destruct H2 as [c2_1  [c2_2] ].
    subst.
    generalize (left_term_length_spec c1_1 c1_2). intros.
    generalize (left_term_length_spec c2_1 c2_2). intros.
    rewrite H1 in H2.
    rewrite H2 in H3.
    clear H2.
    simpl in H1.
    inversion H1.
    assert (godel_digits c1_1 = godel_digits c2_1). {
      eapply list_prefixes_equal.
      auto.
      apply H4.
    }
    assert (c1_1 = c2_1). {
      unfold has_unambiguous_parse in H.
      eapply H.
      assert (length(godel_digits c1_1) < length(godel_digits (c1_1 [+] c1_2))). {
        simpl.
        rewrite app_length.
        rewrite app_length.
        simpl. lia.
      }
      apply H5.
      reflexivity.
      split.
      apply is_const_app_iff in H0. apply H0. auto. auto.
    }
    subst.
    inversion H1.
    apply app_inv_head in H6.
    apply app_inv_tail in H6.
    assert (c1_2 = c2_2). {
      eapply H.
      assert (length (godel_digits c1_2) < length (godel_digits (c2_1 [+] c1_2))). {
        simpl.
        rewrite app_length.
        rewrite app_length.
        simpl.
        lia.
      }
      apply H5.
      reflexivity.
      split.
      apply is_const_app_iff in H0. apply H0. auto. auto.
    }
    subst. auto.
Qed.

(* Do not try to compute this. It crashes Coq *)
Definition godel_number (c : cexpr) : nat :=
  digits_to_nat (godel_digits c) 0.

Theorem concat10_neq_0 : forall a b, b <> 0 -> concat10 a b <> 0.
Proof.
  intros.
  unfold concat10.
  unfold not. intros.
  apply Plus.plus_is_O in H0.
  destruct H0.
  rewrite H0 in H1.
  simpl in H1.
  assert (b = 0) by lia.
  apply H. auto.
Qed.

Theorem digits_represent_S : digits_represent (godel_digits S) 1.
Proof.
  unfold digits_represent.
  split. simpl. auto.
  split. unfold list_ub. intros. inversion H. lia.
  inversion H0.
  auto.
Qed.

Theorem digits_represent_K : digits_represent (godel_digits K) 2.
Proof.
  unfold digits_represent.
  split. simpl. auto.
  split. unfold list_ub. intros. inversion H. lia.
  inversion H0.
  auto.
Qed.

Theorem digits_represent_var : forall n, digits_represent (godel_digits (var n)) 5.
Proof.
  unfold digits_represent.
  split. simpl. auto.
  split. unfold list_ub. intros. inversion H. lia.
  inversion H0.
  auto.
Qed.

Theorem digits_represent_app : forall c1 n1 c2 n2,
    digits_represent (godel_digits c1) n1 ->
    digits_represent (godel_digits c2) n2 ->
    digits_represent (godel_digits (c1 [+] c2)) (concat10 3 (concat10 n1 (concat10 n2 4))).
Proof.
  intros.

  assert (digits_represent [3] 3). {
    unfold digits_represent. split. simpl. auto.
    split. unfold list_ub. intros. inversion H1. lia. inversion H2.
    simpl. auto.
  }

  assert (digits_represent [4] 4). {
    unfold digits_represent. split. simpl. auto.
    split. unfold list_ub. intros. inversion H2. lia. inversion H3.
    simpl. auto.
  }
  
  unfold godel_digits. fold godel_digits.

  apply app_represents_cat10. auto.
  apply app_represents_cat10. auto.
  apply app_represents_cat10. auto. auto. lia.
  apply concat10_neq_0. lia.
  apply concat10_neq_0.
  apply concat10_neq_0. lia.
Qed.

Theorem godel_number_spec c : digits_represent (godel_digits c) (godel_number c).
Proof.
  induction c.
  *
    apply digits_represent_var.
  *
    apply digits_represent_S.
  *
    apply digits_represent_K.
  *
    unfold godel_number.
    generalize (digits_represent_app c1 (godel_number c1) c2 (godel_number c2) IHc1 IHc2). intros.
    unfold digits_represent in H.
    destruct H.
    destruct H0.
    rewrite H1.
    apply digits_represent_app. auto. auto.
Qed.
    
Definition godel_nxt : nat := godel_number nxt. Opaque godel_nxt.
Definition godel_zro : nat := godel_number zro. Opaque godel_zro.

Theorem godel_number_repSn n :
  digits_represent (godel_digits (rep (Datatypes.S n))) (concat10 3 (concat10 godel_nxt (concat10 (godel_number (rep n)) 4))).
Proof.
  Transparent rep.
  unfold rep. fold rep.
  apply digits_represent_app.
  apply godel_number_spec.
  apply godel_number_spec.
Qed.

Definition next_godelize_action :=
  concat10_op [+] rep 3 [+] (concat10_op [+] rep godel_nxt [+] (concat10_op [+] var 0 [+] rep 4)).

Definition next_godelize_op :=
  compile_nary 1 next_godelize_action.

Theorem is_const_next_godelize_op : is_const next_godelize_op.
Proof.
  unfold is_const.
  unfold next_godelize_op.
  intros.

  assert (n = 0 \/ n <> 0) by lia.
  destruct H.

  subst.
  *
    apply compile_nary_removes_vars.
    auto.
  *
    unfold next_godelize_action.
    apply compile_nary_intros_no_vars.
    Opaque concat10_op.
    Opaque rep.
    apply not_bcontains_var_contains_var.
    simpl.

    assert (is_bconst concat10_op). {
      apply is_bconst_is_const.
      apply is_const_concat10_op.
    }

    rewrite H0. clear H0.

    assert (forall n', is_bconst (rep n')). {
      intros.
      apply is_bconst_is_const.
      apply is_const_rep_n.
    }

    rewrite H0.
    rewrite H0.
    rewrite H0.

    simpl.
    destruct n.
    assert (1 = 0) as contra by lia. inversion contra.
    simpl. auto.
Qed.

Theorem steps_star_next_godelize_op : forall c,
    next_godelize_op [+] c ~>* concat10_op [+] rep 3 [+] (concat10_op [+] rep godel_nxt [+] (concat10_op [+] c [+] rep 4)).
Proof.
  intros.
  unfold next_godelize_op.
  eapply steps_star_trans.
  apply steps_star_compile_1ary.
  unfold next_godelize_action.
  Opaque concat10_op.
  Opaque rep.
  simpl.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  apply steps_none.
  apply is_const_rep_n.
  apply is_const_rep_n.
  apply is_const_rep_n.
  apply is_const_concat10_op.
Qed.

Theorem next_godelize_spec : forall n : nat, next_godelize_op [+] rep (godel_number (rep n)) ~>* rep (godel_number (rep (Datatypes.S n))).
Proof.
  intros.
  eapply steps_star_trans.
  apply steps_star_next_godelize_op.
  eapply steps_star_trans.
  eapply steps_star_app_r.
  eapply steps_star_app_r.
  apply concat10_spec.
  eapply steps_star_trans.
  apply steps_star_app_r.
  apply concat10_spec.
  eapply steps_star_trans.
  apply concat10_spec.
  assert (concat10 3 (concat10 godel_nxt (concat10 (godel_number (rep n)) 4)) = godel_number (rep (Datatypes.S n))). {
    generalize (godel_number_repSn n). intros.
    unfold godel_number at 2.
    unfold digits_represent in H. destruct H. destruct H0.
    rewrite H1. reflexivity.
  }
  rewrite H. apply steps_none.
Qed.
    
Definition godelize_action := eq_zro [+] var 1 [+] rep godel_zro [+] (next_godelize_op [+] (var 0 [+] (prv [+] var 1))).
Definition godelize_preop := compile_nary 2 godelize_action.
Definition godelize_op := sage godelize_preop.

Theorem is_const_godelize_op : is_const godelize_op.
Proof.
  unfold is_const.
  intros.
  assert (n < 2 \/ 2 <= n) as cases by lia.
  destruct cases.
  *
    unfold godelize_op.
    apply sage_intros_no_vars.
    apply compile_nary_removes_vars. auto.
  *
    unfold godelize_op.
    apply sage_intros_no_vars.
    apply compile_nary_intros_no_vars.
    unfold godelize_action.
    rewrite <- not_bcontains_var_contains_var.
    Opaque eq_zro.
    Opaque godel_zro.
    Opaque next_godelize_op.
    Opaque prv.
    destruct n. assert (1 = 0) as contra by lia. inversion contra.
    destruct n. assert (1 = 0) as contra by lia. inversion contra.
    unfold bcontains_var. fold bcontains_var.
    assert (is_bconst eq_zro). apply is_bconst_is_const. apply is_const_eq_zro. rewrite H0.
    assert (is_bconst (rep godel_zro)). apply is_bconst_is_const. apply is_const_rep_n. rewrite H1.
    assert (is_bconst next_godelize_op). apply is_bconst_is_const. apply is_const_next_godelize_op. rewrite H2.
    assert (is_bconst prv). apply is_bconst_is_const. apply is_const_prv. rewrite H3. auto.
Qed.

Theorem steps_star_godelize_op : forall c, godelize_op [+] c ~>* eq_zro [+] c [+] rep godel_zro [+] (next_godelize_op [+] (godelize_op [+] (prv [+] c))).
Proof.
  intros.
  unfold godelize_op.
  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_sage.
  unfold godelize_preop at 1.
  Opaque godelize_action.
  Opaque next_godelize_op.
  Opaque sage.
  Opaque godelize_preop.
  Opaque eq_zro.
  Opaque godel_zro.
  Opaque prv.
  eapply steps_star_trans.
  apply steps_star_compile_2ary.
  Transparent godelize_action.
  unfold godelize_action.
  rewrite subst_app_distr.
  rewrite subst_app_distr.
  rewrite subst_app_distr.
  rewrite subst_app_distr.
  rewrite subst_app_distr.
  simpl.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  apply steps_none.
  apply is_const_prv.
  apply is_const_next_godelize_op.
  apply is_const_rep_n.
  apply is_const_eq_zro.
Qed.

Theorem godelize_spec : forall n, godelize_op [+] rep n ~>* rep (godel_number (rep n)).
Proof.
  intros.
  induction n.
  *
    eapply steps_star_trans.
    apply steps_star_godelize_op.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_l.
    apply steps_star_eq_zro_0.
    eapply steps_star_trans.
    apply steps_star_t.
    apply steps_none.
  *
    eapply steps_star_trans.
    eapply steps_star_godelize_op.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply steps_star_app_l.
    apply steps_star_eq_zro_Sn.
    eapply steps_star_trans.
    apply steps_star_f.
    eapply steps_star_trans.
    eapply steps_star_app_r.
    eapply steps_star_app_r.
    eapply steps_star_prv_nxt.
    eapply steps_star_trans.
    apply steps_star_app_r.
    apply IHn.
    apply  next_godelize_spec.
Qed.

Definition normalize_action := concat10_op [+] rep 3 [+] (concat10_op [+] var 0 [+] (concat10_op [+] (godelize_op [+] var 0) [+] rep 4)).
Definition normalize_op := compile_nary 1 normalize_action.

Theorem is_const_normalize_op : is_const normalize_op.
Proof.
  unfold is_const.
  intros.
  unfold normalize_op.
  assert (n = 0 \/ n <> 0) as cases by lia.
  destruct cases.
  *
    apply compile_nary_removes_vars. lia.
  *
    apply compile_nary_intros_no_vars.
    unfold normalize_action.
    rewrite <- not_bcontains_var_contains_var.
    Opaque concat10_op. Opaque godelize_op. simpl.
    assert (is_bconst concat10_op). apply is_bconst_is_const. apply is_const_concat10_op. rewrite H0. clear H0.
    assert (is_bconst godelize_op). apply is_bconst_is_const. apply is_const_godelize_op. rewrite H0. clear H0.
    destruct n. contradiction. auto.
Qed.

Theorem steps_star_normalize_op : forall c,
    normalize_op [+] c ~>* concat10_op [+] rep 3 [+] (concat10_op [+] c [+] (concat10_op [+] (godelize_op [+] c) [+] rep 4)).
Proof.
  intros.
  eapply steps_star_trans.
  unfold normalize_op.
  apply steps_star_compile_1ary.
  unfold normalize_action.
  rewrite subst_app_distr.
  rewrite subst_app_distr.
  rewrite subst_app_distr.
  Opaque concat10_op.
  Opaque godelize_op.
  simpl.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  rewrite subst_const.
  apply steps_none.
  apply is_const_rep_n.
  apply is_const_godelize_op.
  apply is_const_rep_n.
  apply is_const_concat10_op.
Qed.

Theorem normalize_spec : forall n, normalize_op [+] rep n ~>* rep (concat10 3 (concat10 n (concat10 (godel_number (rep n)) 4))).
Proof.
  intros.
  eapply steps_star_trans.
  apply steps_star_normalize_op.
  eapply steps_star_trans.
  apply steps_star_app_r.
  apply steps_star_app_r.
  apply steps_star_app_l.
  apply steps_star_app_r.
  apply godelize_spec.
  eapply steps_star_trans.
  apply steps_star_app_r.
  apply steps_star_app_r.
  apply concat10_spec.
  eapply steps_star_trans.
  eapply steps_star_app_r.
  apply concat10_spec.
  apply concat10_spec.
Qed.

Definition sage2 c := B [+] c [+] normalize_op [+] rep (godel_number (B [+] c [+] normalize_op)).

Theorem fixed_point_principle :
  forall c : cexpr, (sage2 c) ~>* c [+] rep (godel_number (sage2 c)).
Proof.
  intros.
  unfold sage2 at 1.
  eapply steps_star_trans.
  apply steps_star_B.
  eapply steps_star_trans.
  apply steps_star_app_r.
  apply normalize_spec.

  assert (godel_number(sage2 c) = concat10 3 (concat10 (godel_number (B [+] c [+] normalize_op)) (concat10 (godel_number (rep (godel_number (B [+] c [+] normalize_op)))) 4))). {
    unfold sage2.
    pose digits_represent_app.
    assert (digits_represent (godel_digits (B [+] c [+] normalize_op [+] rep (godel_number (B [+] c [+] normalize_op))))
                             (concat10 3 (concat10 (godel_number (B [+] c [+] normalize_op)) (concat10 (godel_number (rep (godel_number (B [+] c [+] normalize_op)))) 4)))). {
      apply digits_represent_app.
      apply godel_number_spec.
      apply godel_number_spec.
    }
    generalize (godel_number_spec (B [+] c [+] normalize_op [+] rep (godel_number (B [+] c [+] normalize_op)))). intros.
    destruct H. destruct H1. rewrite <- H2.
    apply H0.
  }
  rewrite H.
  apply steps_none.
Qed.  
  
Definition is_computable (P : nat -> Prop) := exists c, is_const c /\ (forall n, (P n /\ c [+] rep n ~>* t) \/ (~ P n /\ c [+] rep n ~>* f)).

Definition neg := (V [+] f [+] t).

Theorem is_const_neg : is_const neg.
Proof.
  unfold neg.
  rewrite is_const_app_iff.
  rewrite is_const_app_iff.

  split. split.
  apply is_const_V.
  apply is_const_f.
  apply is_const_t.
Qed.

Theorem steps_star_neg_t : neg [+] t ~>* f.
Proof.
  unfold neg.
  eapply steps_star_trans.
  apply steps_star_V.
  apply steps_star_t.
Qed.

Theorem steps_star_neg_f : neg [+] f ~>* t.
Proof.
  unfold neg.
  eapply steps_star_trans.
  apply steps_star_V.
  apply steps_star_f.
Qed.

Theorem is_computable_complement (P : nat-> Prop) : is_computable P -> is_computable (fun n => ~P n).
Proof.
  intros.
  unfold is_computable.
  unfold is_computable in H.
  destruct H.
  exists (B [+] neg [+] x).
  split.

  rewrite is_const_app_iff. split.
  rewrite is_const_app_iff. split.
  apply is_const_B.
  apply is_const_neg.
  destruct H. auto.
  
  destruct H as [HH H].
  intros.
  generalize (H n). intros. clear H.
  destruct H0. destruct H.
  right.
  split.
  unfold not.
  intros. apply H1 in H. apply H.
  eapply steps_star_trans.
  apply steps_star_B.
  eapply steps_star_trans.
  apply steps_star_app_r.
  apply H0.
  apply steps_star_neg_t.
  left.
  destruct H.
  split.
  apply H.
  eapply steps_star_trans.
  apply steps_star_B.
  eapply steps_star_trans.
  apply steps_star_app_r.
  apply H0.
  apply steps_star_neg_f.
Qed.
 
Definition godel_sentence (P : nat -> Prop) (c : cexpr) := is_const c /\ ((c ~>* t /\ P (godel_number c)) \/ (~ c ~>* t /\ ~P (godel_number c))).

Theorem computable_prop_has_godel_sentence : forall P, is_computable P -> exists g, godel_sentence P g.
Proof.
  intros.
  unfold is_computable in H.
  destruct H as [x [HH H]].
  exists (sage2 x).
  unfold godel_sentence.

  split.
  unfold sage2.
  rewrite is_const_app_iff.
  rewrite is_const_app_iff.
  rewrite is_const_app_iff.
  split. split. split.
  apply is_const_B.
  auto.
  apply is_const_normalize_op.
  apply is_const_rep_n.
  
  generalize (H (godel_number (sage2 x))). intros.
  destruct H0.
  destruct H0.
  clear H.
  
  left.
  split.
  eapply steps_star_trans.
  apply fixed_point_principle.
  apply H1. apply H0.
  right.
  destruct H0.
  split.
  unfold not.
  intros.
  assert (t = f). {
    eapply unique_normal_form.
    apply H2.
    eapply steps_star_trans.
    apply fixed_point_principle.
    apply H1.
    apply is_normal_t.
    apply is_normal_f.
  }
  inversion H3.
  apply H0.
Qed.

Definition converges_t n := exists c, n = godel_number c /\ c ~>* t.

Theorem converges_t_not_computable : ~is_computable converges_t.
Proof.
  unfold not.
  intros.
  generalize (is_computable_complement converges_t H). intros.
  apply computable_prop_has_godel_sentence in H0.
  destruct H0.
  unfold godel_sentence in H0.
  unfold is_computable in H.
  destruct H as [c [HH H]].
  generalize (H (godel_number x)). intros. clear H.

  destruct H0 as [HHH H].
  destruct H; destruct H1.
  *
    destruct H. destruct H0. contradiction.
  *
    destruct H.
    apply H1.
    unfold converges_t.
    exists x. split; auto.
  *
    destruct H.
    destruct H0.
    unfold converges_t in H0.
    destruct H0.
    destruct H0.
    assert (x = x0). {
      generalize (godel_number_spec x). intros.
      generalize (godel_number_spec x0). intros.
      assert (godel_digits x = godel_digits x0). {
        eapply digits_rep_unique.
        apply H4.
        rewrite H0.
        auto.
      }
      generalize (all_unambiguous_parse (godel_digits x0)). intros.
      unfold has_unambiguous_parse in H7.
      apply H7.
      split. auto. auto. auto.
    }
    subst. contradiction.
  *
    destruct H.
    destruct H0.
    contradiction.
Qed.
