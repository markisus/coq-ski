Require Import SKI.expr.
Require Import SKI.substitution.
Require Import SKI.well_known_combinators.
Import Nat.
Require Coq.Arith.PeanoNat.
Require Coq.Arith.EqNat.
Require Import Lia.

Fixpoint alpha_elim (v : expr) (n: nat) : expr :=
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
      apply is_const_I.
    **
      apply not_contains_var_app_iff.
      split.
      apply is_const_K. auto.
  *
    simpl.
    apply not_contains_var_app_iff.
    split.
    apply is_const_K.
    apply is_const_S.
  *
    simpl.
    apply not_contains_var_app_iff.
    split; auto.
  *
    simpl.
    apply not_contains_var_app_iff in H.
    destruct H.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    apply is_const_S. apply IHc1. auto.
    apply IHc2. auto.
Qed.

Theorem alpha_elim_removes_var :    
  forall c n, ~ n IN α(n)*c.
Proof.
  intros.
  induction c.
  *
    intros.
    destruct (PeanoNat.Nat.eq_decidable n0 n).
    **
      subst.
      simpl.
      rewrite <- EqNat.beq_nat_refl.
      apply is_const_I.
    **
      apply PeanoNat.Nat.eqb_neq in H.
      unfold alpha_elim. rewrite H.
      apply not_contains_var_app_iff.
      split.
      apply is_const_K.
      apply not_contains_var_var_iff.
      unfold not. intros. subst.
      apply PeanoNat.Nat.eqb_neq in H. auto.
  *
    unfold alpha_elim.
    apply not_contains_var_app_iff.
    split.
    apply is_const_K.
    apply is_const_S.
  *
    unfold alpha_elim.
    apply not_contains_var_app_iff.
    split; apply is_const_K.
  *
    simpl.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    apply is_const_S.
    apply IHc1.
    apply IHc2.
Qed.

Fixpoint compile_nary_subterm (first_elim : nat) (num_elims : nat) (c : expr) :=
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
Fixpoint add_vars (c : expr) (n : nat) :=
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

(* Definition compile_3ary (c : expr) := alpha_elim (alpha_elim (alpha_elim c 2) 1) 0. *)
Definition compile_nary (n : nat) (c : expr) := compile_nary_subterm 0 n c.

Theorem steps_star_compile_nary : forall n c, add_vars (compile_nary (Datatypes.S n) c) (Datatypes.S n) ~>* c.
Proof.
  intros.
  destruct n.
  *
    simpl.
    apply steps_star_alpha_elim.
  *
    unfold compile_nary.
    eapply steps_star_trans.
    assert (1 + (1 + n) + 0 = Datatypes.S (Datatypes.S n))%nat by lia.
    rewrite <- H at 1.
    apply (steps_star_add_vars_compile_nary_subterm _ 0).
    simpl.
    apply steps_none.
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
Definition fmap_1ary (x : expr) := (0 <<- x, --).
Definition fmap_2ary (x y : expr) := (0 <<- x, 1 <<- y, --).
Definition fmap_3ary (x y z : expr) := (0 <<- x, 1 <<- y, 2 <<- z, --).

Lemma fmap_1ary_ub (x : expr) : fmap_ub (fmap_1ary x) 1.
Proof.
  unfold fmap_ub.
  intros.
  unfold fmap_1ary.

  destruct n.
  assert (1 = 0)%nat as X by lia.
  inversion X.

  induction n; auto.
Qed.

Lemma fmap_2ary_ub (x y : expr) : fmap_ub (fmap_2ary x y) 2.
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

Lemma fmap_3ary_ub (x y z : expr) : fmap_ub (fmap_3ary x y z) 3.
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
  forall n f, fmap_ub f n -> forall c, disjoint_expr_fmap (compile_nary n c) f.
Proof.
  intros.
  unfold disjoint_expr_fmap.
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
  replace (compile_nary 1 c [+] x) with ((add_vars (compile_nary 1 c) 1) <-- fmap_1ary x).
  apply steps_star_subst.
  apply steps_star_compile_nary.
  simpl.
  rewrite subst_disjoint. reflexivity.
  apply compile_nary_disjoint_fmap_lb.
  apply fmap_1ary_ub.
Qed.

Theorem steps_star_compile_2ary : forall c x y, compile_nary 2 c [+] x [+] y ~>* (c <-- (fmap_2ary x y)).
Proof.
  intros.
  replace (compile_nary 2 c [+] x [+] y) with ((add_vars (compile_nary 2 c) 2) <-- fmap_2ary x y).
  apply steps_star_subst.
  apply steps_star_compile_nary.
  simpl.
  rewrite subst_disjoint. reflexivity.
  apply compile_nary_disjoint_fmap_lb.
  apply fmap_2ary_ub.  
Qed.

Theorem steps_star_compile_3ary c x y z : (compile_nary 3 c) [+] x [+] y [+] z ~>* (c <-- (fmap_3ary x y z)).
Proof.
  intros.
  replace (compile_nary 3 c [+] x [+] y [+] z) with ((add_vars (compile_nary 3 c) 3) <-- fmap_3ary x y z).
  apply steps_star_subst.
  apply steps_star_compile_nary.
  simpl.
  rewrite subst_disjoint. reflexivity.
  apply compile_nary_disjoint_fmap_lb.
  apply fmap_3ary_ub.  
Qed.
