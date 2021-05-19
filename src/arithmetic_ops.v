Import Nat.
Require Import SKI.expr.
Require Import SKI.digits.
Require Import SKI.well_known_combinators.
Require Import SKI.compile.
Require Import SKI.substitution.
Require Import Lia.

(* Modeling the non-negative integers *)

Definition nxt : expr := V [+] f.
Definition prv : expr := T [+] f.
Definition zro : expr := I.

Theorem is_const_zro : is_const zro.
Proof.
  apply is_const_I.
Qed.

Fixpoint rep (n: nat) :=
  match n with
  | 0 => zro
  | Datatypes.S m => nxt [+] (rep m)
  end.

Theorem is_const_prv : is_const prv.
Proof.
  unfold prv.
  apply is_const_app_iff. split.
  apply is_const_T.
  apply is_const_f.
Qed.

Theorem is_const_nxt : is_const nxt.
Proof.
  unfold nxt.
  apply is_const_app_iff. split.
  apply is_const_V. apply is_const_f. 
Qed.

Theorem is_const_rep_n : forall n, is_const (rep n).
Proof.
  intros.
  induction n.
  *
    simpl.
    apply is_const_zro.
  *
    simpl.
    apply is_const_app_iff. split.
    apply is_const_nxt. auto.
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

Definition eq_zro : expr := T [+] t.

Theorem is_const_eq_zro : is_const eq_zro.
Proof.
  unfold eq_zro.
  apply is_const_app_iff. split.
  apply is_const_T. apply is_const_t.
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
    unfold add_m_n_action.
    generalize is_const_eq_zro. intros.
    generalize is_const_prv. intros.
    generalize is_const_nxt. intros.
    assert (n <> 0) by lia.
    assert (n <> 1) by lia.
    assert (n <> 2) by lia.

    apply not_contains_var_app_iff. split. 
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_app_iff. split.
    apply is_const_nxt.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_app_iff. split.
    apply is_const_prv.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_var_iff. auto.
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
    unfold mul_m_n_action.
    generalize is_const_eq_zro. intros.
    generalize is_const_zro. intros.
    generalize is_const_add_m_n_op. intros.
    generalize is_const_prv. intros.
    assert (n <> 0) by lia.
    assert (n <> 1) by lia.
    assert (n <> 2) by lia.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff.
    auto.
    auto.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_var_iff. auto.
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
    unfold pow_m_n_preop.
    apply compile_nary_intros_no_vars.
    unfold pow_m_n_action.
    generalize is_const_eq_zro. intros.
    generalize is_const_mul_m_n_op. intros.
    generalize is_const_prv. intros.
    assert (n <> 0) by lia.
    assert (n <> 1) by lia.
    assert (n <> 2) by lia.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply is_const_rep_n.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_var_iff. auto.
    auto.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_var_iff. auto.
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
    unfold gt_m_n_action.
    assert (n <> 0) by lia.
    assert (n <> 1) by lia.
    assert (n <> 2) by lia.
    generalize is_const_eq_zro. intros.
    generalize is_const_prv. intros.
    generalize is_const_f. intros.
    generalize is_const_t. intros.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    auto.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    auto.
    apply not_contains_var_app_iff. split. 
    apply not_contains_var_app_iff. split. 
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
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
    generalize is_const_gt_m_n_op. intros.
    generalize is_const_t. intros.
    generalize is_const_f. intros.
    assert (n <> 0) by lia.
    assert (n <> 1) by lia.

    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_var_iff. auto.
    auto.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_var_iff. auto.
    auto.
    auto.
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
  *
    apply compile_nary_removes_vars. auto.
  *
    assert (n <> 0) by lia.
    assert (n <> 1) by lia.

    apply compile_nary_intros_no_vars. unfold nat_length_action.

    unfold predlen.
    generalize is_const_eq_zro. intros.
    generalize is_const_eq_m_n_op. intros.
    generalize is_const_pow_m_n_op. intros.
    generalize is_const_nxt. intros.
    generalize is_const_prv. intros.

    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply is_const_rep_n.
    apply not_contains_var_app_iff. split.  
    apply not_contains_var_app_iff. split.  
    apply not_contains_var_app_iff. split.  
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_app_iff. split.  
    apply not_contains_var_app_iff. split.
    auto.
    apply is_const_rep_n.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
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
    generalize is_const_add_m_n_op. intros.
    generalize is_const_mul_m_n_op. intros.
    generalize is_const_pow_m_n_op. intros.
    generalize is_const_nat_length_op. intros.
    assert (n <> 0) by lia.
    assert (n <> 1) by lia.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply is_const_rep_n.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
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

