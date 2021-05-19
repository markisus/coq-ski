Require Coq.Arith.PeanoNat.
Require Import Lia.
Require Import Nat.
Import Coq.Arith.Wf_nat. (* needed for "lt_wf_ind" *)
Require Import List.

Require Import SKI.expr.
Require Import SKI.digits.
Require Import SKI.arithmetic_ops.
Require Import SKI.compile.
Require Import SKI.substitution.
Require Import SKI.church_rosser.
Require Import SKI.well_known_combinators.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Fixpoint godel_digits (c : expr) : list nat :=
  match c with
  | S => [ 1 ]
  | K => [ 2 ]
  | c1 [+] c2 => [3] ++ (godel_digits c1) ++ (godel_digits c2) ++ [4]
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
Definition left_term_length l :=
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
      rewrite Heqe in H1.
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
Definition godel_number (c : expr) : nat :=
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
  unfold godel_digits. fold godel_digits.
  apply app_represents_cat10.
  apply single_digit_represents. lia.
  apply app_represents_cat10. auto.
  apply app_represents_cat10. auto.
  apply single_digit_represents. lia. lia.
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
    generalize is_const_concat10_op. intros.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply is_const_rep_n.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply is_const_rep_n.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply is_const_rep_n.
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

    assert (n <> 0) by lia.
    assert (n <> 1) by lia.

    generalize is_const_next_godelize_op. intros.
    generalize is_const_eq_zro. intros.
    generalize is_const_prv. intros.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply is_const_rep_n.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
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
    generalize is_const_concat10_op. intros.
    generalize is_const_godelize_op. intros.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply is_const_rep_n.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply not_contains_var_app_iff. split.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_app_iff. split.
    auto.
    apply not_contains_var_var_iff. auto.
    apply is_const_rep_n.
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
  forall c, (sage2 c) ~>* c [+] rep (godel_number (sage2 c)).
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

Definition godel_sentence (P : nat -> Prop) (c : expr) := is_const c /\ ((c ~>* t /\ P (godel_number c)) \/ (~ c ~>* t /\ ~P (godel_number c))).

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
