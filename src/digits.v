Require Coq.Arith.PeanoNat.
Require Import Nat.
Require Import Lia.
Require Import List.
Import Coq.Arith.Wf_nat. (* needed for "lt_wf_ind" *)
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

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

(* little-endian concat *)
Definition concat10 a b : nat := a + b*10^(nat_length a).

Lemma concat10_neq_0 : forall a b, b <> 0 -> concat10 a b <> 0.
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

Lemma single_digit_represents : forall n, n < 10 -> digits_represent [n] n.
Proof.
  intros.
  generalize (nat_length_spec n). intros.
  destruct H0. destruct H0. subst.

  unfold digits_represent. simpl.
  split; auto. split; auto.
  unfold list_ub. intros. inversion H0. lia.
  inversion H2.

  destruct H0.
  destruct H1.

  assert (10^(pred (nat_length n)) < 10^1). {
    rewrite PeanoNat.Nat.pow_1_r.
    lia.
  }
  
  apply PeanoNat.Nat.pow_lt_mono_r_iff in H3; try lia.
  generalize (nat_length_neq_0 n). intros.
  assert (nat_length n = 1). lia.

  unfold digits_represent. split.
  subst. auto.
  split.
  unfold list_ub. intros.
  inversion H6. subst. lia. inversion H7.
  unfold digits_to_nat.
  rewrite PeanoNat.Nat.pow_0_r.
  lia.
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
