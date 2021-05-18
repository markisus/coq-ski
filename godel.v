Require Import Lia.
Require Import Nat.
Require Import List.

(* S K combinators *)
Inductive cexpr :=
| var : nat -> cexpr (* var 0 denotes variable 0, var 1 denotes variable 1, etc *)
| S : cexpr
| K : cexpr
| app : cexpr -> cexpr -> cexpr.

Notation " a + b " := (app a b) (at level 50, left associativity).

Inductive contains_var (n : nat) : cexpr -> Prop :=
| contains_here : contains_var n (var n)
| contains_left : forall c1 c2, contains_var n c1 -> contains_var n (c1 + c2)
| contains_right : forall c1 c2, contains_var n c2 -> contains_var n (c1 + c2).

Fixpoint bcontains_var (n : nat) (c : cexpr) : bool :=
  match c with
  | var m => m =? n
  | S => false
  | K => false
  | c1 + c2 => orb (bcontains_var n c1) (bcontains_var n c2)
  end.

Theorem bcontains_var_contains_var : forall n c, bcontains_var n c = true <-> contains_var n c.
Proof.
  intros.
  split.
  *
    intros.
    induction c.
    **
      simpl in H.
      Search (_ =? _ = true).
      rewrite PeanoNat.Nat.eqb_eq in H.
      subst.
      apply contains_here.
    **
      simpl in H.
      inversion H.
    **
      simpl in H.
      inversion H.
    **
      simpl in H.
      Search (_ || _ = true)%bool.
      rewrite Bool.orb_true_iff in H.
      inversion H.
      
      apply IHc1 in H0.
      apply contains_left.
      apply H0.

      apply IHc2 in H0.
      apply contains_right.
      apply H0.
  *
    intros.
    induction H.
    **
      simpl.
      Search (_ =? _).
      rewrite PeanoNat.Nat.eqb_refl.
      auto.
    **
      simpl.
      rewrite IHcontains_var.
      simpl.
      auto.
    **
      simpl.
      rewrite IHcontains_var.
      Search (_ || true)%bool.
      rewrite Bool.orb_true_r.
      auto.
Qed.

Theorem not_bcontains_var_contains_var : forall n c, bcontains_var n c = false <-> ~contains_var n c.
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

Inductive steps : cexpr -> cexpr -> Prop :=
| steps_S : forall x y z, steps (S + x + y + z) (x + z + (y + z))
| steps_K : forall x y, steps (K + x + y) x
| steps_app_l : forall x y z, steps x y -> steps (x + z) (y + z)
| steps_app_r : forall x y z, steps x y -> steps (z + x) (z + y).

Notation " a ~> b " := (steps a b) (at level 55, left associativity).

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

Theorem steps_star_app_l : forall c1 c2 c3, (c1 ~>* c2) -> (c1 + c3) ~>* (c2 + c3).
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

Theorem steps_star_app_r : forall c1 c2 c3, (c1 ~>* c2) -> (c3 + c1) ~>* (c3 + c2).
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

Theorem steps_star_eq : forall c1 c2 c3, c1 ~>* c2 -> c2 = c3 -> c1 ~>* c3.
Proof.
  intros.
  subst.
  assumption.
Qed.
    
Inductive equiv : cexpr -> cexpr -> Prop :=
| equiv_steps : forall c1 c2, (c1 ~> c2) -> equiv c1 c2
| equiv_app_l : forall x y z, equiv x y -> equiv (x + z) (y + z)
| equiv_app_r : forall x y z, equiv x y -> equiv (z + x) (z + y)
| equiv_refl : forall x, equiv x x
| equiv_sym : forall x y, equiv x y -> equiv y x
| equiv_trans : forall x y z, equiv x y -> equiv y z -> equiv x z.

Notation "x ~= y" := (equiv x y) (at level 55).
Notation "x ~/= y" := (~ (equiv x y)) (at level 55).

Theorem equiv_steps_star : forall c1 c2, c1 ~>* c2 -> c1 ~= c2.
Proof.
  intros.
  induction H.
  *
    apply equiv_refl.
  *
    apply equiv_steps.
    assumption.
  *
    eapply equiv_trans.
    apply equiv_steps.
    apply H.
    assumption.
Qed.

(* Substitutes variable n with c *)
Definition fmap := nat -> option cexpr.
Definition fmap_empty : fmap := fun n => None.
Definition fmap_assn (f: fmap) (n: nat) (c: cexpr) :=
  fun m => if m =? n then Some c else f m.
Definition fmap_del (f: fmap) (n: nat) :=
  fun m => if m =? n then None else f m.

Notation "'__'" := (fmap_empty).
Notation "n '!->' c ',' f" := (fmap_assn f n c)
                                (at level 100, c at next level, right associativity).

Fixpoint cexpr_subst (v : cexpr) (f: fmap) : cexpr :=
  match v with
  | var m => match f m with
             | Some c => c
             | None => var m
             end
  | va + vb => (cexpr_subst va f) + (cexpr_subst vb f)
  | S => S
  | K => K
  end.

Notation " e ; f " := (cexpr_subst e f) (at level 60, no associativity).

Theorem subst_app_distr :  forall c1 c2 f, (c1 + c2 ; f) = (c1 ; f) + (c2 ; f).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Definition disjoint_cexpr_fmap (c : cexpr) (f: fmap) :=
  forall n, contains_var n c -> f n = None.

Theorem subst_disjoint : forall c f, disjoint_cexpr_fmap c f -> c ; f = c.
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

Theorem steps_subst : forall v1 v2, v1 ~> v2 -> forall f, (v1; f) ~> (v2; f).
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

Theorem steps_star_subst : forall v1 v2, v1 ~>* v2 -> forall f, (v1; f) ~>* (v2; f).
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

Theorem equiv_subst : forall v1 v2, v1 ~= v2 -> forall f, (v1; f) ~= (v2; f).
Proof.
  intros.
  induction H.
  *
    apply equiv_steps.
    apply steps_subst.
    assumption.
  *
    simpl.
    apply equiv_app_l.
    assumption.
  *
    simpl.
    apply equiv_app_r.
    assumption.
  *
    apply equiv_refl.
  *
    apply equiv_sym.
    assumption.
  *
    eapply equiv_trans.
    apply IHequiv1.
    apply IHequiv2.
Qed.

(* If (S ~= K) then the universe collapses into one combinator *)
Axiom nequiv_S_K : S ~/= K.

Theorem K_cancellation : forall x y, K + x ~= K + y -> x ~= y.
Proof.
  intros.

  assert (K + x + K ~= x) as A. {
    apply equiv_steps.
    apply steps_K.
  }

  assert (K + y + K ~= y) as B. {
    apply equiv_steps.
    apply steps_K.
  }

  assert (K + x + K ~= K + y + K) as C. {
    apply equiv_app_l.
    assumption.
  }

  eapply equiv_trans.
  apply equiv_sym.
  apply A.

  eapply equiv_trans.
  apply C.
  
  apply B.
Qed.

Theorem nequiv_K_Kx : forall x, K ~/= K + x.
Proof.
  unfold not. intros.

  assert (forall y, K + y ~= K + x + y) as A. {
    intros.
    apply equiv_app_l.
    assumption.
  }

  assert (forall y, K + y ~= x) as B. {
    intros.
    eapply equiv_trans.
    apply (A y).
    apply equiv_steps.
    apply steps_K.
  }

  assert (forall y1 y2, K + y1 ~= K + y2) as C. {
    intros.
    eapply equiv_trans.
    apply (B y1).
    apply equiv_sym.
    apply (B y2).
  }

  assert (S ~= K) as equiv_S_K. {
    apply K_cancellation.
    apply C.
  }
  
  apply nequiv_S_K.
  assumption.
Qed.
  
(* Deriving I from S K *)
Definition I : cexpr := S + K + K.

Theorem steps_star_I : forall c, (I + c) ~>* c.
Proof.
  intro.
  unfold I.

  eapply steps_many.
  apply steps_S.

  eapply steps_once.
  apply steps_K.
Qed.

(* Master algorithm to derive a SKI combinator for any variable expresssion *)

(* Gets the alpha-eliminate variable n *)
Fixpoint alpha_elim (v : cexpr) (n: nat) : cexpr :=
  match v with
  | var m => if (eqb m n) then I else K + var m
  | S => (K + S)
  | K => (K + K)
  | va + vb => S + (alpha_elim va n) + (alpha_elim vb n)
  end.

Theorem steps_star_alpha_elim :
  forall c n, (alpha_elim c n) + var n ~>* c.
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

Lemma contains_var_eg : forall n,  ~ contains_var n I.
Proof.
  intros.
  unfold not.
  intros.
  inversion H; subst.
  inversion H1; subst.
  inversion H2; subst.
  inversion H2; subst.
  inversion H1; subst.
Qed.

Theorem alpha_elim_intros_no_vars : forall c n,
    ~contains_var n c -> forall m, ~contains_var n (alpha_elim c m).
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
    rewrite <- not_bcontains_var_contains_var in H.
    simpl in H.

    rewrite <- not_bcontains_var_contains_var in IHc1.
    rewrite <- not_bcontains_var_contains_var in IHc1.
    rewrite <- not_bcontains_var_contains_var in IHc2.
    rewrite <- not_bcontains_var_contains_var in IHc2.

    rewrite <- not_bcontains_var_contains_var.
    unfold alpha_elim.
    fold alpha_elim.
    simpl.

    apply Bool.orb_false_iff in H.
    destruct H.
    apply IHc1 in H.
    apply IHc2 in H0.

    rewrite H.
    rewrite H0.
    simpl.
    reflexivity.
Qed.

Theorem alpha_elim_removes_var :    
  forall c n, ~contains_var n (alpha_elim c n).
Proof.
  intro.
  induction c.
  *
    intros.
    rewrite <- not_bcontains_var_contains_var.
    simpl.

    destruct (PeanoNat.Nat.eq_decidable n n0).
    **
      subst.
      rewrite <- EqNat.beq_nat_refl.
      simpl.
      reflexivity.
    **
      apply PeanoNat.Nat.eqb_neq in H.
      rewrite H.
      simpl. rewrite H.
      reflexivity.
  *
    intros.
    rewrite <- not_bcontains_var_contains_var.
    auto.
  *
    intros.
    rewrite <- not_bcontains_var_contains_var.
    auto.
  *
    intros.
    rewrite <- not_bcontains_var_contains_var.
    simpl.

    Print Bool.
    rewrite Bool.orb_false_iff.
    split.

    rewrite not_bcontains_var_contains_var.
    apply IHc1.

    rewrite not_bcontains_var_contains_var.
    apply IHc2.
Qed.

(* Definition compile_1ary (c : cexpr) := alpha_elim c 0. *)
(* Definition compile_2ary (c : cexpr) := alpha_elim (alpha_elim c 1) 0. *)
(* Definition compile_3ary (c : cexpr) := alpha_elim (alpha_elim (alpha_elim c 2) 1) 0. *)

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

Theorem compile_nary_subterm_intros_no_vars : forall c x, ~ contains_var x c -> forall m n, ~ contains_var x (compile_nary_subterm n m c).
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

Theorem compile_nary_subterm_removes_vars : forall c m n k, k < m -> ~ contains_var (n + k) (compile_nary_subterm n m c).
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
      
Example ex1 : compile_nary_subterm 1 2 S = alpha_elim (alpha_elim S 2) 1.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem steps_star_compile_nary_subterm : forall m n c,
    compile_nary_subterm n (Datatypes.S m) c + var n ~>* compile_nary_subterm (Datatypes.S n) m c.
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
  | Datatypes.S n' => (add_vars c n') + var n'
  end.

Lemma add_vars_fold : forall c n, add_vars c n + var n = add_vars c (1+n).
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

Theorem steps_star_compile_nary (c : cexpr) : forall n c, add_vars (compile_nary (Datatypes.S n) c) (Datatypes.S n) ~>* c.
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
    ~contains_var n c -> ~contains_var n (compile_nary m c).
Proof.
  intros.
  unfold compile_nary.
  apply compile_nary_subterm_intros_no_vars.
  assumption.
Qed.

Theorem compile_nary_removes_vars : forall n m, m < n -> (forall c, ~ contains_var m (compile_nary n c)).
Proof.
  intros.
  unfold compile_nary.
  assert (m = 0 + m)%nat by lia.
  rewrite H0.
  apply compile_nary_subterm_removes_vars.
  assumption.
Qed.

Definition fmap_ub (f : fmap) (ub : nat) := forall n, ub <= n -> f n = None.

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

Definition fmap_1ary (x : cexpr) := (0 !-> x, __).
Definition fmap_2ary (x y : cexpr) := (0 !-> x, 1 !-> y, __).
Definition fmap_3ary (x y z : cexpr) := (0 !-> x, 1 !-> y, 2 !-> z, __).

Fixpoint binding_type n := 
  match n with
  | 0 => fmap
  | Datatypes.S n' => cexpr -> (binding_type n')
  end.

(* Take a binding and and assign v !-> c after doing bindings *)
Fixpoint binding_assn n (binding : binding_type n) (v : nat) (c : cexpr) : binding_type n :=
  (match n as n0 return (binding_type n0 -> binding_type n0) with
   | 0 => fun b => fmap_assn b v c
   | Datatypes.S n' => fun b => fun s => binding_assn n' (b s) v c
   end) binding.

Fixpoint binding_nary_pre n start : binding_type n :=
  match n with
  | 0 => __
  | Datatypes.S n' => fun c => binding_assn n' (binding_nary_pre n' (Datatypes.S start)) start c
  end.

Definition binding_nary n := binding_nary_pre n 0.

Lemma binding_1ary_spec : forall x, binding_nary 1 x = (0 !-> x, __).
Proof.
  intros.
  unfold binding_nary. simpl. reflexivity.
Qed.

Lemma binding_2ary_spec : forall x y, binding_nary 2 x y = (0 !-> x, 1 !-> y, __).
Proof.
  intros.
  unfold binding_nary. simpl. reflexivity.
Qed.

Lemma binding_3ary_spec : forall x y z, binding_nary 3 x y z = (0 !-> x, 1 !-> y, 2 !-> z, __).
Proof.
  intros.
  unfold binding_nary. simpl. reflexivity.
Qed.

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

Theorem steps_star_compile_1ary : forall c x, compile_nary 1 c + x ~>* (c ; fmap_1ary x).
Proof.
  intros.
  
  assert (compile_nary 1 c + x = (compile_nary 1 c + var 0; (0 !-> x, __))). {
    simpl.
    rewrite subst_disjoint.
    reflexivity.

    apply compile_nary_disjoint_fmap_lb.
    apply fmap_1ary_ub.
  }

  rewrite H.
  apply steps_star_subst.
  apply steps_star_alpha_elim.
Qed.

Theorem steps_star_compile_2ary : forall c x y, compile_nary 2 c + x + y ~>* (c ; (fmap_2ary x y)).
Proof.
  intros.

  assert (compile_nary 2 c + x + y = (compile_nary 2 c + var 0 + var 1 ; (fmap_2ary x y) )). {
    simpl.
    rewrite subst_disjoint.
    reflexivity.

    apply compile_nary_disjoint_fmap_lb.
    apply fmap_2ary_ub.
  }

  rewrite H.

  eapply steps_star_subst.
  assert (compile_nary 2 c + var 0  + var 1 = add_vars (compile_nary 2 c) 2). {
    simpl.
    reflexivity.
  }

  rewrite H0.
  apply (steps_star_compile_nary c).
Qed.

Theorem steps_star_compile_3ary : forall c x y z, compile_nary 3 c + x + y + z ~>* (c ; (fmap_3ary x y z)).
Proof.
  intros.

  assert (compile_nary 3 c + x + y + z = (compile_nary 3 c + var 0 + var 1 + var 2 ; (fmap_3ary x y z) )). {
    simpl.
    rewrite subst_disjoint.
    reflexivity.

    apply compile_nary_disjoint_fmap_lb.
    apply fmap_3ary_ub.
  }

  rewrite H.

  eapply steps_star_subst.
  assert (compile_nary 3 c + var 0  + var 1 + var 2 = add_vars (compile_nary 3 c) 3). {
    simpl.
    reflexivity.
  }

  rewrite H0.
  apply (steps_star_compile_nary c).
Qed.


(* Deriving B M T basis from S K I *)
Definition T : cexpr := S + (K + (S + I)) + K.

Theorem steps_star_T : forall x y, (T + x + y) ~>* (y + x).
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

Definition B : cexpr := S + (K + S) + K.

Theorem steps_star_B : forall x y z, B + x + y + z ~>* x + (y + z).
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

Definition M : cexpr := S + I + I.

Theorem steps_star_M : forall x, M + x ~>* x + x.
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
Definition C : cexpr := B + (T + (B + B + T)) + (B + B + T).

Theorem steps_star_C : forall x y z, C + x + y + z ~>* x + z + y.
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
Definition L : cexpr := C + B + M.

Theorem steps_star_L : forall x y, L + x + y ~>* x + (y + y).
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

Definition sage c := L + c + (L + c).

Theorem sage_intros_no_vars : forall c n, ~contains_var n c -> ~contains_var n (sage c).
Proof.
  intros.
  apply not_bcontains_var_contains_var.
  apply not_bcontains_var_contains_var in H.
  simpl.
  rewrite H.
  simpl.
  reflexivity.
Qed.

Theorem steps_star_sage : forall c, sage c ~>* c + (sage c).
Proof.
  intros.
  unfold sage.
  apply steps_star_L.
Qed.

Definition V : cexpr := B + C + T.

Theorem steps_star_V : forall x y z, V + x + y + z ~>* z + x + y.
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

Theorem steps_star_t : forall p q, t + p + q ~>* p.
Proof.
  intros.
  unfold t.
  apply steps_once.
  apply steps_K.
Qed.

Definition f : cexpr := K + I.

Theorem steps_star_f : forall p q, f + p + q ~>* q.
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

Definition nxt : cexpr := V + f.
Definition prv : cexpr := T + f.
Definition zro : cexpr := I.

Fixpoint rep (n: nat) :=
  match n with
  | 0 => zro
  | Datatypes.S m => nxt + (rep m)
  end.

Theorem prv_nxt : forall n, prv + (rep (1 + n)) ~>* rep n.
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

(* Representatives of positive integers are not equivalent to zro *)
Theorem nequiv_repSn_zro : forall n, rep (Datatypes.S n) ~/= zro.
Proof.
  unfold not.
  intros.
  simpl in H.
  unfold nxt in H.
  assert (V + f + rep n + K ~= I + K) as H0. {
    apply equiv_app_l.
    assumption.
  }
  assert (K + I ~= K) as H1. {
    eapply equiv_trans.
    apply equiv_sym.
    apply equiv_steps.
    apply steps_K.

    eapply equiv_trans.
    apply equiv_sym.
    apply equiv_steps_star.
    apply steps_star_V.

    eapply equiv_trans.
    apply H0.

    apply equiv_steps_star.
    apply steps_star_I.
  }

  eapply nequiv_K_Kx.
  apply equiv_sym.
  apply H1.
Qed.

Lemma equiv_repSm_repSn_imp :
  forall n m, rep (Datatypes.S n) ~= rep (Datatypes.S m) <->
              rep n ~= rep m.
Proof.
  split; intros.
  *
    simpl in H.
    unfold nxt in H.

    assert (V + f + rep n + f ~= V + f + rep m + f). {
      apply equiv_app_l. assumption.
    }

    assert (f + f + rep n ~= f + f + rep m). {
      eapply equiv_trans.
      apply equiv_sym.
      apply equiv_steps_star.
      apply steps_star_V.

      eapply equiv_trans.
      apply H0.
      apply equiv_steps_star.
      apply steps_star_V.
    }

    eapply equiv_trans.
    apply equiv_sym.
    apply equiv_steps_star.
    apply steps_star_f.

    eapply equiv_trans.
    apply H1.

    apply equiv_steps_star.
    apply steps_star_f.
  *
    simpl.
    unfold nxt.
    apply equiv_app_r.
    assumption.
Qed.

(* Representatives of different integers are not equivalent *)
Theorem nequiv_repn_repm : forall n m : nat, n < m -> rep n ~/= rep m.
Proof.
  intros.

  assert (exists (m' : nat), m = n + (Datatypes.S m'))%nat. {
    exists (m - n - 1).
    lia.
  }

  destruct H0.
  subst.

  clear H.

  induction n.
  *
    unfold not.
    intro.
    eapply nequiv_repSn_zro.
    simpl in H. simpl.
    apply equiv_sym.
    apply H.
  *
    unfold not.
    intro.

    rewrite plus_Sn_m in H.
    rewrite equiv_repSm_repSn_imp in H.
    apply IHn. apply H.
Qed.

(* So now we know every nat has a different representation. *)

(* Decidability of a set of natural numbers *)
Definition decides (c : cexpr) (P : nat -> Prop) :=
  forall n, (P n -> c + (rep n) ~>* t) /\ ((~ P n) -> c + (rep n) ~>* f).

Definition decidable (P : nat -> Prop) := exists c, decides c P.

Definition computes (f : nat -> nat) (c : cexpr) := forall n1 n2, c + rep (f n1) ~>* rep n2.

(* Now we can make some arithmetic operators *)

(* zero test *)
Definition eq_zro : cexpr := T + t.

Theorem eq_zro_decides : decides eq_zro (fun n => n = 0).
Proof.
  unfold decides.
  intros.
  split;
    intros;
    subst;
    simpl;
    unfold eq_zro.

  *
    eapply steps_star_trans.
    apply steps_star_T.
    apply steps_star_I.
  *
    eapply steps_star_trans.
    apply steps_star_T.
    destruct n. contradiction.
    simpl.
    unfold nxt.
    eapply steps_star_trans.
    apply steps_star_V.
    apply steps_star_t.
Qed.

Theorem steps_star_eq_zro_Sn : forall n, eq_zro + rep (Datatypes.S n) ~>* f.
Proof.
  intros.
  Check eq_zro_decides.
  destruct (eq_zro_decides (Datatypes.S n)).
  apply H0.
  lia.
Qed.

Theorem steps_star_eq_zro_0 : eq_zro + rep 0 ~>* t.
Proof.
  intros.
  Check eq_zro_decides.
  destruct (eq_zro_decides 0).
  apply H.
  lia.
Qed.

(* P a m = Z m b ( nxt ( a (prv m) ) ) *)
(* P a m = Z m b ( rec ( 0 ) ) *)
(* P 0 1  = Z 1 b ( nxt ( 0 ( prv 1 ) ) ) *)

Definition pre_recursive_combinator_action1 (b : nat) (r : cexpr) :=
  eq_zro + (var 1) + rep b + (r ; (0 !-> (var 0 + (prv + var 1)), __)).

Definition pre_recursive_combinator_action2 (b : cexpr) (r : cexpr) :=
  eq_zro + (var 1) + b + (r ; (0 !-> (var 0 + (prv + var 1) + var 2), __)).

Definition pre_recursive_combinator1 (b : nat) (r : cexpr) :=
  compile_nary 2 (pre_recursive_combinator_action1 b r).

Definition pre_recursive_combinator2 (b : cexpr) (r : cexpr) :=
  compile_nary 3 (pre_recursive_combinator_action2 b r).

Definition recursive_combinator1 (b : nat) (r : cexpr) :=
  sage (pre_recursive_combinator1 b r).

Definition recursive_combinator2 (b : cexpr) (r : cexpr) :=
  sage (pre_recursive_combinator2 b r).

Lemma not_contains_var_rep_n : forall n m, ~ contains_var m (rep n).
Proof.
  intro n.
  induction n.
  *
    intros.
    apply not_bcontains_var_contains_var.
    simpl. reflexivity.
  *
    intros.
    apply not_bcontains_var_contains_var.
    simpl.
    apply <- not_bcontains_var_contains_var.
    apply IHn.
Qed.

Lemma pre_recursive_combinator2_intros_no_vars :
  forall b r n, ~contains_var n b -> ~contains_var n r -> ~contains_var n (pre_recursive_combinator2 b r).
Proof.
  intros.
  unfold pre_recursive_combinator2.
  assert (n < 3 \/ 3 <= n) by lia.
  destruct H1.
  apply compile_nary_removes_vars.
  assumption.
  apply compile_nary_intros_no_vars.
  unfold pre_recursive_combinator_action2.
  destruct n. assert (1 = 0) as contra by lia. inversion contra.
  destruct n. assert (1 = 0) as contra by lia. inversion contra.
  destruct n. assert (1 = 0) as contra by lia. inversion contra.
  apply not_bcontains_var_contains_var.
  simpl.
  apply not_bcontains_var_contains_var in H.
  apply not_bcontains_var_contains_var in H0.
  rewrite H.
  simpl.
  induction r.
  *
    destruct (PeanoNat.Nat.eq_decidable n0 0).
    subst. simpl. reflexivity.
    unfold fmap_assn.
    simpl.
    apply PeanoNat.Nat.eqb_neq in H2. rewrite H2.
    simpl.
    simpl in H0. assumption.
  *
    simpl. reflexivity.
  *
    simpl. reflexivity.
  *
    simpl.
    rewrite IHr1.
    rewrite IHr2. simpl. reflexivity.
    simpl in H0.
    apply Bool.orb_false_iff in H0.
    destruct H0.
    apply H2.
    simpl in H0.
    apply Bool.orb_false_iff in H0.
    destruct H0.
    apply H0.
Qed.

Lemma recursive_combinator2_intros_no_vars :
  forall b r n, ~contains_var n b -> ~contains_var n r -> ~contains_var n (recursive_combinator2 b r).
Proof.
  intros.
  unfold recursive_combinator2.
  apply sage_intros_no_vars.
  apply pre_recursive_combinator2_intros_no_vars.
  auto. auto.
Qed.

Lemma recursive_combinator2_removes_vars :
  forall b r n, n < 3 -> ~contains_var n b -> ~contains_var n (recursive_combinator2 b r).
Proof.
  intros.
  unfold recursive_combinator2.
  apply sage_intros_no_vars.
  unfold pre_recursive_combinator2.
  apply compile_nary_removes_vars.
  assumption.
Qed.

Theorem steps_star_recursive_combinator1_base (base_case : nat) (rec : cexpr) :
  (recursive_combinator1 base_case rec) + rep 0 ~>* rep base_case.
Proof.
  unfold recursive_combinator1.
  eapply steps_star_trans.
  apply steps_star_app_l.
  eapply steps_star_sage.

  eapply steps_star_trans.
  apply steps_star_compile_2ary.

  unfold pre_recursive_combinator_action1.
  simpl.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_star_eq_zro_0.

  eapply steps_star_eq.
  apply steps_star_t.

  apply subst_disjoint.
  unfold disjoint_cexpr_fmap.
  intros.

  exfalso.
  eapply not_contains_var_rep_n.
  apply H.
Qed.

Theorem steps_star_recursive_combinator2_base (base_case : cexpr) (rec : cexpr) (m : cexpr) :
  ~contains_var 0 base_case -> ~contains_var 1 base_case ->
  (recursive_combinator2 base_case rec) + rep 0 + m  ~>* (base_case; (2 !-> m, __)).
Proof.
  intros.
  unfold recursive_combinator2.
  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_app_l.
  eapply steps_star_sage.

  eapply steps_star_trans.
  eapply steps_star_compile_3ary.

  unfold pre_recursive_combinator_action2.
  simpl.

  eapply steps_star_trans.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_star_eq_zro_0.

  eapply steps_star_eq.
  apply steps_star_t.

  unfold fmap_3ary.

  assert (forall c c0 c1 c2 f, ~contains_var 0 c -> ~contains_var 1 c -> c ; (0 !-> c0, 1 !-> c1, 2 !-> c2, f) = c; (2 !-> c2, f)).
  {
    clear H H0 base_case rec m.
    intro c.
    induction c.
    *
      intros.
      apply not_bcontains_var_contains_var in H. simpl in H.
      apply not_bcontains_var_contains_var in H0. simpl in H0.
      unfold fmap_assn.
      simpl. rewrite H. rewrite H0. reflexivity.
    *
      intros.
      simpl. reflexivity.
    *
      intros.
      simpl. reflexivity.
    *
      intros.
      simpl.
      rewrite IHc1.
      rewrite IHc2. reflexivity.

      apply not_bcontains_var_contains_var in H; simpl in H.
      apply Bool.orb_false_iff in H.
      inversion H.
      apply not_bcontains_var_contains_var in H2. assumption.

      apply not_bcontains_var_contains_var in H0. simpl in H0.
      apply Bool.orb_false_iff in H0.
      inversion H0.
      apply not_bcontains_var_contains_var in H2. assumption.

      apply not_bcontains_var_contains_var in H. simpl in H.
      apply Bool.orb_false_iff in H.
      inversion H.
      apply not_bcontains_var_contains_var in H1. assumption.

      apply not_bcontains_var_contains_var in H0. simpl in H0.
      apply Bool.orb_false_iff in H0.
      inversion H0.
      apply not_bcontains_var_contains_var in H1. assumption.      
  }

  apply H1. assumption. assumption.
Qed.

Lemma nxt_repn_eq_repSn : forall n, nxt + rep n = rep (Datatypes.S n).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma steps_star_rec_subst_subst1 :
  forall r a m,
    ((r ; (0 !-> var 0 + (prv + var 1), __)) ; (0 !-> a, 1 !-> m, __)) = (r ; (0 !-> (a + (prv + m)), 1 !-> m,  __)).
Proof.
  intros.
  induction r.
  *
    destruct n.
    simpl. reflexivity.

    destruct n.
    simpl. reflexivity.

    simpl. reflexivity.
  *
    simpl. reflexivity.
  *
    simpl. reflexivity.
  *
    simpl. rewrite IHr1. rewrite IHr2. reflexivity.
Qed.

Lemma steps_star_rec_subst_subst2 :
  forall r a m n,
    ((r ; (0 !-> var 0 + (prv + var 1) + var 2, __)) ; (0 !-> a, 1 !-> m, 2 !-> n, __)) = (r ; (0 !-> (a + (prv + m) + n), 1 !-> m,  2 !-> n, __)).
Proof.
  intros.
  induction r.
  *
    destruct n0.
    simpl. reflexivity.

    destruct n0.
    simpl. reflexivity.

    destruct n0.
    simpl. reflexivity.

    simpl. reflexivity.
  *
    simpl. reflexivity.
  *
    simpl. reflexivity.
  *
    simpl. rewrite IHr1. rewrite IHr2. reflexivity.
Qed.


Theorem steps_star_subst_alt : forall c c1 c2 f n,
    c1 ~>* c2 -> (c ; (n !-> c1, f)) ~>* (c ; (n !-> c2, f)).
Proof.
  intros.
  induction c.
  *
    destruct (PeanoNat.Nat.eq_decidable n0 n).
    **
      subst.
      unfold fmap_assn.
      simpl.
      rewrite PeanoNat.Nat.eqb_refl.
      assumption.
    **
      unfold fmap_assn.
      simpl.
      apply PeanoNat.Nat.eqb_neq in H0.
      rewrite H0.
      apply steps_none.
  *
    simpl. apply steps_none.
  *
    simpl. apply steps_none.
  *
    simpl.
    eapply steps_star_trans.
    apply steps_star_app_l.
    apply IHc1.
    apply steps_star_app_r.
    apply IHc2.
Qed.

(* Theorem fmap_assn_swap : forall c c1 c2 f m n, *)
(*     m <> n -> *)
(*     ~contains_var n c2 -> *)
(*     (c ; (n !-> c1, m !-> c2, f)) = (c ; (m !-> c2, n !-> c1, f)). *)
(* Proof. *)
(*   intros. *)
(*   induction c. *)
(*   * *)
(*     destruct (PeanoNat.Nat.eq_decidable n0 m). *)
(*     ** *)
(*       subst. *)
(*       unfold fmap_assn. simpl. *)
(*       apply PeanoNat.Nat.eqb_neq in H. rewrite H. *)
(*       rewrite PeanoNat.Nat.eqb_refl. *)
(*       reflexivity. *)
(*     ** *)
(*       destruct (PeanoNat.Nat.eq_decidable n0 n). *)
(*       *** *)
(*         subst. *)
(*         unfold fmap_assn. simpl. *)
(*         rewrite PeanoNat.Nat.eqb_refl. *)
(*         apply PeanoNat.Nat.eqb_neq in H1. *)
(*         rewrite H1. *)
(*         reflexivity. *)
(*       *** *)
(*         apply PeanoNat.Nat.eqb_neq in H1. *)
(*         apply PeanoNat.Nat.eqb_neq in H2. *)
(*         unfold fmap_assn. simpl. rewrite H1. rewrite H2. *)
(*         reflexivity. *)
(*   * *)
(*     simpl. reflexivity. *)
(*   * *)
(*     simpl. reflexivity. *)
(*   * *)
(*     simpl. *)
(*     rewrite IHc1. *)
(*     rewrite IHc2. *)
(*     reflexivity. *)
(* Qed. *)

Theorem steps_star_recursive_combinator1_recursive (base_case : nat) (rec : cexpr) :
  forall n, (recursive_combinator1 base_case rec) + rep (Datatypes.S n) ~>*
            (rec ; (0 !-> (recursive_combinator1 base_case rec) + rep n, 1 !-> rep (Datatypes.S n), __)).
Proof.
  intros.
  unfold recursive_combinator1.
  eapply steps_star_trans.
  eapply steps_star_app_l.
  apply steps_star_sage.
  unfold pre_recursive_combinator1.
  eapply steps_star_trans.
  apply steps_star_compile_2ary.
  unfold fmap_2ary.

  unfold pre_recursive_combinator_action1.
  eapply steps_star_trans.
  simpl.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_star_eq_zro_Sn.

  eapply steps_star_trans.
  apply steps_star_f.

  rewrite steps_star_rec_subst_subst1.
  
  apply steps_star_subst_alt.
  apply steps_star_app_r.
  apply prv_nxt.
Qed.

Theorem steps_star_recursive_combinator2_recursive (base_case : cexpr) (rec : cexpr) :
  forall n m,
    ~contains_var 0 base_case -> ~contains_var 1 base_case ->
    (recursive_combinator2 base_case rec) + rep (Datatypes.S n) + rep m ~>*
            (rec ; (0 !-> (recursive_combinator2 base_case rec) + rep n + rep m, 1 !-> rep (Datatypes.S n), 2 !-> rep m, __)).
Proof.
  intros.
  unfold recursive_combinator2.
  eapply steps_star_trans.
  eapply steps_star_app_l.
  eapply steps_star_app_l.
  apply steps_star_sage.
  unfold pre_recursive_combinator2.
  eapply steps_star_trans.
  apply steps_star_compile_3ary.
  unfold fmap_3ary.

  unfold pre_recursive_combinator_action2.
  eapply steps_star_trans.
  simpl.
  apply steps_star_app_l.
  apply steps_star_app_l.
  apply steps_star_eq_zro_Sn.

  eapply steps_star_trans.
  apply steps_star_f.

  rewrite steps_star_rec_subst_subst2.
  
  apply steps_star_subst_alt.
  apply steps_star_app_l.
  apply steps_star_app_r.
  apply prv_nxt.
Qed.
  
Definition recurses1 (f : nat -> nat) rec :=
  forall n, (rec ; (0 !-> rep (f n), 1 !-> rep (Datatypes.S n),  __)) ~>* rep (f (Datatypes.S n)).

Definition recurses2 (f : nat -> nat -> nat) base rec :=
  ~contains_var 0 base /\
  ~contains_var 1 base /\
  (forall m, (base ; (2 !-> rep m, __)) ~>* rep (f 0 m)) /\
  forall n m, (rec ; (0 !-> rep (f n m), 1 !-> rep (Datatypes.S n), 2 !-> rep m,  __)) ~>* rep (f (Datatypes.S n) m).

Theorem fixpoint_principle1 :
  forall (f : nat -> nat) rec, recurses1 f rec ->
                               forall n,
                                 recursive_combinator1 (f 0) rec + rep n ~>* rep (f n).
Proof.
  intros.
  induction n.
  *
    apply steps_star_recursive_combinator1_base.
  *
    eapply steps_star_trans.
    apply steps_star_recursive_combinator1_recursive.
    eapply steps_star_trans.
    eapply steps_star_subst_alt.
    apply IHn.
    apply H.
Qed.

Theorem fixpoint_principle2 :
  forall (f : nat -> nat -> nat) base rec,
    recurses2 f base rec ->
    forall n m,
      recursive_combinator2 base rec + rep n + rep m ~>* rep (f n m).
Proof.
  intros.
  destruct H. destruct H0. destruct H1.
  induction n.
  *
    eapply steps_star_trans.
    apply steps_star_recursive_combinator2_base.
    assumption. assumption. apply H1.
  *
    eapply steps_star_trans.
    apply steps_star_recursive_combinator2_recursive.
    assumption. assumption.

    eapply steps_star_trans.
    eapply steps_star_subst_alt.
    apply IHn.
    apply H2.
Qed.    

(* The op that adds n to every input *)
Definition add_m_n_base := var 2. 
Definition add_m_n_rec := nxt + var 0.
Definition add_m_n_op := (recursive_combinator2 add_m_n_base add_m_n_rec).
Theorem add_m_n_works : forall m n, add_m_n_op + (rep m) + (rep n) ~>* rep (m + n).
Proof.
  intros.
  pose (fun m' n' => (m' + n')%nat) as f.
  eapply steps_star_trans.
  unfold add_m_n_op.

  eapply fixpoint_principle2.
  unfold recurses2.
  split.
  apply not_bcontains_var_contains_var. simpl. reflexivity.
  split.
  apply not_bcontains_var_contains_var. simpl. reflexivity.
  split.
  intros.
  simpl.
  assert (f 0 m0 = m0) by reflexivity.
  rewrite H.
  apply steps_none.

  intros.
  unfold add_m_n_rec.
  simpl.
  apply steps_none.

  unfold f.
  apply steps_none.
Qed.

Theorem add_m_n_op_contains_no_vars : forall n, ~contains_var n (add_m_n_op).
Proof.
  intros.
  rewrite <- not_bcontains_var_contains_var.
  simpl.
  reflexivity.
Qed.

(* The op that muls inputs together *)
Definition mul_m_n_base := rep 0. 
Definition mul_m_n_rec := add_m_n_op + var 0 (* (m-1)n *) + var 2 (* n *).
Definition mul_m_n_op := (recursive_combinator2 mul_m_n_base mul_m_n_rec).

Theorem mul_m_n_op_contains_no_vars :
  forall n, ~contains_var n mul_m_n_op.
Proof.
  intros.
  unfold mul_m_n_op.
  assert (n < 3 \/ 3 <= n) by lia.
  destruct H.
  *
    apply recursive_combinator2_removes_vars. assumption.
    unfold mul_m_n_base.
    apply not_bcontains_var_contains_var.
    simpl. reflexivity.
  *
    apply recursive_combinator2_intros_no_vars.
    unfold mul_m_n_base.
    apply not_bcontains_var_contains_var. simpl. reflexivity.
    unfold mul_m_n_rec.
    apply not_bcontains_var_contains_var.
    unfold bcontains_var.
    fold bcontains_var.
    assert (bcontains_var n add_m_n_op = false). {
      apply not_bcontains_var_contains_var.
      apply add_m_n_op_contains_no_vars.
    }
    rewrite H0.
    destruct n. assert (1 = 0) as contra by lia. inversion contra.
    destruct n. assert (1 = 0) as contra by lia. inversion contra.
    destruct n. assert (1 = 0) as contra by lia. inversion contra.
    simpl. reflexivity.
Qed.
  
Theorem mul_m_n_works : forall m n, mul_m_n_op + (rep m) + (rep n) ~>* rep (m * n).
Proof.
  intros.
  pose (fun m' n' => (m' * n')%nat) as f.
  eapply steps_star_trans.
  unfold mul_m_n_op.

  eapply fixpoint_principle2.
  unfold recurses2.
  split.
  apply not_bcontains_var_contains_var. simpl. reflexivity.
  split.
  apply not_bcontains_var_contains_var. simpl. reflexivity.
  split.
  intros.
  simpl.
  assert (f 0 m0 = 0) by reflexivity.
  rewrite H.
  apply steps_none.

  intros.
  unfold mul_m_n_rec.

  assert (add_m_n_op + var 0 + var 2; (0 !-> rep (f n0 m0), 1 !-> rep (Datatypes.S n0), 2 !-> rep m0, __) = add_m_n_op + rep (f n0 m0) + rep m0). {
    reflexivity.
  }
  rewrite H.
  eapply steps_star_eq.
  apply add_m_n_works.
  unfold f.
  assert (n0 * m0 + m0 = Datatypes.S n0 * m0)%nat by lia.
  rewrite H0.
  reflexivity.
  unfold f.

  apply steps_none.
Qed.

Definition pow_n_m_base := rep 1. 
Definition pow_n_m_rec := mul_m_n_op + var 0 (* n^(m-1) *) + var 2 (* n *).
Definition pow_n_m_op := (recursive_combinator2 pow_n_m_base pow_n_m_rec).

Theorem pow_n_m_op_contains_no_vars :
  forall n, ~contains_var n pow_n_m_op.
Proof.
  intros.
  unfold pow_n_m_op.
  assert (n < 3 \/ 3 <= n) by lia.
  destruct H.
  *
    apply recursive_combinator2_removes_vars. assumption.
    unfold pow_n_m_base.
    apply not_bcontains_var_contains_var.
    simpl. reflexivity.
  *
    apply recursive_combinator2_intros_no_vars.
    unfold pow_n_m_base.
    apply not_bcontains_var_contains_var. simpl. reflexivity.
    unfold pow_n_m_rec.
    apply not_bcontains_var_contains_var.
    unfold bcontains_var.
    fold bcontains_var.
    assert (bcontains_var n mul_m_n_op = false). {
      apply not_bcontains_var_contains_var.
      apply mul_m_n_op_contains_no_vars.
    }
    rewrite H0.
    destruct n. assert (1 = 0) as contra by lia. inversion contra.
    destruct n. assert (1 = 0) as contra by lia. inversion contra.
    destruct n. assert (1 = 0) as contra by lia. inversion contra.
    simpl. reflexivity.
Qed.

Theorem pow_n_m_works : forall m n, pow_n_m_op + (rep m) + (rep n) ~>* rep (pow n m).
Proof.
  intros.
  pose (fun m' n' => (pow n' m')%nat) as f.
  eapply steps_star_trans.
  unfold pow_n_m_op.

  eapply fixpoint_principle2.
  unfold recurses2.
  split.
  apply not_bcontains_var_contains_var. simpl. reflexivity.
  split.
  apply not_bcontains_var_contains_var. simpl. reflexivity.
  split.
  intros.
  unfold pow_n_m_base.
  assert (f 0 m0 = 1) by reflexivity.
  rewrite H.
  apply steps_none.

  intros.
  unfold pow_n_m_rec.
  rewrite subst_app_distr.
  rewrite subst_app_distr.

  assert (forall f, mul_m_n_op ; f = mul_m_n_op). {
    intros.
    apply subst_disjoint.
    unfold disjoint_cexpr_fmap.
    intros.
    apply mul_m_n_op_contains_no_vars in H.
    exfalso. apply H.
  }

  rewrite H.
  assert (var 0; (0 !-> rep (f n0 m0), 1 !-> rep (Datatypes.S n0), 2 !-> rep m0, __) = rep (f n0 m0)). {
    reflexivity.
  }
  rewrite H0.

  assert (var 2; (0 !-> rep (f n0 m0), 1 !-> rep (Datatypes.S n0), 2 !-> rep m0, __) = rep m0) by reflexivity.
  rewrite H1.

  eapply steps_star_eq.
  apply mul_m_n_works.
  unfold f.

  unfold pow. fold pow.
  Search (_ * _ = _ * _)%nat.
  rewrite PeanoNat.Nat.mul_comm.
  reflexivity.

  apply steps_none.
Qed.

Definition pow_m_n_op := C + pow_n_m_op.
Theorem pow_m_n_op_works : forall m n, pow_m_n_op + (rep m) + (rep n) ~>* rep (pow m n).
Proof.
  intros.
  unfold pow_m_n_op.
  eapply steps_star_trans.
  apply steps_star_C.
  apply pow_n_m_works.
Qed.

(* length measuring *)



Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Fixpoint godel_number_l (c : cexpr) : list nat :=
  match c with
  | S => [ 1 ]
  | K => [ 2 ]
  | app c1 c2 => [3] ++ (godel_number_l c1) ++ (godel_number_l c2) ++ [4]
  end.

Fixpoint concat_l (l : list nat) : nat :=
  match l with
  | nil => 0
  | cons x l' => let e := length l' in ((pow 10 e) * x) + (concat_l l')
  end.

(* Do not try to compute this. It crashes Coq *)
Definition godel_number (c : cexpr) : nat :=
  concat_l (godel_number_l c).

(* Definition of computable set of numbers *)
Definition computable (p : nat -> Prop) := exists A, forall n, A (rep n) ~>* t <-> p n.

(* A number is truthy if it is the godel number of an expression that reduces to t *)
Definition is_truthy (n : nat) := exists c : cexpr, n = godel_number c /\ c ~= t.

(* Are truthy numbers computable? *)
Theorem godel_incompletness : ~ computable is_truthy.










Definition sage (c : cexpr) := L + c + (L + c).

Theorem fixed_point_0 : forall c, (sage c) ~>* c + (sage c).
Proof.
  intros.
  unfold sage.
  apply steps_star_L.
Qed.


