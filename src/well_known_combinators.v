Require Import SKI.expr.
Require Coq.Setoids.Setoid.

Definition I : expr := S [+] K [+] K.

Theorem steps_star_I : forall c, (I [+] c) ~>* c.
Proof.
  intro.
  unfold I.

  eapply steps_many.
  apply steps_S.

  eapply steps_once.
  apply steps_K.
Qed.

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

Theorem is_const_I : is_const I.
Proof.
  unfold I.
  generalize (is_const_S).
  generalize (is_const_K).
  intros.
  apply is_const_app_iff. split.
  apply is_const_app_iff. split.
  auto.
  auto.
  auto.
Qed.

(* Deriving B M T basis from S K I *)
Definition T : expr := S [+] (K [+] (S [+] I)) [+] K.

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

Definition B : expr := S [+] (K [+] S) [+] K.

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

Definition M : expr := S [+] I [+] I.

Theorem is_const_M : is_const M.
Proof.
  unfold M.
  apply is_const_app_iff. split.
  apply is_const_app_iff. split.
  apply is_const_S.
  apply is_const_I.
  apply is_const_I.
Qed.

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
Definition C : expr := B [+] (T [+] (B [+] B [+] T)) [+] (B [+] B [+] T).

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
Definition L : expr := C [+] B [+] M.

Theorem is_const_L : is_const L.
Proof.
  unfold L.
  apply is_const_app_iff. split.
  apply is_const_app_iff. split.
  apply is_const_C.
  apply is_const_B.
  apply is_const_M.
Qed.

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

Definition V : expr := B [+] C [+] T.

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
Definition t : expr := K.

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
  unfold t.
  apply is_const_K.
Qed.

Definition f : expr := K [+] I.

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
  unfold f.
  apply is_const_app_iff.
  split.
  apply is_const_K.
  apply is_const_I.
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

Definition sage c := L [+] c [+] (L [+] c).

Theorem sage_intros_no_vars : forall c n, ~ n IN c -> ~ n IN (sage c).
Proof.
  intros.
  unfold sage.
  generalize (is_const_C). intros.
  generalize (is_const_L). intros.
  apply not_contains_var_app_iff. split.
  apply not_contains_var_app_iff. split.
  auto. auto.
  apply not_contains_var_app_iff. split.
  auto. auto.
Qed.

Theorem steps_star_sage : forall c, sage c ~>* c [+] (sage c).
Proof.
  intros.
  unfold sage.
  apply steps_star_L.
Qed.

