Require Import SKI.expr.
Import Nat.

Definition fmap := nat -> option expr.
Definition fmap_empty : fmap := fun n => None.
Definition fmap_assn (f: fmap) (n: nat) (c: expr) :=
  fun m => if m =? n then Some c else f m.
Definition fmap_del (f: fmap) (n: nat) :=
  fun m => if m =? n then None else f m.

Notation "'--'" := (fmap_empty).
Notation "n '<<-' c ',' f" := (fmap_assn f n c)
                                (at level 100, c at next level, right associativity).


Fixpoint csubst (c : expr) (f: fmap) :=
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

Definition disjoint_expr_fmap (c : expr) (f: fmap) :=
  forall n, n IN c -> f n = None.

Theorem subst_disjoint : forall c f, disjoint_expr_fmap c f -> (c <-- f) = c.
Proof.
  intros.
  induction c.
  *
    simpl.
    unfold disjoint_expr_fmap in H.
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

    unfold disjoint_expr_fmap.
    intros.
    unfold disjoint_expr_fmap in H.
    apply H.
    apply contains_right. assumption.

    unfold disjoint_expr_fmap.
    intros.
    unfold disjoint_expr_fmap in H.
    apply H.
    apply contains_left. assumption.
Qed.

Theorem subst_const : forall c f, is_const c -> c <-- f = c.
Proof.
  intros.
  apply subst_disjoint.
  unfold disjoint_expr_fmap.
  intros.
  apply H in H0.
  contradiction H0.
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
