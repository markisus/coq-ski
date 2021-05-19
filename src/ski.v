(* S K combinators *)
Inductive expr :=
| S : expr
| K : expr
| app : expr -> expr -> expr.

Notation " a [+] b " := (app a b) (at level 50, left associativity).

(* Rewrite rules *)
Inductive steps : expr -> expr -> Prop :=
| steps_S : forall x y z, steps (S [+] x [+] y [+] z) (x [+] z [+] (y [+] z))
| steps_K : forall x y, steps (K [+] x [+] y) x
| steps_app_l : forall x y z, steps x y -> steps (x [+] z) (y [+] z)
| steps_app_r : forall x y z, steps x y -> steps (z [+] x) (z [+] y).

Notation " a ~> b " := (steps a b) (at level 55, left associativity).

(* Transitive closure of steps *)
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
