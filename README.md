Build
----
coq_makefile -f _CoqProject src/*.v -o Makefile  
make

Walkthrough
----------
The documentation below describes the main theorem statements and definitions of this development.
The proofs are found within the source. The proofs are adapted from Raymond Smullyan's "To Mock a Mockingbird".

The SKI Combinators
------------------
```
(* src/expr.v *)

Inductive expr :=
| var : nat -> expr (* var 0 denotes variable 0, var 1 denotes variable 1, etc *)
| S : expr
| K : expr
| app : expr -> expr -> expr.

Notation " a [+] b " := (app a b) (at level 50, left associativity).

Inductive steps : expr -> expr -> Prop :=
| steps_S : forall x y z, steps (S [+] x [+] y [+] z) (x [+] z [+] (y [+] z))
| steps_K : forall x y, steps (K [+] x [+] y) x
| steps_app_l : forall x y z, steps x y -> steps (x [+] z) (y [+] z)
| steps_app_r : forall x y z, steps x y -> steps (z [+] x) (z [+] y).

Notation " a ~> b " := (steps a b) (at level 55, left associativity).

Inductive steps_star : expr -> expr -> Prop :=
| steps_none : forall c, steps_star c c
| steps_once : forall c1 c2, c1 ~> c2 -> steps_star c1 c2
| steps_many : forall c1 c2 c3, c1 ~> c2 -> steps_star c2 c3 -> steps_star c1 c3.

Notation " a ~>* b " := (steps_star a b) (at level 55, left associativity).
```

These are the standard definitions of the S and K combinator system, with the addition of variable terms like `var n`.
We can speak about whether expressions contain variables. Expressions which contain no variables are called constants.
The addition of variables allows us to build a small compiler using the concept of alpha-elimination (see src/compile.v).

```
(* src/expr.v *)

Inductive contains_var (n : nat) : expr -> Prop :=
| contains_here : contains_var n (var n)
| contains_left : forall c1 c2, contains_var n c1 -> contains_var n (c1 [+] c2)
| contains_right : forall c1 c2, contains_var n c2 -> contains_var n (c1 [+] c2).

Notation "  n 'IN' c " := (contains_var n c) (at level 60, no associativity).

Definition is_const c := forall n, ~ n IN c.
```

All other combinators, including I, are derivable from S and K.  
```
(* src/well_known_combinators.v *)

Definition I : expr := S [+] K [+] K.
Theorem steps_star_I : forall c, (I [+] c) ~>* c.

Definition T : expr := S [+] (K [+] (S [+] I)) [+] K.
Theorem steps_star_T : forall x y, (T [+] x [+] y) ~>* (y [+] x).

Definition B : expr := S [+] (K [+] S) [+] K.
Theorem steps_star_B : forall x y z, B [+] x [+] y [+] z ~>* x [+] (y [+] z).

Definition M : expr := S [+] I [+] I.
Theorem steps_star_M : forall x, M [+] x ~>* x [+] x.

Definition C : expr := B [+] (T [+] (B [+] B [+] T)) [+] (B [+] B [+] T).
Theorem steps_star_C : forall x y z, C [+] x [+] y [+] z ~>* x [+] z [+] y.
```

We can set aside two particular combinators `t` and `f` to represent true and false respectively.
```
Definition t : expr := K.
Definition f : expr := K [+] I.
```

Arithmetic
---------
We can also encode the natural numbers. `nxt` takes a natural number to its successor.
`prv` takes a natural number to its predecessor. And `zro` encodes 0.
We can define `rep` which takes a natural number and gives its representation inside the SK calculus.
```
(* src/arithmetic_ops.v *)

Definition nxt : expr := V [+] f.
Definition prv : expr := T [+] f.
Definition zro : expr := I.

Fixpoint rep (n: nat) :=
  match n with
  | 0 => zro
  | Datatypes.S m => nxt [+] (rep m)
  end.

Theorem steps_star_prv_nxt : forall n, prv [+] (rep (1 + n)) ~>* rep n.
```

Then we can encode addition, multiplication, and exponents.
```
Definition add_m_n_op : expr := ...
Theorem add_m_n_spec : forall x y : nat, add_m_n_op [+] rep x [+] rep y ~>* rep (x + y).

Definition mul_m_n_op : expr := ...
Theorem mul_m_n_spec : forall x y : nat, mul_m_n_op [+] rep x [+] rep y ~>* rep (x * y).

Definition pow_m_n_op : expr := ...
Theorem pow_m_n_spec : forall x y : nat, pow_m_n_op [+] rep x [+] rep y ~>* rep (x ^ y).
```

Godel Numbering
--------------
Every expr can be represented uniquely by a list of digits.
```
(* src/godel.v *)

Fixpoint godel_digits (c : expr) : list nat :=
  match c with
  | S => [ 1 ]
  | K => [ 2 ]
  | c1 [+] c2 => [3] ++ (godel_digits c1) ++ (godel_digits c2) ++ [4]
  | var n => [ 5 ]
  end.
```

And of course a list of digits can be converted to a natural number by multiplying each
successive digit by a a successive power of 10 and then summing.
```
(* src/digits.v *)

Fixpoint digits_to_nat (l : list nat) idx :=
  match l with
  | nil => 0
  | d :: l' => (10^idx * d) + (digits_to_nat l' (1 + idx))
  end.
```

Which means every expr can be associated to a unique natural number, which we can call its Godel number.
```
(* src/godel.v *)

Definition godel_number (c : expr) : nat :=
  digits_to_nat (godel_digits c) 0.
```

We can create an expression **within the SK combinator calculus itself** which computes Godel numbers.
```
(* src/godel.v *)

Definition godelize_op : expr := ...
Theorem godelize_spec : forall n : nat, godelize_op [+] rep n ~>* rep (godel_number (rep n)).
```

Computability
------------
A predicate `P` over the natural numbers is computable if there is a constant SK expression `c` which steps to `t` when fed any number belonging to `P`, and steps to `f` when fed any number not belonging to `P`.
```
(* src/godel.v *)

Definition is_computable (P : nat -> Prop) := exists c, is_const c /\ (forall n, (P n /\ c [+] rep n ~>* t) \/ (~ P n /\ c [+] rep n ~>* f)).
```

Godel's Theorem
---------------
A Godel sentence for a predicate `P` is a constant SK expression which steps to `t` if and only if its own Godel number satisfies `P`.
When `c` is a Godel sentence for `P`, `c` says "My Godel number belongs in P".
```
(* src/godel.v *)

Definition godel_sentence (P : nat -> Prop) (c : expr) := is_const c /\ ((c ~>* t /\ P (godel_number c)) \/ (~ c ~>* t /\ ~P (godel_number c))).
```

 A Godel sentence can be constructed for every computable predicate.
```
(* src/godel.v *)

Theorem computable_prop_has_godel_sentence : forall P, is_computable P -> exists g, godel_sentence P g.
```

Godel showed that not every predicate is computable. In particular, consider the set of all Godel numbers who are associated to expressions which steps to `t`.
```
(* src/godel.v *)

Definition converges_t n := exists c, n = godel_number c /\ c ~>* t.
```

If this predicate `converges_t` were computable, so would the predicate `not_converges_t := fun n => ~converges_t n`. Then it would have a Godel sentence `g` by `computable_prop_has_godel_sentence`. The sentence `g` would say "My Godel number does not converge to t." This leads to a liar's paradox and therefore we know `converges_t` is not computable.

```
Theorem converges_t_not_computable : ~is_computable converges_t.
```

We conclude that there are sets of natural numbers which are well defined, but cannot be computed by SK expressions.

Technicalities
--------------
There are some technicalities that need to be overcome during the course of the development.
First, we need to show the model of computation described by the stepping / reduction `~>*` operator is well defined and doesn't depend on the order of reductions. This is addressed by the Church-Rosser theorem, which proves that normal forms are unique.
```
(* src/expr.v *)

Definition is_normal c := forall c', ~ c ~> c'.
```

```
(* src/church_rosser.v *)

Theorem unique_normal_form : forall c c1 c2, c ~>* c1 -> c ~>* c2 -> is_normal c1 -> is_normal c2 -> c1 = c2.
```

Second, we need to that a list of Godel digits uniquely specifies an expression.
```
(* src/godel.v *)

Definition has_unambiguous_parse l := forall c1, is_const c1 /\ l = godel_digits c1 -> forall c2, l = godel_digits c2 -> c1 = c2.
Theorem all_unambiguous_parse : forall l, has_unambiguous_parse l.
```