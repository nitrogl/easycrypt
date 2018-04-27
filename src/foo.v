From mathcomp Require Import all_ssreflect.

Lemma L : forall (x y : nat), x - y = 2 -> x + y = 3.
Proof.
move=> x y.
wlog: y / x <= y.
admit.


