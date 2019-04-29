(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2018 - Roberto Metere <r.metere2@ncl.ac.uk>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

lemma nosmt andWI: forall (a b c : bool),
  (a => b => c) <=> (a /\ b => c).
proof.
  move => *; split; first by apply (andW a b c).
  move => hyp at bt; apply hyp; rewrite at bt //.
qed.

lemma nosmt eqDnot: forall a b,
  (!(a)) = b <=> !(a = b).
proof.
  move => a b; case a => aV /=; by case b => bV //=.
qed.