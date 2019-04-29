(* --------------------------------------------------------------------
 * Copyright (c) - 2018 - Roberto Metere <r.metere2@ncl.ac.uk>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Int Ring IRing.
import Ring.IntID.

(* addzI and addIz are implications, these are iff *)
lemma nosmt eqz_add2r (l n m : int):
  n + l = m + l <=> n = m by rewrite eqz_leq 2!lez_add2r -eqz_leq //.

lemma nosmt eqz_add2l (l n m : int):
  l + n = l + m <=> n = m by rewrite (addzC l n) (addzC l m) eqz_add2r //.

