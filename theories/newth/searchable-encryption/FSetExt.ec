(* --------------------------------------------------------------------
 * Copyright (c) - 2018 - Roberto Metere <r.metere2@ncl.ac.uk>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Int IntExt List ListExt FSet.

lemma elems_empty_eq_fset0 ['a] (A : 'a fset):
  elems A = [<:'a>] <=> A = fset0.
proof.
  split.
  + move=> elems_nil; apply/fsetP=> x; rewrite !memE elems_fset0 elems_nil //.
  + move => A0; rewrite A0 elems_fset0 //.
qed.

lemma fsetD1 (x : 'a) (A : 'a fset):
  ! mem A x <=> A `\` fset1 x = A.
proof.
  split.
  + move => x_notin_A; rewrite fsetP; move => a; rewrite in_fsetD1; by case (a = x) => //.
  + apply absurd => /=; move => x_in_A; rewrite fsetP negb_forall /=; exists x; rewrite in_fsetD x_in_A in_fset1 //.
qed.

lemma fsetU1 (x : 'a) (A : 'a fset):
  mem A x <=> A `|` fset1 x = A.
proof.
  split.
  + move => x_notin_A; rewrite fsetP; move => a; rewrite in_fsetU1; split.
    * move => [a_in_A | a_eq_x] => //; rewrite a_eq_x //.
    * move => a_in_A; rewrite a_in_A //.
  + apply absurd => /=; move => x_in_A; rewrite fsetP negb_forall /=; exists x; rewrite in_fsetU x_in_A in_fset1 //.
qed.

lemma fsetU1_oflist (x : 'a) (A : 'a fset):
  A `|` fset1 x = oflist (x :: elems A) by rewrite oflist_cons fsetUC elemsK //.

lemma oflist_undup (s : 'a list):
  oflist (undup s) = oflist s.
proof.
  move : (undup_uniq s) => s_uu.
  move : (oflist_uniq (undup s)); rewrite s_uu /=; move => us_eq_eous.
  move : (oflistK s) => us_eq_eos.
  move : (perm_eq_trans (undup s) (elems (oflist (undup s))) (elems (oflist s))); rewrite perm_eq_sym us_eq_eous us_eq_eos /=; move => eous_eq_eos.
  apply fset_eq; exact eous_eq_eos.
qed.



lemma perm_eq_oflist (s1 s2 : 'a list):
  uniq s1 /\ uniq s2 => (oflist s1 = oflist s2) <=> (perm_eq s1 s2).
proof.
  move => [s1_u s2_u].
  split; last by apply oflist_perm_eq.
  rewrite -(undup_id s1) // -(undup_id s2) // 2!oflist_undup; apply perm_eq_oflist.
qed.

lemma fset_rem (A : 'a fset) z:
  mem A z => !mem (rem z (elems A)) z.
proof.
  rewrite memE; move => z_in_A.
  move : (uniq_elems A); elim (elems A) => //.
  move => x l ibase /=.
  case (x = z) => //=.
  move => x_neq_z [x_notin_l l_u].
  rewrite negb_or eq_sym x_neq_z /=.
  apply ibase => //.
qed.

lemma memC_fset_count (A : 'a fset) z:
  ! mem A z => count (pred1 z) (elems A) = 0.
proof.
  rewrite memE; elim (elems A) => //.
  move => x l ibase.
  rewrite in_cons negb_or eq_sym.
  move => [x_neq_z hypbase].
  rewrite /= /pred1 /b2i x_neq_z /=.
  apply ibase => //.
qed.

lemma memC_count (s : 'a list) z:
  ! mem s z => count (pred1 z) s = 0.
proof.
  elim s => //.
  move => x l ibase.
  rewrite in_cons negb_or eq_sym.
  move => [x_neq_z hypbase].
  rewrite /= /pred1 /b2i x_neq_z /=.
  apply ibase => //.
qed.

lemma count_oflist (A : 'a fset) z:
  mem A z <=> count (pred1 z) (elems A) = 1.
proof.
  split.
  + move => z_in_A.
    rewrite (count_rem (pred1 z) (elems A) z).
    * rewrite -memE //.
    rewrite /b2i /= addzC.
    pose c := count (pred1 z) (rem z (elems A)).
    have ->: c + 1 = 1 <=> c + 1 = 0 + 1 by trivial.
    rewrite -eqn_add /c.
    move : (fset_rem A z _) => //.
    move : (uniq_elems A).
    elim (elems A) => //.
    move => x l ibase /=.
    case (x = z); move => xz.
    * move => [x_noint_l lu] z_notin_l.
      rewrite memC_count => //.
    * have ->: z <> x by rewrite eq_sym //.
      rewrite /b2i /pred1 xz /=.
      move => [x_noint_l lu] z_notin_l.
      apply ibase => //.
  + apply absurd.
    rewrite memE.
    move => z_notin_A.
    move : (memC_count (elems A) z _) => // c.
    rewrite c //.
qed.

lemma memC_D (A: 'a fset) z:
  !mem A z => A `\` fset1 z = A.
proof.
  move => z_notin_A.
  apply fset_eq.
  have ->: elems A = rem z (elems A) by rewrite rem_id => //; first by rewrite -memE //.
  rewrite setD1E.
qed.


lemma memC_perm_rem (A : 'a fset) z:
  !mem A z => perm_eq (elems A) (rem z (elems (A `|` fset1 z))).
proof.
  move => z_notin_A.
  rewrite fsetU1_oflist oflist_cons fsetUC elemsK.
  have ->: elems A = elems ((A `|` fset1 z) `\` fset1 z) by rewrite fsetDK memC_D //.
  rewrite setD1E.
qed.
