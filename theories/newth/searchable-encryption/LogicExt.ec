(* --------------------------------------------------------------------
 * Copyright (c) - 2016--2017 Roberto Metere (r.metere2@ncl.ac.uk)
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Logic Int.

lemma forall_and (P Q: 'a -> bool):
  (forall x, P x /\ Q x) <=> ((forall x, P x) /\ (forall x, Q x)).
proof.
  split.
  + move => h; split => x; first 2 by move : (h x); move => [pre _] => //.
  + move => [hl hr] x; rewrite hl hr //.
qed.

(* Iterated applications of the same function - note that negative composition is just not defined here, so fcomp f -1 is expanding forever *)
op (^): { ('a -> 'a) -> int -> 'a -> 'a |
   forall f n x, (f^n) x = (n = 0) ? x : (f^(n - 1)) (f x)
} as fcompE.

lemma fcomp0 (f: 'a -> 'a): f^0 = idfun
  by rewrite fun_ext => x; rewrite fcompE //.

lemma fcomp_proper n (f: 'a -> 'a): 0 <= n => f^(n + 1) = f^n \o f.
proof.
  move => nat_n.
  rewrite fun_ext => x; rewrite fcompE /= fcompE /= addz1_neq0 //.
qed.

lemma fcomp1 (f: 'a -> 'a): f^1 = f
  by rewrite fun_ext => x; rewrite fcompE /= fcompE //.

lemma fcomp2 (f: 'a -> 'a): f^2 = f \o f
  by rewrite fun_ext => x; rewrite fcompE /=  fcompE /= fcompE //=.

lemma fcompC n (f: 'a -> 'a): 0 <= n => f^n \o f = f \o f^n.
proof.
  elim n.
  + rewrite /(\o) fun_ext => x; rewrite fcompE /= fcompE //=.
  + move => i nat_i ibase.
    rewrite fcomp_proper //; pose z := (f \o (f^i \o f)); rewrite ibase /z.
    rewrite /(\o) fun_ext => x //.
qed.

lemma fcompC_ext n (f: 'a -> 'a) x: 0 <= n => (f^n) (f x) = f ((f^n) x) by move => nat_n; move : x; rewrite -fun_ext fcompC //.

lemma fcomp_add a b (f: 'a -> 'a): 0 <= a => 0 <= b =>
   f^a \o f^b = f^(a + b).
proof.
  elim : a; first by rewrite fcomp0 /(\o) /idfun //.
  move => i nat_i ibase pre.
  move : ibase; rewrite pre /= => ibase.
  rewrite /(\o) fun_ext => x; rewrite fcompE -addzA addzC -addzA add1z_neq0 //=.
  rewrite addzC (fcompE f (i + b + 1)) /=.
  rewrite addz1_neq0 //=; first by rewrite addz_ge0 //.
  rewrite -ibase /(\o) (fcompC_ext b) //.
qed.

lemma fcompC_alt a b (f: 'a -> 'a): 0 <= a => 0 <= b =>
   f^a \o f^b = f^b \o f^a.
proof.
   move => nat_a nat_b; rewrite fcomp_add // fcomp_add // addzC //.
qed.

lemma fcomp_inj (f: 'a -> 'a):
  injective f <=> forall n, 0 <= n => forall x y, (f^n) x = (f^n) y => x = y.
proof.
  split.
  - rewrite /injective; move => inj_f n.
    elim n.
    + rewrite fcomp0 /idfun //.
    + move => n nat_n ibase x y.
      have sucn0: n + 1 <> 0 by rewrite neq_ltz; right; rewrite -lez_add1r addzC -(lez_add2r (-1)) /= nat_n //.
      rewrite fcompE sucn0 /= eq_sym fcompE sucn0 /= eq_sym => pre.
      move : (ibase (f x) (f y) pre).
      apply inj_f.
  - move => pre; move : (pre 1) => /=.
     rewrite fcomp1 //.
qed.

lemma fcomp_cancel (f g: 'a -> 'a) n:
  cancel f g => 0 <= n => cancel (f^n) (g^n).
proof.
  move => can_fg; elim n.
  - rewrite /= 2!fcomp0 /idfun //.
  - move => n nat_n ibase.
    move : (can_fg); rewrite /cancel.
    move => pre x; move : (pre x) => pre_x.
    have sucn0: n + 1 <> 0 by move : nat_n; rewrite -(lez_add2r 1); apply absurd => /= sucn0; rewrite sucn0 //.
    rewrite 2!(fcompE _ (n + 1)) sucn0 /= (fcompC_ext _ f) // can_fg ibase //.
qed.
