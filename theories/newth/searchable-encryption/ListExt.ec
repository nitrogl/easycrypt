(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2018 Roberto Metere (r.metere2@ncl.ac.uk)
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* Freely adapted from datatypes/Array.ec *)

require import Core Int IntExtra List Ring.
require import LogicExt IntExt TacticsExt.
(*---*) import Ring.IntID.

lemma nosmt mem_nth_exists (s: 'a list) x:
  mem s x => exists i, 0 <= i < size s /\ nth witness s i = x.
proof.
  elim s => //= e s ibase.
  case (x = e) => //=.
  + move => xe; exists 0 => //.
    rewrite -lez_add1r lez_addl size_ge0 /= eq_sym //.
  + move => xe pre; move : ibase; rewrite pre /=; move => [i] [[ige ilt] inth].
    exists (i + 1) => //=.
    rewrite addzC ltz_add2l ilt /= addz_ge0 //= add1z_neq0 //.
qed.

lemma nosmt mem_size (s: 'a list) x:
  mem s x => 0 < size s.
proof.
  elim s => //= e s ibase.
  case (x = e) => //=; first 2 by move => xe; rewrite -lez_add1r lez_addl size_ge0 /=.
qed.

lemma nosmt mem_size_nth (s: 'a list) x:
  mem s x <=> 0 < size s /\ exists i, 0 <= i < size s /\ nth witness s i = x.
proof.
  split; first by move => pre; rewrite (mem_size s x) // (mem_nth_exists s x) //.
  elim s => //= e s ibase.
  case (x = e) => //=.
  move => xe; rewrite -lez_add1r lez_addl size_ge0 /=.
  move => [i] [[ige ilt] h].
  have i0: i <> 0 by move : h; apply absurd => //= i0; rewrite i0 //= eq_sym xe //=.
  move : h; rewrite i0 /= => h.
  apply ibase; split.
  + move : ilt; apply absurd => /=.
    rewrite -lezNgt; move : (size_ge0 s); rewrite andWI -eqz_leq => empty.
    rewrite -empty /= -lezNgt.
    move : i0 ige; rewrite andWI -ltz_def -lez_add1r //=.
  + exists (i - 1); rewrite h /=.
    have igt0: 0 < i by rewrite ltz_def i0 ige //.
    rewrite -(lez_addl 1) /= -addz0 lez_add1r igt0 /= -(ltz_add2l 1) /= ilt.
qed.

lemma nosmt eq_nth x0 (s1 s2 : 'a list):
  s1 = s2 <=>
     size s1 = size s2
  /\ (forall i, 0 <= i < size s1 => nth x0 s1 i = nth x0 s2 i).
proof.
  elim: s1 s2 => [|x1 s1 IHs1] [|x2 s2] //=; 1,2: smt w=(size_ge0).
  split. move => eq_szS; have eq_sz: size s1 = size s2 by move=> /#.
  split. have ->: size s1 = size s2 by assumption. trivial.
  move => *.
  have ->: x1 = x2 by move => /#.
  have ->: s1 = s2 by move => /#.
  trivial.
  move=> eq_szS; have eq_sz: size s1 = size s2 by move=> /#.
  split; first smt.
  have ads: (forall (i : int),
        0 <= i < size s1 => nth x0 s1 i = nth x0 s2 i) by move => /#.
  apply (eq_from_nth x0 s1 s2) => //.
qed.

lemma nosmt drop_take_nth (l: 'a list) s:
  0 <= s < size l => drop s (take (s + 1) l) = [nth witness l s].
proof.
  move => hyp.
  elim: hyp; move => s_ge0 s_lt_lenl.
  have [la x ->]: exists la x, l = take s l ++ [x] ++ la by smt.
  have ->: take (s + 1) (take s l ++ [x] ++ la) = take s l ++ [x] by smt.
  smt.
qed.

lemma nosmt cons_take n x (s: 'a list):
  0 <= n => x :: take n s = take (n + 1) (x :: s)
by rewrite take_cons; smt.

lemma nosmt take_cat n (s: 'a list):
  0 <= n < size s => take (n + 1) s = take n s ++ [nth witness s n]
by smt.

lemma nosmt take_less n (s1 s2: 'a list):
  (take (n + 1) s1 = take (n + 1) s2) => (take n s1 = take n s2).
proof.
  case (0 <= n); last by smt.
  case (size s1 <= n); first by smt.
  case (size s2 <= n); first by smt.
  move => *.
  rewrite take_cat in H2; first by smt.
  rewrite take_cat in H2; first by smt.
  smt.
qed.

lemma nosmt take_takemore (l: 'a list) n:
  take n (take (n + 1) l) = take n l.
proof.
  case (l <> []); last by smt.
  move => *.
  have [x xs l_cons]: exists x xs, l = x :: xs by smt.
  case (n < size l); last by smt.
  case (0 <= n); last by smt.
  elim: n; first by smt.
  move => i i_ge0 induction hyp.
  have hyp1: take i (take (i + 1) l) = take i l by smt.
  rewrite take_cat in hyp1; first by smt.
  have ->: take (i + 1) l = take i l ++ [nth witness l i] by rewrite take_cat; first by smt.
  rewrite take_cat; first by smt.
  have ->: nth witness (take (i + 1 + 1) l) i = nth witness l i by smt.
  rewrite take_cat; first by smt.
  pose l1 := take i (take (i + 1) l ++ [nth witness l (i + 1)]);
    pose l2 := take i l.
  have ->: (l1 ++ [nth witness l i] = l2 ++ [nth witness l i]) <=> (l1 = l2) by smt.
  rewrite /l1 /l2.
  have ->: take i (take (i + 1) l ++ [nth witness l (i + 1)]) = take i (take (i + 1) l) by smt.
  apply induction; first by smt.
qed.

lemma nosmt mem_eq_empty (s : 'a list): (forall x, ! mem s x) <=> s = [] by split => //; apply mem_eq0.

lemma nosmt uniq_mem_perm_eq (s1 s2 : 'a list):
  uniq s1 /\ uniq s2 => (mem s1 = mem s2 <=> perm_eq s1 s2).
proof.
  move => [s1u s2u]; split.
  + rewrite fun_ext /(==); move => hyp; apply uniq_perm_eq => //; move => x; rewrite -eq_iff hyp //.
  + rewrite fun_ext /(==); move => hyp x; rewrite eq_iff; apply perm_eq_mem; exact hyp.
qed.

lemma nosmt count_mem_rem (x : 'a) (s : 'a list):
  count (pred1 x) s <= 1 => !mem (rem x s) x.
proof.
  apply absurd => /=; move => x_in_rxs.
  move : (List.mem_rem x s x _) => // x_in_s.
  move : (count_rem (pred1 x) s x _) => //.
  move : (count_rem (pred1 x) (rem x s) x _) => //.
  rewrite /pred1 /b2i /=.
  move => crr; rewrite crr.
  move => cr; rewrite cr /=.
  move : (count_ge0 (pred1 x) (rem x (rem x s))).
  pose c := count (transpose (=) x) (rem x (rem x s)).
  elim/natind : c.
  + move => *; rewrite (lez_anti n 0) => //.
  + move => n c_gt0 ibase sn.
    have sn_gt0: 0 < n + 1 by rewrite ltz_def sn addz1_neq0 //.
    rewrite lezNgt negbK addzA -add0z ltz_add2r -lez_add1r.
    have ->: 2 = 1 + 1 by trivial.
    rewrite -addzA lez_add2l addzC sn //.
qed.

lemma nosmt mem_has_pred1 (s: 'a list) x:
  mem s x <=> has (pred1 x) s.
proof.
  elim s => //= z zs ibase.
  case (x = z) => //= x_z.
  rewrite ibase /pred1 eq_sym x_z //.
qed.

lemma nosmt memC_count_pred1 (s: 'a list) x:
  !mem s x <=> count (pred1 x) s = 0.
proof.
  elim s => //= z zs ibase.
  rewrite negb_or eq_sym.
  split.
  + move => [x_z].
    rewrite /b2i ibase /pred1 x_z //=.
  + move => pre.
    have b0: b2i (pred1 x z) = 0 by move : pre; apply absurd; rewrite -lt0n ?(b2i_ge0); move : (b2i_le1 (pred1 x z)); rewrite -lez_add1r /= andWI -eqz_leq => b2i_eq1; rewrite b2i_eq1 add1z_neq0 ?(count_ge0) //.
    move : pre.
    rewrite b0 /= => c0.
    have ->: z <> x by move : b0; apply absurd => /= z_x; rewrite /b2i /pred1 z_x //.
    rewrite ibase c0 //.
qed.

lemma mem_count_pred1 (s: 'a list) x:
  mem s x <=> 0 < count (pred1 x) s by rewrite lt0n ?count_ge0 -iff_negb memC_count_pred1 //=.

lemma nosmt count_pred1_mem (s1 s2: 'a list):
  (forall x, count (pred1 x) s1 <= count (pred1 x) s2) => (forall x, mem s1 x => mem s2 x).
proof.
  apply absurd.
  rewrite 2!negb_forall /=.
  move => [x].
  rewrite negb_imply.
  move => [s1x s2x].
  exists x.
  rewrite memC_count_pred1 in s2x.
  rewrite s2x lezNgt /=.
  apply mem_count_pred1 => //.
qed.

lemma nosmt mem_rem_uniq ['a] s:
  (exists (x : 'a), mem (rem x s) x) <=> !uniq s.
proof.
  split.
  * move => [x].
    apply absurd => /= s_uniq.
    move : (rem_uniq x s).
    rewrite s_uniq /=.
    move : s_uniq.
    elim s => // [y l] ibase.
    rewrite cons_uniq -andWI.
    case (y = x) => x_eq_y.
    + rewrite x_eq_y //.
    + rewrite x_eq_y /=.
      move => y_not_l l_uniq.
      rewrite -andWI.
      move => y_not_rem_x_l rem_x_l_uniq.
      rewrite ibase //= eq_sym.
      exact x_eq_y.
  * elim s => //.
    move => x l ibase.
    rewrite cons_uniq negb_and /=.
    case (mem l x) => x_in_l /=.
    + exists x => //.
    + move => l_uniq.
      move : ibase.
      rewrite l_uniq /=.
      move => [y y_inrem].
      move : (List.mem_rem y l y) => y_in_l.
      rewrite y_inrem /= in y_in_l.
      have x_neq_y: x <> y by move : x_in_l; apply absurd => /=; move => x_eq_y; rewrite x_eq_y; exact y_in_l.
      exists y => //.
      rewrite x_neq_y /= eq_sym x_neq_y /=.
      exact y_inrem.
qed.

lemma nosmt uniq_mem_rem ['a] s: uniq s => forall (x : 'a), ! mem (rem x s) x by move => su x; move : su; apply absurd => /=; move => hyp; rewrite -mem_rem_uniq //=; exists x => //.

lemma nosmt uniq_mem_rem_eq (s: 'a list):
  (forall (x: 'a), !mem (rem x s) x) <=> uniq s.
proof.
  split; last by apply uniq_mem_rem.
  elim s => // x l ibase.
  move : ibase.
  apply absurd.
  rewrite 2!negb_imply cons_uniq negb_and negbK.
  move => [rempart].
  case (! uniq l) => // luniq.
  + rewrite /=.
    move : rempart.
    apply absurd => //.
    rewrite 2!negb_forall /=.
    move => [a rem_la].
    exists a.
    case (a = x) => // a_x.
    - rewrite a_x /= (mem_rem a l) -a_x //.
    - rewrite eq_sym a_x /= a_x //=.
  + move : (rempart x).
    rewrite //=.
qed.

lemma nosmt mem_rem_alt ['a] (x : 'a) s y:
  mem (rem x s) y /\ uniq s => mem s y /\ x <> y.
proof.
  move => [y_rem_x_s s_uniq].
  rewrite (List.mem_rem x s y) // /=.
  move : y_rem_x_s.
  apply absurd => /=.
  move => x_eq_y.
  rewrite x_eq_y /=.
  apply uniq_mem_rem => //.
qed.

lemma nosmt mem_mem_rem ['a] (x : 'a) (s: 'a list) y:
  mem s y => x <> y => mem (rem x s) y.
proof.
  elim s => // z l ibase.
  rewrite in_cons.
  case (y = z) => y_eq_z /=.
  + rewrite y_eq_z eq_sym.
    move => z_neq_x.
    rewrite z_neq_x //.
  + move => y_in_l x_neq_y.
    case (z = x) => z_eq_x //=.
    rewrite y_eq_z /=.
    apply ibase => //.
qed.

lemma nosmt size_eq1 (l: 'a list):
  size l = 1 <=> exists x, [x] = l.
proof.
  elim l => //.
  move => x l ibase.
  rewrite /= -1!(addz0 1) -addzA add0z (addzC 1 0) -addzA (add0z) addzC eqz_add2r size_eq0 eq_sym.
  split.
  + move => l0; exists x => //=.
  + move => [y [_ hyp]] => //.
qed.

lemma nosmt size_gt0 (l: 'a list):
  0 < size l <=> exists x s, x :: s = l.
proof.
  elim l => // => e l ibase.
  split.
  + move => el.
    case (size l = 0) => //= sl0.
    * rewrite size_eq0 in sl0.
      rewrite sl0.
      exists e [] => //.
    exists e l => //.
  + move => [x s pre].
    rewrite /= -lez_add1r addzC -addzA (add0z (1 + size l)) (addzC 1 (size l)) add0z lez_addr size_ge0.
qed.

lemma nosmt size_le1 (l: 'a list):
  size l <= 1 <=> l = [] \/ exists x, [x] = l.
proof.
  case (size l = 0) => sl0.
  rewrite sl0 /= -size_eq0; by left.
  have sl: 0 < size l by move : (size_ge0 l)  => le; move : sl0; apply absurd => /=; rewrite -lezNgt eqz_leq //.
  have ->: size l <= 1 <=> size l = 1 by (split => pre; first by rewrite -lez_add1r /= in sl; rewrite eqz_leq //); rewrite pre //.
  have ->: !l = [] by rewrite -size_eq0.
  rewrite size_eq1 //.
qed.

op betail (s : 'a list) =
  with s = []      => []
  with s = x :: xs => (xs = []) ? [] : x :: betail xs.

lemma nosmt last_betail (xs : 'a list) z0:
  xs <> [] =>
  (betail xs) ++ [last z0 xs] = xs.
proof.
  elim xs => //= => x l ibase.
  case (l = []) => //= l0.
  have ->: last x l = last z0 l by rewrite (last_nonempty x z0) //.
  apply ibase => //.
qed.

lemma nosmt betail_cat (s1 s2 : 'a list):
  betail (s1 ++ s2) = (s2 = []) ? betail s1 : s1 ++ betail s2.
proof.
  case (s2 = []) => //= s20.
  rewrite s20 2!cats0 //=.
  elim s1 => //= x l ibase.  
  have ->: !(l ++ s2 = []).
    rewrite -size_eq0 size_cat.
    rewrite -size_eq0 in s20.
    move : (size_ge0 l).
    elim (size l) => // => n nbase.
    rewrite (addzC n 1) -addzA add1z_neq0 //.
    move : (size_ge0 s2) => ss2.
    rewrite addz_ge0 //.
  rewrite //=.
qed.

lemma nosmt not_uniq_minsize (s: 'a list):
  (!uniq s) => 2 <= size s.
proof.
  apply absurd => /=.
  rewrite -ltzNge.
  elim s => //= x l ibase.
  have ->: 2 = 1 + 1 by trivial.
  rewrite ltz_add2l.
  have ->: size l < 1 <=> size l = 0 by move : (size_ge0 l); rewrite -lez_add1r -(addz0 1) lez_add2l eqz_leq //.
  rewrite size_eq0 //.
qed.

lemma nosmt not_uniq_explode (s: 'a list):
  (! uniq s) <=> exists x y xs, x :: y :: xs = s /\ (x = y \/ mem xs x \/ mem xs y \/ ! uniq xs).
proof.
  split.
  - (* => *)
    move => suniq.
    move : (not_uniq_minsize s).
    rewrite suniq /= => ss.
    move : ss suniq.
    elim (s) => //= x l ibase.
    rewrite negb_and /=.
    have ->: 2 = 1 + 1 by trivial.
    rewrite lez_add1r -(addz0 1) ltz_add2l size_gt0.
    move => [t w] tw_l hyp.
    exists x t w => /=.
    move : hyp.
    rewrite tw_l /= -tw_l /= negb_and -orbA //=.
  - (* <= *)
    move => [x y xs] [expl memberships].
    rewrite -expl 2!cons_uniq 2!negb_and /= -orbA //=.
qed.

lemma nosmt not_uniq_perm (s: 'a list):
  (! uniq s) <=> exists x xs, perm_eq (x :: x :: xs) s.
proof.
  split.
  - (* => *)
    elim (s) => //= e l ibase.
    rewrite negb_and /= => membership.
    case (!uniq l) => /= luniq.
    + move : (ibase).
      rewrite luniq /=.
      move => [z t] cbase.
      exists z (e :: t).
      rewrite -cat1s perm_catCl -cat1s -catA perm_catCl 2!cat_cons perm_cons perm_catCl catA perm_catCl 2!cat1s //.
    + move : membership.
      rewrite luniq /= => le.
      exists e (rem e l).
      rewrite /= perm_eq_sym perm_cons perm_to_rem => //.
  - (* <= *)
    move => [x xs] perm.
    move : (perm_eq_uniq (x :: x :: xs) s).
    rewrite perm //=.
qed.

lemma nosmt uniq_inj_nth (s: 'a list):
  (uniq s) <=> forall i j, 0 <= i < size s => 0 <= j < size s => nth witness s i = nth witness s j => i = j.
proof.
  split.
  - (* => *)
    elim (s) => //= e l ibase.
    + rewrite lez_lt_asym //.
    + move => [emem luniq] i j [imin imax] [jmin jmax].
      case (i = 0) => // i0.
      * case (j = 0) => // j0.
        rewrite i0 (eq_sym _ j) j0 /=.
        move : emem; apply absurd => /=ah.
        rewrite ah mem_nth // -(ltz_add2r 1) /= (addzC _ 1) jmax /=.
        move : jmin; rewrite lez_eqVlt (eq_sym _ j) j0 -(lez_add2r 1) addzC lez_add1r //.
      * case (j = 0) => // j0.
        - rewrite j0 i0 /=.
          move : emem; apply absurd => /=ah.
          rewrite -ah mem_nth // -(ltz_add2r 1) /= (addzC _ 1) imax /=.
          move : imin; rewrite lez_eqVlt (eq_sym _ i) i0 -(lez_add2r 1) addzC lez_add1r //.
        - move : (ibase luniq (i - 1) (j - 1)).
          move : imin; rewrite lez_eqVlt (eq_sym _ i) i0 -(lez_add2r 1) addzC lez_add1r /= => igt0.
          rewrite igt0 -(ltz_add2r 1) /= (addzC _ 1) imax /=.
          move : jmin; rewrite lez_eqVlt (eq_sym _ j) j0 -(lez_add2r 1) addzC lez_add1r /= => jgt0.
          rewrite jgt0 -(ltz_add2r 1) /= (addzC _ 1) jmax /=.
          rewrite eqz_add2r //.
  - (* <= *)
    apply absurd.
    rewrite negb_forall /=.
    elim (s) => //= e l ibase.
    rewrite negb_and /=.
    case (mem l e) => /= emem.
    + move : (mem_nth_exists l e emem) => [j] [[jmin jmax] e_def].
      exists 0; rewrite negb_forall /=.
      exists (j + 1).
      rewrite -lez_add1r lez_add2l size_ge0 /=.
      have aux: j + 1 <> 0 by rewrite eq_sym neq_ltz; left; rewrite -lez_add1r addzC lez_add2r jmin.
      rewrite aux /= 2!negb_imply (eq_sym 0) aux e_def /=.
      rewrite addzC ltz_add2l jmax /=.      
      rewrite lez_eqVlt addzC (eq_sym 0) aux /=.
      rewrite -lez_add1r addzC lez_add2r jmin.
    + move => luniq; move : (ibase luniq) => [i].
      rewrite negb_forall /=; move => [j].
      rewrite 3!negb_imply; move => [[imin imax]] [[jmin jmax]] [f_eq] ij_neq.
      exists (i + 1).
      rewrite negb_forall /=; exists (j + 1).
      rewrite eqz_add2r /= f_eq ij_neq.
      have auxi: i + 1 <> 0 by rewrite eq_sym neq_ltz; left; rewrite -lez_add1r addzC lez_add2r imin.
      have auxj: j + 1 <> 0 by rewrite eq_sym neq_ltz; left; rewrite -lez_add1r addzC lez_add2r jmin.
      rewrite 3!negb_imply auxi auxj /=.
      rewrite addzC ltz_add2l imax /=.      
      rewrite lez_eqVlt addzC (eq_sym 0) auxi /=.
      rewrite -lez_add1r addzC lez_add2r imin.
      rewrite addzC ltz_add2l jmax /=.      
      rewrite lez_eqVlt addzC (eq_sym 0) auxj /=.
      rewrite -lez_add1r addzC lez_add2r jmin.
qed.

lemma nosmt count_rem_eq ['a] (p : 'a -> bool) (s : 'a list) x:
  count p s = b2i (p x /\ mem s x) + count p (rem x s).
proof.
  case (mem s x) => //= sx.
  + apply count_rem => //.
  + rewrite /b2i /= rem_id //.
qed.

lemma nosmt size_rem_eq (x : 'a) s:
  size (rem x s) = (size s) - b2i (mem s x).
proof.
  case (mem s x) => /= sx.
  + rewrite /b2i /= size_rem //.
  + rewrite /b2i /= rem_id //.
qed.

lemma nosmt size_rem_eq_alt (x : 'a) s:
  size s = size (rem x s) + b2i (mem s x).
proof.
  rewrite -(eqz_add2r (-b2i (mem s x))).
  rewrite -addzA addzN addz0 eq_sym size_rem_eq //.
qed.

lemma nosmt remC (s: 'a list) x y:
  rem y (rem x s) = rem x (rem y s).
proof.
  case (x = y) => // x_neq_y.
  elim s => // e l ibase.
  rewrite /=.
  case (e = x) => ex; first by rewrite ex x_neq_y //=. 
  case (e = y) => // ey.
  rewrite ex //=.
qed.

lemma nosmt perm_rem_cons (s: 'a list) x y:
  mem s x /\ x <> y => perm_eq (x :: rem y (rem x s)) (rem y (x :: (rem x s))).
proof.
  move => [sx x_neq_y].
  rewrite /= x_neq_y /= // perm_eq_refl.
qed.

lemma nosmt subseq_mem (s1 s2: 'a list):
  subseq s1 s2 => forall x, mem s1 x => mem s2 x.
proof.
  apply absurd => /=.
  rewrite negb_forall /=.
  move => [e].
  rewrite negb_imply /=.
  elim: s2 s1 => [|y s2 ih] [|x s1] //=.
  rewrite negb_or.
  case (y = x) => //= y_x.
  - rewrite y_x.
    case (e = x) => //= e_x.
    apply ih.
  - case (e = y) => //= e_y.
    + case (e = x) => //= e_x.
      rewrite -e_x.
      have s1e: mem (e :: s1) e by rewrite in_cons //.
      move : s1e.
      apply (ih (e :: s1)) => //.
    + apply absurd => /=.
      move : (subseq_cons s1 x) => tr1 tr2.
      have tr3: subseq s1 s2 by rewrite (subseq_trans (x :: s1)).
      move : tr3. 
      apply absurd => /=; apply ih.
qed.

lemma nosmt subseq_uniq (s2 s1: 'a list):
  subseq s1 s2 /\ uniq s2 => uniq s1.
proof.
  elim: s2 s1 => [|y ys ih] [|x xs] //.
  move : (ih (x :: xs)) => /= ih_xxs.
  move : (ih xs) => /= ih_xs.
  case (y = x) => y_x.
  - rewrite y_x.
    move => [ss [ysx ys_u]].
    have mems: forall z, !mem ys z => !mem xs z by move => z; rewrite implybNN; move : z; apply subseq_mem => //.
    split; first by apply mems => //.
    apply ih_xs => //.
  - rewrite andbC -andbA.
    move => [useless].
    rewrite andbC.
    apply ih_xxs => //.
qed.

lemma nosmt subseq_uniq_alt (s1 s2: 'a list):
  subseq s1 s2 /\ ! uniq s1 => ! uniq s2.
proof.
  rewrite andbC -andWI.
  apply absurd.
  rewrite negb_imply /=.
  apply subseq_uniq.
qed.

lemma nosmt filter_eq (s: 'a list) f f':
  (filter f s = filter f' s) <=> (forall x, (mem s x => (f x <=> f' x))).
proof.
  split; last by apply eq_in_filter.
  apply absurd.
  rewrite negb_forall /=.
  move => [x].
  rewrite negb_imply -eq_iff.
  elim s => // z zs ibase.
  case (z = x) => //= z_x.
  - rewrite z_x /=.
    move => f_f'_x.
    case (f x) => //= f_x.
    + have f'_x: (!(f' x)) by rewrite -(negP (f' x)) -f_f'_x f_x eq_sym eqT //.
      rewrite f'_x /=.
      pose s1 := x :: filter f zs;
        pose s2 := filter f' zs.
      have : (mem s1 x) by trivial.
      have : (!mem s2 x) by rewrite mem_filter negb_and f'_x //.
      elim: s2 s1 => [|t ts ih] [|w ws] //=.
      rewrite negb_or negb_and.
      move => [x_t tsx].
      case (x = w) => //= x_w.
      * rewrite -x_w x_t //=.
      * move => wsx; right; apply (ih ws) => //.
    + have f'_x: f' x by move : f_f'_x; rewrite f_x //= eq_sym neqF //=.
      rewrite f'_x /= eq_sym.
      pose s1 := x :: filter f' zs;
        pose s2 := filter f zs.
      have : (mem s1 x) by trivial.
      have : (!mem s2 x) by rewrite mem_filter negb_and f_x //.
      elim: s2 s1 => [|t ts ih] [|w ws] //=.
      rewrite negb_or negb_and.
      move => [x_t tsx].
      case (x = w) => //= x_w.
      * rewrite -x_w x_t //=.
      * move => wsx; right; apply (ih ws) => //.
  - rewrite eq_sym z_x /=.
    move => [zsx f_f'_x].
    move : ibase; rewrite zsx f_f'_x /= => iconcl.
    case (f z) => //= f_z.
    + case (f' z) => //= f'_z.
      pose s1 := z :: filter f zs;
         pose s2 := filter f' zs.
      have : (mem s1 z) by trivial.
      have : (!mem s2 z) by rewrite mem_filter negb_and f'_z //.
      elim: s2 s1 => [|t ts ih] [|w ws] //=.
      rewrite negb_or negb_and.
      move => [z_t tsx].
      case (z = w) => //= z_w.
      * rewrite -z_w z_t //=.
      * move => wsz; right; apply (ih ws) => //.
    + case (f' z) => //= f'_z.
      rewrite eq_sym.
      pose s1 := z :: filter f' zs;
        pose s2 := filter f zs.
      have : (mem s1 z) by trivial.
      have : (!mem s2 z) by rewrite mem_filter negb_and f_z //.
      elim: s2 s1 => [|t ts ih] [|w ws] //=.
      rewrite negb_or negb_and.
      move => [z_t tsx].
      case (z = w) => //= z_w.
      * rewrite -z_w z_t //=.
      * move => wsz; right; apply (ih ws) => //.
qed.

lemma nosmt subseq_uniq_filter (s2 s1: 'a list):
  subseq s1 s2 /\ uniq s2 => s1 = filter (fun x => has (pred1 x) s1) s2.
proof.
  elim: s2 s1 => [|y ys ih] [|x xs] //. smt.
  move : (ih (x :: xs)) => /= ih_xxs.
  move : (ih xs) => /= ih_xs.
  case (y = x) => y_x.
  - rewrite y_x.
    move => [ss [ysx ys_u]].
    have mems: forall z, !mem ys z => !mem xs z by move => z; rewrite implybNN; move : z; apply subseq_mem => //.
    have xs_u: uniq xs by apply (subseq_uniq ys) => //.
    rewrite /pred1 /=.
    move : ih_xs; rewrite ss ys_u /= => ic_xs.
    pose d := filter (fun (x0 : 'a) => x = x0 \/ has (pred1 x0) xs) ys.
    rewrite ic_xs filter_eq /d => z ysz.
    rewrite -eq_iff /=.
    case (x = z) => //=.
  - rewrite /pred1 (eq_sym x y) y_x /=.
    move => [ss [ysy ys_u]].
    move : (subseq_cons xs x) => ss_xs_xxs.
    move : (subseq_trans (x :: xs) xs ys).
    rewrite ss_xs_xxs ss /= => ss_xs_ys.
    have xsy: !mem xs y by move : ysy; apply absurd => /= xsy; rewrite (subseq_mem xs ys) //.
    have ->: !(has (pred1 y) xs) by rewrite hasPn /pred1 /=; move => z; apply absurd => //.
    move : ih_xxs; rewrite ss ys_u /= => ic_xxs.
    rewrite ic_xxs //.
qed.

lemma nosmt subseq_uniq_perm (s2 s1: 'a list):
  subseq s1 s2 /\ uniq s2 => perm_eq s2 (s1 ++ (filter (fun x => !has (pred1 x) s1) s2)).
proof.
  move => [ss s2_u].
  pose d := filter (fun (x : 'a) => !has (pred1 x) s1) s2.
  rewrite (subseq_uniq_filter s2 s1) // /d.
  move : (perm_filterC (fun (x : 'a) => has (pred1 x) s1) s2).
  rewrite /predC perm_eq_sym //.
qed.

lemma nosmt perm_rem_rem (s1 s2: 'a list):
  perm_eq s1 s2 => forall x, (perm_eq (rem x s1) (rem x s2)).
proof.
  move => s1_peq_s2 x.
  move : (perm_eq_mem s1 s2).
  rewrite s1_peq_s2 //= => mem_sync.
  move : (mem_sync x) => mem_sync_x.
  rewrite allP /= => y memrem_y.
  have memy: mem (s1 ++ s2) y.
    move : memrem_y.
    rewrite 2!mem_cat /=.
    case (mem (rem x s1) y) => /= pre.
    + rewrite (mem_rem x s1) //.
    + move => hyp; rewrite (mem_rem x s2) //.
  move : s1_peq_s2.
  rewrite /perm_eq allP /= => s1_peq_s2. 
  move : (s1_peq_s2 y).
  rewrite memy /= => cc.
  rewrite -(eqz_add2l (b2i ((pred1 y) x /\ mem s1 x))) -(count_rem_eq (pred1 y)) addzC -(eqz_add2l (b2i ((pred1 y) x /\ mem s2 x))) addzA -(count_rem_eq (pred1 y)) addzC cc eqz_add2l /b2i /pred1 /= mem_sync //=.
qed.

lemma nosmt uniq_rem_cons (s: 'a list):
  uniq s => (forall x y, (mem s x /\ mem s y /\ x <> y) => perm_eq (x :: y :: (rem y (rem x s))) s).
proof.
  move => s_u x y [sx [sy x_y]].
  move : (mem_mem_rem x s y).
  rewrite sy x_y /= => sDx_y.
  rewrite perm_eqP.
  move : x_y.
  apply absurd.
  rewrite negb_forall /=.
  move => [p].
  rewrite (count_rem_eq p s x) (count_rem_eq p (rem x s) y) sx sDx_y //=.
qed.

lemma nosmt head_cat (s1 s2: 'a list) z0:
  s1 <> [] => head z0 (s1 ++ s2) = head z0 s1 by elim s1 => //.

lemma nosmt nth_head (x0 : 'a) s : nth x0 s 0 = head x0 s.
proof. by case: s => //= x s; rewrite /#. qed.

lemma all_filter (s: 'a list) p q:
  all p s => all p (filter q s).
proof. rewrite 2!allP /= => pre x; rewrite mem_filter; move => [_ xs]; apply pre => //. qed.

lemma nosmt fcomp_listr (s: 'a list) (f: 'a -> 'a) z0:
  (forall n, 0 < n < size s => nth z0 s n = f (nth z0 s (n - 1))) <=> (forall n, 0 <= n < size s => nth z0 s n = (f^n) (head z0 s)).
proof.
  elim : s => //=.
  * split => pre n.
    - apply absurd => _.
      case (0 <= n) => //= n0.
      rewrite -lezNgt n0 //.
    - apply absurd => _.
      case (0 < n) => //= n0.
      rewrite -lezNgt lez_eqVlt n0 //.
  * move => y ys.
    + case (2 <= size (y :: ys)) => //= pre1.
      rewrite iffE; move => [h_left h_right].
      split => pre n.
      - have fy: f y = head z0 ys by move : (pre 1); rewrite /= -lez_add1r /= pre1 /= nth_head eq_sym //.
        case (n = 0) => n0.
        * rewrite n0 fcompE //.
        * rewrite fcompE n0 /= fy -nth_head.
          move => hcompr; move : (hcompr).
          rewrite (lez_eqVlt 0) (eq_sym 0) n0 /=; move => [nat_n nlt].
          rewrite h_left. (* two hypotheses to prove *)
          + move => m [m_pos m_sys].
            have m0: m <> 0 by rewrite neq_ltz m_pos //.
            have [sucm_pos sucm_sys]: 0 < m + 1 < 1 + size ys by rewrite addzC ltz_add2l m_sys -lez_add1r lez_add2l lez_eqVlt m_pos eq_sym m0 //.
            move : (pre (m + 1)); rewrite m0 /= -(eqz_add2r 1) sucm_pos /=.
            have ->/=: m + 2 <> 1 by rewrite eq_sym addzC -addz0 -(eqz_add2l (-1)) /= addzC neq_ltz sucm_pos //.
            rewrite sucm_sys //.
          + rewrite -(lez_add2l 1) /= -addz0 lez_add1r nat_n -(ltz_add2l 1) /= nlt //.
          rewrite nth_head //.
      - have fy: f y = (head z0 ys) by move : (pre 1); rewrite /= -lez_add1r /= pre1 /= nth_head eq_sym fcomp1 //.
        move => [n_pos nlt].
        have ->/=: n <> 0 by rewrite neq_ltz n_pos //.
        case (n = 1) => pren1; first by rewrite pren1 /= fy nth_head //.
        have nat_n: 0 <= n by rewrite lez_eqVlt n_pos //.
        rewrite h_right.  (* two hypotheses to prove *)
        + move => m [nat_m m_sys].
          have nat_sucm: 0 <= m + 1 by rewrite addz_ge0 //.
          have sucm_pos: 0 < m + 1 by rewrite -lez_add1r (addzC m) lez_add2l nat_m //.
          move : (pre (m + 1)); rewrite /= -(eqz_add2r 1) nat_sucm /=.
          have ->/=: m + 2 <> 1 by rewrite eq_sym addzC -addz0 -(eqz_add2l (-1)) /= addzC neq_ltz sucm_pos //.
          rewrite fcompE.
          have ->/=: m + 1 <> 0 by rewrite eq_sym addzC -addz0 /= neq_ltz addzC sucm_pos //.
          rewrite fy // addzC ltz_add2l m_sys //.
        + rewrite -(ltz_add2l 1) /= ltz_def pren1 -addz0 lez_add1r n_pos /= -(ltz_add2l 1) /= nlt //.
        rewrite -(eqz_add2r 1) /= pren1 //.
    + move : pre1 (size_ge0 ys).
      rewrite -ltzNge -(ltz_add2l (-1)) /= -lez_add1r -(lez_add2l (-1)) /= andWI -eqz_leq size_eq0 => ys0.
      rewrite ys0 /= iffE; move => [h_left h_right].
      split => pre n.
      - rewrite -(ltz_add2l (-1)) /= -lez_add1r /= andaE -eqz_leq eq_sym => n0.
        rewrite n0 fcompE //. 
      - apply absurd => _.
        case (0 < n) => //= n0.
        rewrite -lezNgt -addz0 lez_add1r n0 //.
qed.

lemma nosmt fcomp_listl (s: 'a list) (f: 'a -> 'a) z0:
  (forall n, 0 < n < size s => nth z0 s (n - 1) = f (nth z0 s n)) <=> (forall n, 0 <= n < size s => let l = nth z0 s (size s - 1) in nth z0 s n = (f^(size s - n - 1)) l).
proof.
  elim/last_ind : s => //=.
  * split => pre n.
    - apply absurd => _.
      case (0 <= n) => //= n0.
      rewrite -lezNgt n0 //.
    - apply absurd => _.
      case (0 < n) => //= n0.
      rewrite -lezNgt lez_eqVlt n0 //.
  * move => ys y.
    pose s := rcons ys y.
    pose l := last z0 ys.
    have sys_ss: size s = size ys + 1 by rewrite size_rcons.
    have yl: y = last z0 s by rewrite -nth_last nth_rcons sys_ss //.
    rewrite iffE; move => [h_left h_right].
    + case (2 <= size s) => // pre1.
      have pre1ys: 1 <= size ys by rewrite -(lez_add2r 1) -sys_ss //.
      split => pre n.
      - have fy: f y = l by move : (pre (size s - 1)); rewrite /= -lez_add1r /= sys_ss /= pre1ys -(ltz_add2l (-size ys)) /= addzA /= nth_rcons -(ltz_add2l (-size ys)) /= addzA /= nth_rcons -(ltz_add2l (-size ys)) /= nth_last eq_sym //.
        move => [nat_n nss].
        case (n = size s - 1) => n_prelast.
        * rewrite n_prelast nth_rcons sys_ss /= -addzA (addzC (size ys)) addzA -(addzA 1) fcomp0 /idfun //.
        * have nsys: n < size ys by move : n_prelast nss; rewrite sys_ss /= => n_prelast; rewrite /= -lez_add1r addzC -(lez_add2r (-1)) /= lez_eqVlt n_prelast //.
          rewrite nth_rcons nsys /=.
          rewrite h_left => //.
            move => m [m_pos msys].
            have mss: m < size s by rewrite sys_ss -lez_add1r addzC -(lez_add2r (-1)) /= lez_eqVlt msys //.
            move : (pre m); rewrite nth_rcons /= m_pos mss /=.
            rewrite -(eqz_add2r 1) /= addzC -lez_add1r addzA lez_eqVlt msys /= nth_rcons msys //.
          rewrite eq_sym fcompE /=.
          have ->/=: size s - n - 1 <> 0. rewrite (addzC (size s)) -(eqz_add2l n) 2!addzA /= addzC eq_sym n_prelast //.
          rewrite sys_ss -addzA (addzC (-n)) addzA /= -addzA (addzC (-1)) addzA.
          rewrite nth_last nth_rcons /= fy /l //.
      - have fy: f y = l. rewrite yl /l. move : (pre (size s - 2)).
          rewrite -(lez_add2r 2) -(ltz_add2l (-size s)) /= pre1 addzA /=.
          rewrite nth_last sys_ss /=.
          rewrite -addzA -opprB (addzC _ 1) /= opprB nth_rcons -(ltz_add2r 1) -(ltz_add2l (-size ys)) /= addzA /= -nth_last.
          rewrite nth_rcons sys_ss /= nth_last eq_sym -addzA /= fcomp1 //.
        move => [n_pos nss].
        have nat_n: 0 <= n by rewrite lez_eqVlt n_pos //.
        case (n = size ys) => n_prelast.
        + rewrite n_prelast nth_rcons /= -(ltz_add2r 1) -(ltz_add2l (-size ys)) /= addzA /=.
          rewrite nth_rcons /= fy /l nth_last //.
        + rewrite nth_rcons.
          rewrite h_right => //.  (* two hypotheses to prove *)
          - move => m [nat_m msys].
            have nat_sucm: 0 <= m + 1 by rewrite addz_ge0 //.
            have sucm_pos: 0 < m + 1 by rewrite -lez_add1r (addzC m) lez_add2l nat_m //.
            have mss: m < size s by rewrite sys_ss -lez_add1r addzC -(lez_add2r (-1)) /= lez_eqVlt msys //.
            move : (pre m); rewrite /= nat_m mss /=.
            rewrite nth_rcons msys /= nth_rcons sys_ss fcompE /=.
            rewrite -addzA (addzC (-m)) addzA /= -(eqz_add2r m) /= -addzA /=.
            have ->/=: size ys <> m by rewrite neq_ltz msys //.
            rewrite -addzA (addzC (-m)) addzA /= -addzA (addzC (-1)) addzA.
            rewrite fy /l nth_last //.
          - rewrite n_pos; move : n_prelast nss; rewrite sys_ss /= => n_prelast; rewrite /= -lez_add1r addzC -(lez_add2r (-1)) /= lez_eqVlt n_prelast //.
          rewrite -(ltz_add2l 1) -(eqz_add2l 1) /= addzC -sys_ss nss /= nth_rcons ltz_def n_prelast (eq_sym _ n) n_prelast /=.
          rewrite -(lez_add2l 1) lez_add1r addzC -sys_ss nss //.
    + move : pre1 (size_ge0 ys).
      rewrite sys_ss -ltzNge -(ltz_add2l (-1)) /= -lez_add1r -(lez_add2l (-1)) /= andWI -eqz_leq size_eq0 => ys0.
      rewrite ys0 /= iffE /=.
      split => pre n.
      - rewrite -(ltz_add2l (-1)) /= -lez_add1r /= andaE -eqz_leq eq_sym => n0.
        rewrite n0 fcompE //. 
      - apply absurd => _.
        case (0 < n) => //= n0.
        rewrite -lezNgt -addz0 lez_add1r n0 //.
qed.

lemma nosmt fcomp_listl_head (s: 'a list) (f: 'a -> 'a) z0:
  (forall n, 0 <= n < size s => let l = nth z0 s (size s - 1) in nth z0 s n = (f^(size s - n - 1)) l) => (forall n, 0 <= n < size s => head z0 s = (f^n) (nth z0 s n)).
proof.
  move => pre n [nat_n nss].
  have : head z0 s = (f^(size s - 1)) (last z0 s).
    move : (pre 0) => /=.
    case (n = 0) => n0.
    + rewrite -n0 nss n0 nth_head nth_last //.
    + move : nat_n; rewrite lez_eqVlt eq_sym n0 /= => npos; rewrite (ltz_trans n) // nth_head nth_last //.
  have ->: size s - 1 = (size s - n - 1) + n by rewrite -addzA (addzC _ n) -addzA (addzA (-n)) //.
  pose j := size s - n - 1.
  rewrite addzC -fcomp_add /(\o) => //.
    move : (size_ge0 s) => ss; rewrite /j -(lez_add2r 1) /= -addz0 lez_add1r -(ltz_add2r n) -addzA //=.
  move : (pre n); rewrite nat_n nss /= => pren preh.
  rewrite preh pren /j nth_last //.
qed.

lemma nosmt fcomp_inj_listl_head (s: 'a list) (f: 'a -> 'a) z0:
  injective f =>
  (forall n, 0 <= n < size s => let l = nth z0 s (size s - 1) in nth z0 s n = (f^(size s - n - 1)) l) <=> (forall n, 0 <= n < size s => head z0 s = (f^n) (nth z0 s n)).
proof.
    move => inj_f.
    split; first by move => pre; apply fcomp_listl_head => //.
    case (2 <= size s).
    - elim s => //=.
      + move => y ys ibase.
        move => ss2 pre n [nat_n nss].
        have ys0: size ys <> 0 by rewrite neq_ltz; right; rewrite -(ltz_add2l 1) -lez_add1r /= ss2 //.
        rewrite ys0 eq_sym -addzA addzC addzA /= addzC.
        move : (pre 1); rewrite fcomp1 nth_head /= -(ltz_add2l (-1)) /= ltz_def ys0 size_ge0 /= => yf.
        case (n = 0) => n0; first by move : (pre (size ys)); rewrite /= -(ltz_add2r (-size ys)) -addzA /= size_ge0 ys0 n0 /= eq_sym addzC //.
        case (n = size ys) => nsys0; first by rewrite nsys0 fcomp0 /idfun /= addzC //.
        have nsys: n < size ys by move : nsys0 nss; rewrite /= => nsys0; rewrite /= -lez_add1r addzC -(lez_add2r (-1)) /= lez_eqVlt nsys0 //.
        move : (pre 2).
        have sys1: size ys <> 1 by move : nsys; apply absurd => /= sys0; rewrite sys0 -lezNgt -addz0 lez_add1r ltz_def n0 nat_n.
        rewrite yf /=.
        have ->/=: 2 < 1 + size ys by rewrite ltz_def ss2 -(eqz_add2l (-1)) //.
        move => f1f2.
        have ibase_pre: (forall (n : int), 0 <= n < size ys => head z0 ys = (^) f n (nth z0 ys n)).
          move => m [nat_m msys].
          have nat_sucm: 0 <= m + 1 by rewrite addz_ge0 //.
          have sucm_pos: 0 < m + 1 by rewrite -lez_add1r (addzC m) lez_add2l nat_m //.
          have mss: m < 1 + size ys by rewrite -lez_add1r addzC -(lez_add2r (-1)) /= lez_eqVlt msys //.
          move : (pre (m + 1)); rewrite /= nat_sucm addzC ltz_add2l msys /=.
          rewrite addzC fcompE (eq_sym _ 0) eqz_leq nat_sucm /= addzC lez_add1r ltzNge nat_m /=.
          rewrite fcompC_ext // yf; apply inj_f.
        have sys2: 2 <= size ys by (have ->: 2 = 1 + 1 by trivial); rewrite -addz0 lez_add1r /= ltz_def sys1 -addz0 lez_add1r ltz_def ys0 size_ge0 //.
        move : (ibase sys2 ibase_pre (n - 1)); rewrite /=.
        rewrite -(lez_add2r 1) -(ltz_add2r 1) /= -addz0 lez_add1r ltz_def n0 nat_n addzC /= nss //= eq_sym.
        rewrite opprB (addzC 1) addzA /= (addzC (-1)) //.
    - rewrite -ltzNge /= => slt pre n [nat_n nss].
      have s1: size s = 1 by rewrite eqz_leq -(lez_add2l 1) lez_add1r slt /= -addz0 lez_add1r ltz_def size_ge0 /=; move : nss; apply absurd => /= ss0; rewrite ss0 -lezNgt nat_n.
      have ->: n = 0 by rewrite eqz_leq nat_n -(lez_add2l 1) lez_add1r -s1 nss //.
      rewrite s1 fcomp0 /idfun //.
qed.

lemma nosmt fcomp_listr_listl (s: 'a list) (f g: 'a -> 'a) z0:
  cancel f g /\ cancel g f => forall n, 0 < n < size s => (nth z0 s n = f (nth z0 s (n - 1))) <=> (nth z0 s (n - 1) = g (nth z0 s n)).
proof.
  move => [can_fg can_gf] n _.
  rewrite -(can_eq g f) // can_fg eq_sym //.
qed.

lemma nosmt uniq_index (s: 'a list):
  uniq s => forall x y, index x s = index y s <=> x = y \/ (!mem s x /\ !mem s y).
proof.
  elim s => //= e l ibase.
  move => [emem luniq] x y.
  rewrite 2!index_cons.
  move : ibase; rewrite luniq /= => ibase.
  case (x = e) => //= xe.
  * case (y = e) => //= ye.
    rewrite xe (eq_sym e) ye /=.
    rewrite neq_ltz; left.
    rewrite -lez_add1r addzC lez_add2r index_ge0 //.
  * case (y = e) => //= ye.
    move : (ibase x y).
    rewrite ye xe /=.
    move : emem (index_size e l); rewrite -index_mem -lezNgt andWI -eqz_leq => se.
    case (mem l x) => /= xmem.
    + rewrite -se eqz_leq addzC index_size /= -ltzNge.
      rewrite index_mem xmem /= neq_ltz; right.
      rewrite -lez_add1r lez_add2l index_ge0 //.
    + move : xmem (index_size x l); rewrite -index_mem -lezNgt andWI -eqz_leq => sx.
      rewrite -se -sx /= neq_ltz; right.
      rewrite -lez_add1r addzC lez_add2r size_ge0 //.
  rewrite eqz_add2r; apply ibase.
qed.

(* -------------------------------------------------------------------- *)
(*                             Indexed                                  *)
(* -------------------------------------------------------------------- *)
pred indexed ['a] (s: (int * 'a) list) = forall i, 0 <= i < size s => nth witness (unzip1 s) i = i.

lemma nosmt indexed_cons (s: (int * 'a) list) x:
  indexed (x :: s) <=> x.`1 = 0 /\ forall i, 0 <= i < size s => nth witness (unzip1 s) i = i + 1.
proof.
  rewrite /indexed; split.
  - (* => *)
    move => pre; split.
    + move : (pre 0).
      rewrite /= -lez_add1r lez_add2l size_ge0 //.
    + move => i [imin imax].
      move : (pre (i + 1)).
      rewrite /= addzC ltz_add2l imax /=.
      rewrite lez_eqVlt -lez_add1r lez_add2l imin /=.
      rewrite (eqz_leq _ 0) (lez_eqVlt 0) -lez_add1r lez_add2l imin /=.
      rewrite lezNgt -lez_add1r lez_add2l imin /=.
      trivial.
  - (* <= *)
    move => [fst_el others].
    move => /= i [imin imax].
    case (i = 0) => //= i0.
    move : (others (i - 1)).
    rewrite -(ltz_add2r 1) /= (addzC _ 1) imax /=.
    rewrite -(lez_add2r 1) /= lezNgt.
    rewrite -lez_add1r -addz0 lez_add2l lez_eqVlt i0 /= -lezNgt imin //.
qed.

lemma nosmt indexed_rcons (s: (int * 'a) list) x:
  fst x = size s => indexed s => indexed (rcons s x).
proof.
  move => right_idx pre.
  rewrite -cats1 /indexed size_cat /= => i [imin imax].
  rewrite map_cat nth_cat size_map.
  case (i = size s) => // ilast.
  move : (pre i).
  rewrite imin ltz_def (eq_sym (size s)) ilast /=.
  rewrite -(lez_add2l 1) lez_add1r addzC imax //.
qed.

lemma nosmt indexed_fst_uniq (s: (int * 'a) list):
  indexed s => uniq (unzip1 s).
proof.
  move => pre; move : (pre).
  rewrite uniq_inj_nth /indexed.
  apply absurd.
  rewrite negb_forall /=; move => [i].
  rewrite negb_forall /=; move => [j].
  rewrite 3!negb_imply size_map.
  move => [[imin imax]] [[jmin jmax]].
  rewrite (nth_map witness) // (nth_map witness) //=; move => [f_eq] ij_neq.
  move : (pre i); rewrite imin imax /= (nth_map witness) //= => paradoxi.
  move : (pre j); rewrite jmin jmax /= (nth_map witness) //= => paradoxj.
  move : f_eq; rewrite paradoxi paradoxj ij_neq //.
qed.

lemma nosmt indexed_uniq (s: (int * 'a) list):
  indexed s => uniq s.
proof.
  move => pre; move : (pre).
  rewrite uniq_inj_nth /indexed.
  apply absurd.
  rewrite negb_forall /=; move => [i].
  rewrite negb_forall /=; move => [j].
  rewrite 3!negb_imply.
  move => [[imin imax]] [[jmin jmax]].
  pose pi := nth witness s i;
    pose pj := nth witness s j.
  rewrite (pairS pi) (pairS pj) /= andaE; move => [[idx_eq _]] ij_neq.
  move : (pre i); rewrite imin imax /= (nth_map witness) //= => paradoxi.
  move : (pre j); rewrite jmin jmax /= (nth_map witness) //= => paradoxj.
  move : idx_eq; rewrite /pi /pj paradoxi paradoxj ij_neq //.
qed.

lemma nosmt indexed_all (s: (int * 'a) list):
  indexed s => all (fun x, fst x = index x s) s.
proof.
  rewrite /indexed allP.
  move => pre x.
  rewrite -index_mem => ilt.
  move : (pre (index x s)).
  rewrite (nth_map witness) // index_ge0 ilt /= nth_index //.
    rewrite -index_mem //.
qed.
