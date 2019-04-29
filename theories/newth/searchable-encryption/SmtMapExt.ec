(* --------------------------------------------------------------------
 * Copyright (c) - 2018 - Roberto Metere <r.metere2@ncl.ac.uk>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import FSet SmtMap Int List.
require import IntExt ListExt TacticsExt.

op remlast_none (m: ('a, 'b list) fmap) x = if dom m x then (size (oget m.[x]) <= 1) ? rem m x : m.[x <- betail (oget m.[x])] else m.
op remlast (m: ('a, 'b list) fmap) x = dom m x ? m.[x <- betail (oget m.[x])] : m.

lemma remlast_remlast_none (m: ('a, 'b list) fmap):
  forall x, dom m x /\ 1 < size (oget m.[x]) => remlast m x = remlast_none m x.
proof.
  move => x [mx size_mx].
  rewrite ltzNge in size_mx.
  rewrite /remlast /remlast_none mx size_mx //=.
qed.

lemma nosmt dom_oget (A: ('a, 'b) fmap) x:
  dom A x <=> A.[x] = Some (oget A.[x]).
proof.
  split; first by move => A_x; rewrite -Core.some_oget //.
  move => A_x; rewrite domE A_x //.
qed.

lemma dom_exists (A: ('a, 'b) fmap) x:
  dom A x <=> exists y, A.[x] = Some y.
proof.
  split; first by move => A_x; exists (oget A.[x]); rewrite -Core.some_oget //.
  move => [y] => A_x; rewrite domE A_x //.
qed.

lemma rng_frng_eq (A: ('a, 'b) fmap) (B : ('c, 'b) fmap):
  rng A = rng B <=> frng A = frng B.
proof.
  split.
  + rewrite (fun_ext (rng A) (rng B)) /(==); move => h_in; rewrite fsetP; move => x'; rewrite 2!mem_frng -eq_iff h_in //.
  + rewrite (fun_ext (rng A) (rng B)) /(==) fsetP; move => h_in x; rewrite -2!mem_frng eq_iff h_in //.
qed.

lemma rng_rem ['a 'b] (A : ('a, 'b) fmap) x y :
  rng (SmtMap.rem A x) y <=> exists x', x' <> x /\ A.[x'] = Some(y).
proof.
  rewrite rngE /=; split.
  + move => [x' hyp]; exists x'.
    have x'_neq_x: x' <> x by move : hyp; apply absurd; simplify; move => x_eq_x'; rewrite x_eq_x' remE //.
    rewrite -hyp remE x'_neq_x //.
  + move => [x'] [x'_neq_x hyp]; exists x'; rewrite -hyp remE x'_neq_x //.
qed.

lemma mem_set_rem ['a 'b] (m : ('a, 'b) fmap) x y y' :
  mem (frng m.[x <- y']) y /\ y <> y' => mem (frng (rem m x)) y.
proof.
  rewrite 2!mem_frng rngE /=.
  move => [[x' my] y_neq_y'].
  rewrite rngE /=.
  have x'_neq_x: x' <> x by move : my; apply absurd => /=; move => x_eq_x'; rewrite x_eq_x' get_set_sameE /= eq_sym //.
  exists x'.
  rewrite remE x'_neq_x /= -(get_set_neqE m x x' y') //.
qed.

lemma mem_rem_set ['a 'b] (m : ('a, 'b) fmap) x y y' :
  mem (frng (SmtMap.rem m x)) y => mem (frng m.[x <- y']) y.
proof.
  rewrite 2!mem_frng rngE /=.
  move => [x' my].
  have x'_neq_x: x' <> x by move : my; apply absurd => /=; move => x_eq_x'; rewrite x_eq_x' remE //.
  move : my; rewrite remE x'_neq_x /=; move => my.
  rewrite rngE //.
  exists x'.
  rewrite get_set_neqE //.
qed.

lemma dom_mem_frng ['a 'b] (m: ('a, 'b) fmap) x y y':
  !dom m x /\ mem (frng m) y => mem (frng m.[x <- y']) y.
proof.
  move => [m_x fm_x].
  rewrite mem_frng rngE /=.
  case (y = y') => yy'.
  + exists x.
    rewrite yy' get_set_sameE //.
  + rewrite domE /= in m_x.
    move : fm_x.
    rewrite mem_frng rngE /=.
    move => [x'] m_x'.
    have x'x: (x' <> x).
      move : m_x'.
      apply absurd => /= ah.
      rewrite ah m_x //.
    exists x'.
    rewrite get_set_neqE //.
qed.

lemma oflist_nil (l: ('a * 'b) list):
  oflist l = oflist [] <=> l = [].
proof.
by smt.
(*
  split.
  rewrite fmapP; apply absurd.
  elim: l; trivial.
  move => x l nilcase /=.
  apply negb_forall; exists (fst x) => /=.
  rewrite (get_oflist []) get_oflist /assoc => /=.
  by have ->: index x.`1 (x.`1 :: map fst l) = 0.
  trivial.
*)
qed.

op olast (xs : 'a list) : 'a option =
with xs = []      => None
with xs = y :: ys => Some (last y ys).

lemma filter_nil (m: ('a, 'b) fmap) f:
  (filter f m) = empty <=> forall a, (dom m a) => !f a (oget m.[a]).
proof.
  split.
  + apply absurd => /=.
    rewrite negb_forall /=.
    move => [a].
    rewrite negb_imply /= domE /=.
    move => [a_m].
    have [x m_x]: exists x, m.[a] = Some x by exists (oget m.[a]); rewrite -Core.some_oget //.
    rewrite m_x Core.oget_some.
    move => f_a_x.
    rewrite -fmap_eqP negb_forall /=.
    exists a.
    rewrite filterE emptyE m_x /= f_a_x //=.
  + apply absurd => /=.
    rewrite -fmap_eqP 2!negb_forall /=.
    move => [a fnone].
    exists a.
    move : fnone.
    apply absurd => /=.
    case (dom m a) => a_m /=.
    * have [x m_x]: exists x, m.[a] = Some x by exists (oget m.[a]); rewrite -Core.some_oget //.
      rewrite m_x Core.oget_some.
      move => f_a_x.
      rewrite filterE emptyE m_x /= f_a_x //=.
    * rewrite filterE emptyE.
      by have ->: m.[a] = None by trivial.
qed.

lemma filter_notnil (m: ('a, 'b) fmap) f:
  (filter f m) <> empty => m <> empty.
proof.
  rewrite -fmap_eqP negb_forall /=.
  move => [a].
  apply absurd => /= m0.
  rewrite -fmap_eqP in m0.
  rewrite filterE emptyE /=.
  by have ->: m.[a] = None by rewrite -(emptyE a); apply (m0 a).
qed.

lemma dom_filter (m : ('a,'b) fmap) f x:
  dom (filter f m) x <=> dom m x /\ f x (oget m.[x]).
proof.
  rewrite domE.
  split.
  + apply absurd => /=.
    rewrite negb_and.
    case (!(dom m x)) => /= x_m.
    - rewrite filterE.
      by have ->: m.[x] = None by trivial.
    - have [y m_x]: exists y, m.[x] = Some y by exists (oget m.[x]); rewrite -Core.some_oget //.
      rewrite m_x Core.oget_some.
      move => fC.
      rewrite filterE m_x /= fC //=.
  * move => [x_m].
    have [y m_x]: exists y, m.[x] = Some y by exists (oget m.[x]); rewrite -Core.some_oget //.
    rewrite m_x Core.oget_some => fV.
    rewrite filterE  m_x /= fV //=.
qed.

lemma dom_not_filter (m : ('a,'b) fmap) f x:
  !dom m x => !dom (filter f m) x.
proof.
  rewrite domE /= => m_x.
  rewrite domE /= filterE m_x //=.
qed.

lemma filter_set_notnil (m: ('a, 'b) fmap) f i x:
  (filter f m) <> empty /\ !(dom m i) => (filter f m.[i <- x]) <> empty.
proof.
  rewrite -fmap_eqP negb_forall /=.
  move => [[a f0] i_m].
  have a_i: a <> i by move : f0; rewrite filterE emptyE /=; rewrite domE /= in i_m; apply absurd => /= a_i; rewrite a_i i_m //.
  have c: oapp (f a) false m.[a] by move : f0; apply absurd => abshyp /=; rewrite filterE emptyE /= abshyp //.
  have c': oapp (f a) false m.[i <- x].[a] by rewrite get_set_neqE //.
  rewrite -fmap_eqP negb_forall /=.
  exists a.
  rewrite filterE emptyE /= c' //= get_set_neqE //.
  move : f0.
  rewrite filterE emptyE c //=.
qed.

lemma filter_dom_elems_notnil (m: ('a, 'b) fmap) f:
  (filter f m) <> empty <=> elems (fdom (filter f m)) <> [] by smt.

lemma filter_filter_eq (m: ('a, 'b) fmap) f f':
  filter f m = filter f' m <=> (forall x, (dom m x) => f x (oget m.[x]) = f' x (oget m.[x])).
proof.
  split.
  + rewrite -fmap_eqP => ff y.
    move : ff.
    apply absurd.
    rewrite negb_forall negb_imply /=.
    move => [y_m ff].
    exists y.
    rewrite 2!filterE.
    have [x m_x]: exists x, m.[y] = Some x by exists (oget m.[y]); rewrite -Core.some_oget //.
    move : ff.
    rewrite m_x Core.oget_some => ff /=.
    have <-: (!(f y x)) = (f' y x) by rewrite eqDnot //=.
    by case (f y x) => c.
  + rewrite -fmap_eqP.
    apply absurd.
    rewrite 2!negb_forall /=.
    move => [y ff].
    rewrite 2!filterE in ff.
    exists y.
    move : ff. apply absurd => /=.
    case (dom m y) => y_m /=.
    - have [x ->]: exists x, m.[y] = Some x by exists (oget m.[y]); rewrite -Core.some_oget //.
      rewrite Core.oget_some //= => ff.
      rewrite -ff; by case (f y x).
    - by have ->: m.[y] = None by trivial.
qed.

lemma dom_filter_set (m: ('a, 'b) fmap) f i x y:
  !(dom m i) => ((dom (filter f m) y => dom (filter f m.[i <- x]) y)) by smt.

lemma filter_filter (m: ('a, 'b list) fmap) (m': ('c, 'c) fmap) b' c' f f' g (h: 'a -> 'c) i x r r' t:
  g  = (fun (_ c : 'c) => c = c') =>
  r  = (fun a (b: 'b list) => mem (fdom (filter g m')         ) (h a)) =>
  r' = (fun a (b: 'b list) => mem (fdom (filter g m'.[i <- x])) (h a)) =>
  t  = (fun b => has ((=) b') b) =>
  f  = (fun a b => r  a b /\ t b) =>
  f' = (fun a b => r' a b /\ t b) =>
  !(dom m' i) => (x <> c') => filter f m <> empty => filter f' m <> empty.
proof.
  move => gdef rdef r'def tdef fdef f'def irrelevant x_c' notnil.
  have r_r': r === r'.
    move => a b.
    rewrite rdef r'def /= 2!mem_fdom 2!dom_filter /= 2!domE.
    case (h a = i) => ha_i; last by rewrite get_set_neqE.
    rewrite ha_i get_set_sameE Core.oget_some /=. 
    have ->: m'.[i] = None by trivial.
    rewrite /= gdef x_c' //=.
  have r_r'_alt: r = r' by rewrite fun_ext => a; rewrite fun_ext => b; exact r_r'.
  have f_f': f = f' by rewrite f'def fdef r_r'_alt //=.
  rewrite -f_f' //.
qed.

lemma filter_setnew (m: ('a, 'b) fmap) f a b:
  !(dom m a) => filter f m.[a <- b] = f a b ? (filter f m).[a <- b] : filter f m.
proof.
  move => new_el.
  move : (dom_not_filter m f a).
  rewrite new_el domE /= => new_el_filter.
  rewrite filter_set eq_sym.
  case (f a b) => //= fV.
  rewrite -fmap_eqP => x.
  rewrite remE.
  case (x = a) => //=.
qed.

lemma rem_filter (m: ('a, 'b) fmap) f a:
  (dom m a) => rem (filter f m) a = f a (oget m.[a]) ? filter f (rem m a) : filter f m.
proof.
  move => new_el.
  move : (dom_filter m f a).
  rewrite new_el domE /= => new_el_filter.
  case (f a (oget m.[a])) => //= fV.
  + rewrite -fmap_eqP => x.
    rewrite remE.
    case (x = a) => xa.
    + rewrite filterE remE xa //=.
    + rewrite 2!filterE remE xa //=.
  + rewrite -fmap_eqP => x.
    rewrite filterE remE.
  case (x = a) => xa //=.
  + rewrite xa /=.
    have ->: m.[a] = Some (oget m.[a]) by rewrite -Core.some_oget //.
    rewrite /= fV //=.
  + rewrite filterE //.
qed.

(*
 * Collisions in functions are just non-injective functions. For example:
 * ---

pred collision_exists (f: 'a -> 'b) = exists x y, x <> y /\ f x = f y.

lemma coll_inj (f: 'a -> 'b):
  collision_exists f <=> !injective f.
proof.
  rewrite /collision_exists /injective.
  split.
  * move => [x y coll].
    rewrite negb_forall /=; exists x.
    rewrite negb_forall /=; exists y.
    rewrite negb_imply andbC //.
  * rewrite negb_forall /=; move => [x].
    rewrite negb_forall /=; move => [y].
    rewrite negb_imply andbC => pre.
    exists x y.
    exact pre.
qed.

 * ---
 * We can see functions as fmaps.
 * Since collisions obviously exists in a fmap according with the predicate
 * stated above changing f with f.[x], the concept of collision "exists" is
 * not directly applicable, and we need the concept of collision for fmap:
 * Just slightly different a naming where we take extra care in fmap.
 * The subtlety comes from the fact that empty fmap actually is not "empty".
 * Its domain is every value that can belong or not to the "considered" domain,
 * and maps every value indeed. Precisely, to Some _ (if "considered") or None
 * otherwise.
 *
 * For completeness, if we naively instantiated
 * fmap_collision in a fmap the following way:
 * ---

pred fmap_collision (m: ('a, 'b) fmap) = collision_exists (Map.tofun (tomap m)).

lemma coll_empty (f: 'a -> 'b):
  forall (a b: 'a), a <> b => fmap_collision empty<: 'a, 'b>.
proof.
  move => a b a_b.
  rewrite /fmap_collision empty_valE /offun /collision_exists.
  exists a b.
  rewrite a_b 2!Map.cstE //.
qed.

 * ---
 * which obviously is "wrong", in the sense that it does not model what we want.
 *)

(* Note that  *)
op fmap_collision (m: ('a, 'b) fmap) = exists x y, dom m x /\ x <> y /\ m.[x] = m.[y].

lemma coll_dom (m: ('a, 'b) fmap) x y:
  dom m x /\ x <> y /\ m.[x] = m.[y] => dom m y.
proof.
  apply absurd.
  rewrite -mem_fdom fdomP /= => y0.
  rewrite y0 2!negb_and /=.
  case (dom m x) => //=.
  case (x = y) => //=.
qed.

lemma coll_setnew (m: ('a, 'b) fmap) x y:
  !dom m x =>
  fmap_collision m.[x <- y] <=> fmap_collision m \/ rng m y.
proof.
  move => x_notin_m; split => [[z z' [m_up_z [z'_neq_z]]]|].
  * (* => *)
    move : m_up_z.
    rewrite -mem_fdom fdom_set in_fsetU mem_fdom in_fset1.
    case (z = x) => z_x /=.
    + rewrite z_x get_set_sameE.
      have z'_x: z' <> x by rewrite -z_x eq_sym.
      rewrite (get_set_neqE m x z') //= eq_sym.
      move => hyp; right.
      rewrite rngE /=.
      exists z' => //.
    + case (z' = x) => z'_x.
      - rewrite z'_x get_set_sameE (get_set_neqE m x z) //=.
        move => mz z_some; right.
        rewrite rngE /=.
        exists z => //.
      - rewrite get_set_neqE //= get_set_neqE //=.
        move => mz hyp; left.
        rewrite /fmap_collision.
        exists z z'.
        rewrite z'_neq_z mz /=.
        exact hyp.
  * (* <= *)
    case (rng m y) => /=.
    + rewrite rngE /=.
      move => [z mz].
      rewrite /fmap_collision.
      exists z x.
      have mx: m.[x] = None by trivial.
      have mxz: m.[x] <> m.[z] by rewrite mx mz.
      have z_neq_x: z <> x by move : mxz; apply absurd => //=.
      rewrite z_neq_x get_set_neqE // get_set_eqE //= mz //= -mem_fdom fdom_set in_fsetU in_fset1 z_neq_x mem_fdom domE mz //=.
    + move => y_notfrom_m /=.
      rewrite /fmap_collision.
      move => [z z' [mz [z_neq_z' z_mapeq_z']]].
      have mzy: m.[z] <> Some y by move : y_notfrom_m; apply absurd => //=; move => m_up_z; rewrite rngE /=; exists z => //.
      have mx: m.[x] = None by trivial.
      have mxz: m.[x] <> m.[z] by rewrite mx eq_sym //.
      have z_neq_x: z <> x by move : mxz; apply absurd => //=.
      have z'_neq_x: z' <> x by rewrite z_mapeq_z' in mxz; move : mxz; apply absurd => //=.
      exists z z'.
      rewrite z_neq_z' /= (get_set_neqE m x z) //= (get_set_neqE m x z') //=.
rewrite -mem_fdom fdom_set in_fsetU in_fset1 z_mapeq_z' z_neq_x mem_fdom domE mz //=.
qed.

pred fmap_inj (m: ('a, 'b) fmap) =
  forall x y, dom m x /\ m.[x] = m.[y] => x = y.

lemma coll_inj (m: ('a, 'b) fmap):
  fmap_collision m <=> !fmap_inj m.
proof.
  rewrite /fmap_collision /fmap_inj.
  split.
  * move => [x y [mx [xy x_map_y]]].
    rewrite negb_forall /=; exists x.
    rewrite negb_forall /=; exists y.
    rewrite negb_imply //=.
  * rewrite negb_forall /=; move => [x].
    rewrite negb_forall /=; move => [y].
    rewrite negb_imply andbC.
    move => [xy [mx x_map_y]].
    exists x y => //.
qed.

lemma no_filter (m: ('a, 'b) fmap):
  filter (fun _ _ => true) m = m.
proof.
  rewrite -fmap_eqP => x.
  rewrite filterE /=.
  case (m.[x] = None) => mx; first by rewrite mx //.
  by have [y ->]: exists y, m.[x] = Some y by exists (oget m.[x]); rewrite -Core.some_oget //.
qed.

lemma empty_card_fdom_filter ['a 'b] (m: ('a, 'b) fmap):
  m = empty<:'a, 'b> <=> forall f, card (fdom (filter f m)) = 0.
proof.
  split.
  + move => pre f.
    rewrite pre cardE size_eq0.
    move : (filter_notnil m f) => hyp.
    apply contra in hyp.
    rewrite /= pre /= in hyp.
    rewrite hyp -elems_fset0 fdom0 //.
  + apply absurd => pre.
    rewrite negb_forall  /=.
    exists (fun _ _ => true).
    rewrite no_filter.
    move : pre.
    apply absurd => /=.
    rewrite cardE size_eq0.
    move => pre.
    move : (elems_eq_fset0 (fdom m)) => nodom.
    rewrite pre /= in nodom.
    move : pre.
    rewrite nodom elems_fset0 /= fdom_eq0 //.
qed.

lemma coll_card (m: ('a, 'b) fmap):
  !fmap_collision m <=> forall b, card (fdom (filter (fun _ y => y = b) m)) <= 1.
proof.
  split.
  + (* => *)
    move => pre b.
    pose f  := (fun (_ : 'a) (y : 'b) => y = b);
      pose fm := filter f m;
      pose A  := (fdom fm).
    have ->: card A <= 1 <=> card A = 0 \/ card A = 1 by rewrite cardE size_eq0 size_eq1 size_le1 //.
    case (card A = 0) => c0 //=.
    move : pre.
    apply absurd => /=.
    have ->: card A <> 1 <=> 1 < card A.
      move : c0.
      rewrite -lez_add1r cardE neq_ltz /=.
      have ->: !size (elems A) < 0 by move : (size_ge0 (elems A)); rewrite lezNgt //.
      rewrite /= neq_ltz.
      move => sgt0.
      have ->: !size (elems A) < 1 by move : sgt0; rewrite -lez_add1r -lezNgt //.
      rewrite /= -lez_add1r //= cardE -lez_add1r /=.
    move => pre.
    have [e1 e2 l exploded]: exists e1 e2 s, e1 :: e2 :: s = elems A.
      move : pre; rewrite cardE.
      elim (elems A) => //= x l ibase.
      move => hyp.
      exists x => /=.
      exists (head witness l) (behead l).
      rewrite head_behead // -size_eq0 //.
      move : hyp.
      rewrite -lez_add1r lez_add2l.
      apply absurd => /=.
      move => s0.
      rewrite s0 //.
    rewrite /fmap_collision.
    exists e1 e2.
    have Ae1: mem A e1 by rewrite memE -exploded //.
    move : Ae1; rewrite mem_fdom dom_filter; move => [me1 f1].
    have Ae2: mem A e2 by rewrite memE -exploded //.
    move : Ae2; rewrite mem_fdom dom_filter; move => [me2 f2].
    have e1_neq_e2: e1 <> e2 by move : (uniq_elems A); rewrite -exploded /= negb_or //.
    rewrite me1 e1_neq_e2 /=.
    have me1V: m.[e1] = Some b by rewrite /f in f1; rewrite -f1 // -Core.some_oget //.
    have me2V: m.[e2] = Some b by rewrite /f in f2; rewrite -f2 // -Core.some_oget //.
    rewrite me1V me2V //.
  + (* <= *)
    apply absurd => /=.
    rewrite /fmap_collision.
    move => [x y [mx [xy x_mapeq_y]]].
    rewrite negb_forall /=.
    exists (oget m.[x]).
    rewrite -ltzNge.
    have my: dom m y by apply (coll_dom m x).
    pose b  := oget m.[x];
      pose f  := (fun (_ : 'a) (y : 'b) => y = b);
      pose fm := filter f m;
      pose A  := (fdom fm).
    have Ax: mem A x by rewrite mem_fdom dom_filter //.
    have Ay: mem A y by rewrite mem_fdom dom_filter my -x_mapeq_y //=.
    rewrite cardE.
    rewrite memE in Ax.
    rewrite memE in Ay.
    have size_rem_alt: forall (x : 'a) (s : 'a list), x \in s => size s = 1 + size (rem x s) by move => *; rewrite size_rem // addzA addzC addzA addNz add0z //.
    have ADx_y: mem (rem x (elems A)) y by rewrite mem_mem_rem //.
    rewrite (size_rem_alt x) // (size_rem_alt y) // -lez_add1r -addz0 2!lez_add2l.
    apply size_ge0.
qed.