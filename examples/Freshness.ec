(* --------------------------------------------------------------------
 * Copyright (c) - 2018 - Roberto Metere <r.metere2@ncl.ac.uk>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Int.
require import Leakable.
require import Real.
require import Distr.
require import SmtMap.
require import FSet.

type X.
type Y.

op dv : { Y distr | is_lossless dv } as dv_ll.

(*
 * This is an example of algorithm module type, where
 * - init: may do nothing
 * - f: acts as a random function
 * - prepare_f: prepares values for f, but does not disclose them
 *)
module type RF = {
  proc init(): unit
  proc f(x: X): Y
  proc prepare_f(x: X): unit
}.

(*
 * This module type exposes the two precedures f and prepare_f,
 * but hides the init procedure.
 *)
module type RFAccess = {
  proc f(x: X): Y
  proc prepare_f(x: X): unit
}.

(*
 * A distinguished is allowed to perform oracle calls to what RFAccess exposes.
 * Plus, it is supposed to have an abstract procedure distinguish().
 *)
module type Dist(A: RFAccess) = {
  proc distinguish(): bool
}.

(*
 * The module M is a regular map that behaves as a lazy map
 * in the meaning that the values are fd when either needed
 * (procedure f) or simply requested (procedure prepare_f).
 *
 * prepare_f is actually not as lazy as it can be.
 *)
module M: RF = {
  var m: (X, Y) fmap

  proc init() = {
    m <- empty;
  }

  proc f(x: X): Y = {
    var ret;

    if (!(dom m x)) {
      m.[x] <$ dv;
    }

    ret <- oget m.[x];

    return ret;
  }

  proc prepare_f(x: X) = {
    if (!(dom m x)) {
      m.[x] <$ dv;
    }
  }
}.

(*
 * HalfLazy here behaves exactly as M: it does not fill the map in advance,
 * but act lazy for f, and not that lazy for prepare_f.
 *)
module HalfLazyM: RF = {
  var m: (X, Y leakable) fmap

  proc init() = {
    m <- empty;
  }

  proc f(x: X) = {
    var ret: Y;

    if (!(dom m x)) {
      m.[x] </$ dv; (* EXPERIMENTAL SYNTAX *)
    }

    ret </ oget m.[x]; (* EXPERIMENTAL SYNTAX *)

    return ret;
  }

  proc prepare_f(x: X) = {
    if (!(dom m x)) {
      m.[x] </$ dv; (* EXPERIMENTAL SYNTAX *)
    }
  }
}.

(*
 * Lazy here refers to the procedure prepare_f which does nothing,
 * de facto procastinating the real sampling to when the
 * procedure f is called on the same value.
 * We call it lazy because its behaviour is lazier than the
 * HalfLazy procedure.
 *
 * The only difference would be that when we call prepare_f, the map m
 * is not filled in; therefore, having access to the inner memory of both
 * LazyM and HalfLazyM, one could tell the difference of behaviour.
 * Nevertheless, the distinguisher is not allowed to access them, but is
 * restricted to merely call either f or prepare_f.
 *)
module LazyM: RF = {
  var m: (X, Y leakable) fmap

  proc init() = {
    m <- empty;
  }

  proc f(x: X) = {
    var ret;

    if (!(dom m x)) {
      m.[x] </$ dv; (* EXPERIMENTAL SYNTAX *)
    } 

    ret </ oget m.[x]; (* EXPERIMENTAL SYNTAX *)

    return ret;
  }

  proc prepare_f(x: X) = {
  }
}.

(*
 * We prove that the behaviour of the module M (the regular EasyCrypt
 * lazy module) equals the behaviour of the module HalfLazyM, which contains
 * the experimental syntax and leakable type in the map.
 * They do pretty much the same work and the additional information of the
 * leakable type is actually neglected, so the idea behind this equality is
 * trivial to understand.
 *
 * Notably, the proof only requires the usage of the additional
 * experimental tactics "declassify" and "secsample", the rest of the proof
 * is exactly the same as it would have been without and with two
 * different types of sampling from bijective distibutions.
 *)
lemma nosmt example_leakable_equivalence (D<: Dist{M,HalfLazyM}) &m:
  (M.m = empty){m} =>
  (HalfLazyM.m = empty){m} =>
  Pr[D(M).distinguish() @ &m : res] = Pr[D(HalfLazyM).distinguish() @ &m : res].
proof.
  move => *.
  byequiv (_: ={glob D}
        /\ (forall x, dom M.m{1} x <=> dom HalfLazyM.m{2} x)
        /\ (forall x, dom M.m{1} x => oget M.m.[x]{1} = vget HalfLazyM.m.[x]{2})
        ==> _) => //.
  proc*.
  call (_: (forall x, dom M.m{1} x <=> dom HalfLazyM.m{2} x)
        /\ (forall x, dom M.m{1} x => oget M.m.[x]{1} = vget HalfLazyM.m.[x]{2})
       ) => //.
  (* call to f *)
  proc*; inline*.
  sp 1 1; wp => /=.
  (* EXPERIMENTAL TACTIC *) declassify{2}.
  wp 1 2.
  wp 1 1 => /=.
  if => //.
  + (* condition *)
    move => &1 &2 [_ [_ [_ [dom_eq same_value]]]]; subst.
    rewrite -iff_negb /= dom_eq //.
  + (* then *)
    wp => /=.
    (* EXPERIMENTAL TACTIC *) secsample{2}.
    wp; rnd; wp; skip; progress.
    - rewrite 3!get_set_sameE Core.oget_some //=.
    - case (x1 = x{2}) => x1x /=.
      * rewrite x1x mem_set //.
      * move : H6; rewrite get_set_sameE Core.oget_some 2!set_setE mem_set x1x /= mem_set x1x /= (H1 x1) //.
    - case (x1 = x{2}) => x1x /=.
      * rewrite x1x mem_set //.
      * move : H6; rewrite get_set_sameE Core.oget_some 2!set_setE mem_set x1x /= mem_set x1x /= (H1 x1) //.
    - rewrite get_set_sameE Core.oget_some //=.
      case (x1 = x{2}) => x1x /=.
      * rewrite x1x 2!get_set_sameE Core.oget_some //.
      * move : H6; rewrite mem_set x1x /= => H6; rewrite get_set_neqE // get_set_neqE // get_set_neqE // (H2 x1) //.
  + (* else *)
    skip; progress.
    - rewrite get_set_sameE Core.oget_some (H2 _ H3) //.
    - case (x1 = x{2}) => x1x /=.
      * rewrite x1x mem_set //.
      * move : H4; rewrite mem_set x1x /= (H1 x1) //.
    - move : H4.
      case (x1 = x{2}) => x1x /=.
      * rewrite x1x mem_set //.
      * rewrite mem_set x1x /= (H1 x1) //.
    - case (x1 = x{2}) => x1x /=.
      * rewrite x1x (H2 _ H3) /vget /inst get_set_sameE Core.oget_some //.
      * rewrite get_set_neqE // (H2 _ H4) //.
  (* call to prepare_f *)
  proc*; inline*.
  sp; if => //=.
  + (* condition *)
    move => &1 &2 [_ [_ [_ [dom_eq same_value]]]]; subst.
    rewrite -iff_negb /= dom_eq //.
  + (* then *)
    wp => /=.
    (* EXPERIMENTAL TACTIC *) secsample{2}.
    wp; rnd; wp; skip; progress.
    - case (x1 = x{2}) => x1x /=.
      * rewrite x1x mem_set //.
      * move : H6; rewrite 2!mem_set x1x /= (H1 x1) //.
    - case (x1 = x{2}) => x1x /=.
      * rewrite x1x mem_set //.
      * move : H6; rewrite 2!mem_set x1x /= (H1 x1) //.
    - case (x1 = x{2}) => x1x /=.
      * rewrite x1x 2!get_set_sameE Core.oget_some //.
      * move : H6; rewrite mem_set x1x /= => H6; rewrite get_set_neqE // get_set_neqE // (H2 x1) //.
  (* preconditions must be true with empty too *)
  progress; first 3 by move : H1; rewrite H H0 domE emptyE //=.
  qed.

(*
 * Here we demonstrate the usage of the leakable type to follow the information flow,
 * as we often do in on-paper proofs, to establish the statistical equality of
 * freshly f values and unrevealed values that have been prepared in the past.
 *
 * Before the experimental syntax and tactics introduced to work with leakable types,
 * we needed to create additional redundant modules with additional procedures for
 * re-sampling the values.
 *
 * With this approach, we sacrifice slightly more complex proofs, to enjoy a much clearer
 * and intuitive module construction.
 *
 * Noticeably, the proof has been carried on with excruciating details, many of which
 * can be actually discharged automatically by SMT solvers.
 *)
lemma nosmt example_leakable (D<: Dist{HalfLazyM,LazyM}) &m:
  distr_proper dv =>
  (LazyM.m = empty){m} =>
  (HalfLazyM.m = empty){m} =>
  Pr[D(LazyM).distinguish() @ &m : res] = Pr[D(HalfLazyM).distinguish() @ &m : res].
proof.
  move => dv_proper lm0 em0.
  byequiv (_: ={glob D}
        /\ undeclassify_invariant_fmap LazyM.m{1} HalfLazyM.m{2} dv
        ==> _) => //.
  proc*.
  call (_: undeclassify_invariant_fmap LazyM.m{1} HalfLazyM.m{2} dv
       ) => //.
  (* call to f *)
  proc*; inline*.
  sp 1 1; wp => /=.
  case (dom LazyM.m{1} x{2}) => //=.
  * rcondf{1} 1; progress.
    rcondf{2} 1; progress.
      skip; move => &m' [[_] [_] [_]]; subst; rewrite /invariant; move => [m_dv] [mem_l_m] [mem_l mem_m] pre.
      move : (mem_l_m _ pre) => //.
    (* EXPERIMENTAL TACTIC *) declassify{1}.
    (* EXPERIMENTAL TACTIC *) declassify{2}.
    wp; skip; rewrite /undeclassify_invariant_fmap /(===) /ovd_eq /=.
    move => &1 &2 [[_] [_] [_]]; subst; rewrite /invariant; move => [m_dv] [mem_l_m] [mem_l mem_m] pre /=.
    progress.
    - rewrite 2!get_set_sameE 2!Core.oget_some /=.
      move : (mem_l_m _ pre) => //.
    - case (x1 = x{2}) => /= x1x.
      * rewrite x1x get_set_sameE Core.oget_some //=.
        move : (mem_l_m _ pre) => [pre_m] _.
        move : (m_dv _ pre_m) => //.
      * rewrite get_set_neqE //.
        move : H; rewrite mem_set x1x /= => pre_m.
        move : (m_dv _ pre_m) => //.
    - case (x1 = x{2}) => /= x1x.
      * rewrite mem_set x1x //=.
      * move : H; rewrite 2!mem_set x1x /= => pre_x1.
        move : (mem_l_m _ pre_x1) => //.
    - case (x1 = x{2}) => /= x1x.
      * rewrite x1x /vget /inst 2!get_set_sameE 2!Core.oget_some //=.
        move : (mem_l_m _ pre) => //.
      * move : H; rewrite mem_set x1x get_set_neqE // get_set_neqE //= => pre_x1.
        move : (mem_l_m _ pre_x1) => //.
    - case (x1 = x{2}) => /= x1x.
      * rewrite x1x 2!get_set_sameE //=.
        move : (mem_l_m _ pre) => [_]; rewrite /vget /inst //.
      * move : H; rewrite mem_set x1x /= => pre_x1.
        rewrite get_set_neqE // get_set_neqE //.
        move : (mem_l_m _ pre_x1) => //.
    - case (x1 = x{2}) => /= x1x.
      * rewrite x1x 2!get_set_sameE //=.
        move : (mem_l_m _ pre) => [_]; rewrite /vget /inst //.
      * move : H; rewrite mem_set x1x /= => pre_x1.
        rewrite get_set_neqE // get_set_neqE //.
        apply (mem_l _ pre_x1) => //.
        move : H0; rewrite get_set_neqE //.
    - case (x1 = x{2}) => /= x1x.
      * move : H; rewrite mem_set x1x get_set_sameE Core.oget_some //.
      * move : H H0; rewrite 2!mem_set x1x get_set_neqE //=; exact (mem_m _).
  * rcondt{1} 1; progress.
    case (dom HalfLazyM.m{2} x{2}) => //=; last first.
    + rcondt{2} 1; progress.
      (* EXPERIMENTAL TACTIC *) declassify{1}.
      (* EXPERIMENTAL TACTIC *) declassify{2}.
      wp => /=.
      (* EXPERIMENTAL TACTIC *) secsample{1}.
      (* EXPERIMENTAL TACTIC *) secsample{2}.
      wp => /=; rnd; skip; rewrite /undeclassify_invariant_fmap /(===) /ovd_eq /=.
      move => &1 &2 [[[_] [_] [_]]]; subst; rewrite /invariant; move => [m_dv] [mem_l_m] [mem_l mem_m] pre_l pre_e /=.
      progress.
      - rewrite 4!get_set_sameE 2!Core.oget_some //.
      - move : H1; rewrite get_set_sameE Core.oget_some /= set_setE /=.
        case (x1 = x{2}) => /= x1x.
        * rewrite x1x get_set_sameE Core.oget_some //=.
        * rewrite get_set_neqE // mem_set x1x /= => pre_m.
          move : (m_dv _ pre_m) => //.
      - move : H1; rewrite 2!get_set_sameE Core.oget_some /= set_setE /= set_setE /=.
        case (x1 = x{2}) => /= x1x.
        * rewrite 2!mem_set x1x //=.
        * rewrite 2!mem_set x1x /= => pre_m.
          move : (mem_l_m _ pre_m) => //.
      - move : H1; rewrite 2!get_set_sameE Core.oget_some /= set_setE /= set_setE /=.
        case (x1 = x{2}) => /= x1x.
        * rewrite mem_set x1x 2!get_set_sameE Core.oget_some //=.
        * rewrite get_set_neqE // get_set_neqE // mem_set x1x /= => pre_m.
          move : (mem_l_m _ pre_m) => //.
      - move : H1 H2; rewrite 2!get_set_sameE Core.oget_some /= set_setE /= set_setE /=.
        case (x1 = x{2}) => /= x1x.
        * rewrite mem_set x1x 2!get_set_sameE Core.oget_some //=.
        * rewrite get_set_neqE // get_set_neqE // mem_set x1x /= => pre_m.
          move : (mem_l_m _ pre_m) => //.
      - move : H1 H2; rewrite 2!get_set_sameE Core.oget_some /= set_setE /= set_setE /=.
        case (x1 = x{2}) => /= x1x.
        * rewrite mem_set x1x 2!get_set_sameE Core.oget_some //=.
        * rewrite get_set_neqE // get_set_neqE // mem_set x1x /= => pre_m.
          move : (mem_l _ pre_m) => //.
      - move : H1 H2; rewrite 2!get_set_sameE Core.oget_some /= set_setE /= set_setE /=.
        case (x1 = x{2}) => /= x1x.
        * rewrite 2!mem_set x1x get_set_sameE Core.oget_some //=.
        * rewrite get_set_neqE // 2!mem_set x1x /= => pre_Nm pre_m.
          move : (mem_m _ pre_Nm pre_m) => //.
    + rcondf{2} 1; progress.
      (* EXPERIMENTAL TACTIC *) undeclassify.
      wp => /=; skip; rewrite /undeclassify_invariant_fmap /(===) /ovd_eq /=.
      move => &1 &2 [[[[_] [_] [_]]]]; subst; move => [m_dv] [mem_l_m] [mem_l mem_m] pre_l pre_e _ /=; subst.
      progress.
      - case (x1 = x{2}) => //= x1x.
        move : H; rewrite mem_set x1x /= => pre_m.
        move : (mem_l_m _ pre_m) => //.
      - case (x1 = x{2}) => //= x1x.
        * rewrite x1x get_set_sameE //.
        * move : H; rewrite mem_set x1x get_set_neqE ///= => pre_m.
          move : (mem_l_m _ pre_m) => //.
      - case (x1 = x{2}) => //= x1x.
        * rewrite x1x get_set_sameE //.
        * move : H; rewrite mem_set x1x get_set_neqE ///= => pre_m.
          move : (mem_l_m _ pre_m) => //.
      - case (x1 = x{2}) => //= x1x.
        * rewrite x1x get_set_sameE //= -Core.some_oget.
            rewrite -domE //.
          trivial.
        * move : H; rewrite get_set_neqE // mem_set x1x /= => pre_m.
          move : (mem_l _ pre_m _) => //.
      - case (x1 = x{2}) => /= x1x.
        * move : H; rewrite mem_set x1x //=.
        * move : H; rewrite mem_set x1x /= => pre_Nm.
          move : (mem_m _ pre_Nm _) => //.
      - rewrite get_set_sameE Core.oget_some /=.
        move : (m_dv _ pre_e) => //.
      - rewrite get_set_sameE Core.oget_some /=.
        move : (mem_m _ pre_l _) => //.
      - rewrite get_set_sameE Core.oget_some //=.
      - case (x1 = x{2}) => //= x1x.
        move : H; rewrite mem_set x1x /= => pre_m.
        move : (mem_l_m _ pre_m) => //.
      - case (x1 = x{2}) => //= x1x.
        * rewrite x1x get_set_sameE //.
        * move : H; rewrite mem_set x1x get_set_neqE ///= => pre_m.
          move : (mem_l_m _ pre_m) => //.
      - case (x1 = x{2}) => //= x1x.
        * rewrite x1x get_set_sameE //.
        * move : H; rewrite mem_set x1x get_set_neqE ///= => pre_m.
          move : (mem_l_m _ pre_m) => //.
      - case (x1 = x{2}) => //= x1x.
        * rewrite x1x get_set_sameE //= -Core.some_oget.
            rewrite -domE //.
          trivial.
        * move : H; rewrite get_set_neqE // mem_set x1x /= => pre_m.
          move : (mem_l _ pre_m _) => //.
      - case (x1 = x{2}) => /= x1x.
        * move : H; rewrite mem_set x1x //=.
        * move : H; rewrite mem_set x1x /= => pre_Nm.
          move : (mem_m _ pre_Nm _) => //.
  (* call to prepare_f *)
  proc*; inline*.
  sp; if{2} => //=.
  + (* then *)
    (* EXPERIMENTAL TACTIC *) secsample{2}.
    wp => /=; rnd{2}; skip; rewrite /undeclassify_invariant_fmap /(===) /ovd_eq /=.
    move => &1 &2 [[_] [_] [_]]; subst; rewrite /invariant; move => [m_dv] [mem_l_m] [mem_l mem_m] pre_e /=.
    progress.
    - exact dv_ll.
    - case (x1 = x{2}) => /= x1x.
      * rewrite x1x get_set_sameE Core.oget_some //=.
      * move : H1; rewrite get_set_neqE // mem_set x1x /= => pre_m.
        move : (m_dv _ pre_m) => //.
    - move : (mem_l_m x1 H1) => [concl] _.
      rewrite mem_set concl //.
    - move : (mem_l_m x1 H1) => [_] [concl] _.
      have x1x: x1 <> x{2} by move : pre_e; apply absurd => /= ah; rewrite -ah //.
      rewrite get_set_neqE //; exact concl.
    - move : (mem_l_m x1 H1) => [_] [_] concl.
      have x1x: x1 <> x{2} by move : pre_e; apply absurd => /= ah; rewrite -ah //.
      rewrite get_set_neqE //; exact concl.
    - move : (mem_l_m x1 H1) => [_] _.
      have x1x: x1 <> x{2} by move : pre_e; apply absurd => /= ah; rewrite -ah //.
      move : H2; rewrite get_set_neqE // => pre.
      move : (mem_l x1 _ pre) => //.
    - case (x1 = x{2}) => /= x1x.
      * rewrite x1x get_set_sameE Core.oget_some //=.
      * move : H2; rewrite get_set_neqE // mem_set x1x /= => pre_m.
        move : (mem_m _ _ pre_m) => //.
  (* preconditions must be true with empty too *)
  progress.
  - move : H; rewrite em0 domE emptyE //=.
  - move : H; rewrite lm0 domE emptyE //=.
  - move : H; rewrite lm0 domE emptyE //=.
  - move : H; rewrite lm0 domE emptyE //=.
  - move : H; rewrite lm0 domE emptyE //=.
  - move : H; rewrite em0 domE emptyE //=.
  - move : H0; rewrite em0 domE emptyE //=.
  qed.

