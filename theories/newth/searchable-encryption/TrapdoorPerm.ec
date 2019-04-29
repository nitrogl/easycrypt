(* --------------------------------------------------------------------
 * Copyright (c) - 2016--2017 Roberto Metere (r.metere2@ncl.ac.uk)
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(*
 * Trapdoor one-way permutations with (enhanced) hard-core predicate.
 * 
 * I(1^n) -> (\alpha, \tau) -- \tau is the trapdoor
 * I(1^n, r) -> (\alpha, \tau) -- deterministic, knowing the random tape r
 * S(\alpha) -> x
 * S(\alpha, r) -> x -- deterministic, knowing the random tape r
 * F(\alpha, x) -> f_{\alpha} (x)
 * B(\tau, y) -> f_{\alpha}^{-1} (y)
 *
 * The hard core predicate:
 * hc(\alpha, x) -> bool
 *)
require import Distr.
require import DBool.
require import Real.
require import Int.
require import List.
require (*--*) FinType.
require import TacticsExt.
require import ListExt.
require import IntExt.
require (*--*) Permutation.

theory TrapdoorPermutation.
  type D.
  clone import Permutation as TrapdoorDomain with
    type D <- D
  .

  type alpha.
  type tau.
  type coin.
  type rtape. (* multiset/list/map of coins, i.e. elements extracted from dcoins *)
  type keypair = alpha * tau.

  (* Generic random tape operations *)
  op singleton_rtape: coin -> rtape. (* random tape with single coin *)
  op consume: rtape -> rtape. (* remove the first element of the random tape *)
  op bitemap ['a]: (coin -> 'a) -> rtape -> 'a. (* read the first element from the random tape and apply a function on it *)
  op bite: rtape -> coin = bitemap idfun.
  op extract: rtape -> int -> coin.
  op compose: rtape -> rtape -> rtape.

  pred rtape_nonempty (r: rtape) = exists c, singleton_rtape (bite r) = singleton_rtape c.
  pred bite_dependent (f: rtape -> 'a) =
    forall r1 r2, (f r1 = f r2) = (bite r1 = bite r2).
  pred bite_cancel (f: rtape -> 'a) (g: 'a -> rtape) = forall r, g (f r) = singleton_rtape (bite r).
  pred extract1_is_bite = forall r, bite r = extract r 1.

  (* For  *)
  pred (-<) (f: 'a -> 'b) (g: 'b -> 'a) = cancel f g.
  pred (>-) (f: 'a -> 'b) (g: 'b -> 'a) = cancel g f.
  pred (><) (f: 'a -> 'b) (g: 'b -> 'a) = f -< g /\ f >- g.

  (* Trapdoor generic functions *)
  op owf: tau -> alpha. (* compute the "public" alpha from the trapdoor *)
  op forward: alpha -> D -> D. (* the permutation *)
  op backward: tau -> D -> D. (* its supposed inverse *)

  (* Generic indexing/sampling operations *)
  op index_f: coin -> tau.
  op rindex_f: tau -> coin.
  op sample: alpha -> rtape -> D.
  op rdsample: alpha -> D -> rtape.

  (* Indexing *)
  op index (r: rtape) = let t = bitemap index_f r in (owf t, t).
  op rindex (k: keypair) = (singleton_rtape \o rindex_f \o snd) k.
  pred validkeypair (k: keypair) = (fst k) = owf (snd k).

  (* Distributions *)
  op dcoins: coin distr. (* n-bit long inputs, n is determined by the cardinality of coins *)
  op dD: alpha -> D distr. (* indexed distribution over D this has to be uniform *)

  (* Collection of trapdoor functions from D to D, and permutations, predicates *)
  pred ct (i: rtape -> keypair) (s: alpha -> rtape -> D) (f: alpha -> D -> D) (b: tau -> D -> D) =
    forall k, (forall r, k = index r => validkeypair k) /\ (validkeypair k => (f (fst k)) -< (b (snd k))).

  pred enhanced_ct (s: alpha -> rtape -> D) (s_inv: alpha -> D -> rtape) =
    forall a,
      (forall x, rtape_nonempty (s_inv a x)) /\
      bite_cancel (s a) (s_inv a) /\ (s_inv a) -< (s a).

  lemma ect_sample_bite s s_inv:
    enhanced_ct s s_inv =>
    forall a (r: rtape), s a (singleton_rtape (bite r)) = s a r.
  proof.
    move => *; smt.
  qed.

  (* Hard-core predicate *)
  op hc: alpha -> D -> bool.
  
  (* Collection of Trapdoor Permutations given a random tape *)
  module type CollectionTP = {
    proc index(): keypair
    proc sample(a: alpha): D
    proc forward(a: alpha, x: D): D
    proc backward(t: tau, y: D): D
    proc validk(k: keypair): bool
    proc validx(k: keypair, x: D): bool

    (* Deterministic versions of index and sample *)
    proc indexR(r: rtape): keypair
    proc sampleR(a: alpha, r: rtape): D
  }.

  module Correctness(C: CollectionTP) = {
    proc main() : bool = {
      var a, t, x, x', y, vx, r;

      (a, t) <@ C.index();
      x  <@ C.sample(a);
      vx <@ C.validx((a, t), x);
      if (vx) {
        y  <@ C.forward(a, x);
        x' <@ C.backward(t, y);
        r = x = x';
      } else {
        r = false;
      }

      return r;
    }
  }.

  module type ReverseDomain = {
    proc rdsample(a: alpha, y: D): rtape
  }.

  (* The attacker is an inverter *)
  module type Inverter = {
    proc invert(a: alpha, y: D): D
  }.
  
  module TPExperiment(C: CollectionTP, I: Inverter) = {
    proc game(real: bool) : bool = {
      var a, t, x, x', y;

      (a, t) = C.index();
      y = C.sample(a);
      x = C.backward(t, y);
      if (real) x' = I.invert(a, y);
      else      x' = C.sample(a);

      return (x = x');
    }
  
    proc main(): bool = {
      var b, b';
      
      b  <$ {0,1};
      b' <@ game(b);

      return b = b';
    }
  }.

  (* Enhanced inverter and games *)
  module type EnhancedInverter = {
    proc invert(a: alpha, r: rtape): D
  }.
  
  module ETPExperiment(C: CollectionTP, I: EnhancedInverter) = {
    proc game(real: bool, r: rtape) : bool = {
      var a, t, x, x', y;

      (a, t) = C.index();
      y = C.sampleR(a, r);
      x = C.backward(t, y);
      if (real) x' = I.invert(a, r);
      else      x' = C.sample(a);

      return (x = x');
    }
  
    proc main(r: rtape): bool = {
      var b, b';
      
      b  <$ {0,1};
      b' <@ game(b, r);

      return b = b';
    }
  }.

  (*
   * Attacking the hard-core predicate. Pr[A(alpha, y) = hc(alpha, f_inv(tau, y))] is negligible
   *)
  module type HCInverter = {
    proc invert(a: alpha, y: D): bool
  }.
  
  module HCExperiment(C: CollectionTP, I: HCInverter) = {
    proc game(real: bool) : bool = {
      var a, t, h, h', x, y;
      
      (a, t) = C.index();
      y = C.sample(a);
      x = C.backward(t, y);
      h = hc a x;
      if (real) h' = I.invert(a, y);
      else      h' <$ {0,1};

      return (h = h');
    }
  
    proc main(): bool = {
      var b, b';
      
      b  <$ {0,1};
      b' <@ game(b);

      return b = b';
    }
  }.

  (*
   * Attacking the hard-core predicate. Pr[A(alpha, r) = hc(alpha, f_inv(tau, y))] is negligible
   *)
  module type EnhancedHCInverter = {
    proc invert(a: alpha, c: coin): bool
  }.
  
  module EHCExperiment(C: CollectionTP, I: EnhancedHCInverter) = {
    proc game(real: bool, c: coin) : bool = {
      var a, t, h, h', x, y;
      
      (a, t) = C.index();
      y = C.sampleR(a, singleton_rtape c);
      x = C.backward(t, y);
      h = hc a x;
      if (real) h' = I.invert(a, c);
      else      h' <$ {0,1};

      return (h = h');
    }
  
    proc main(c: coin): bool = {
      var b, b';
      
      b  <$ {0,1};
      b' <@ game(b, c);

      return b = b';
    }
  }.

  (*
   * ===========================================
   *    Security of the trapdoor permutation.
   * ===========================================
   *)
  lemma tp_game_ll (C<: CollectionTP) (I<: Inverter):
    islossless I.invert =>
    islossless C.index =>
    islossless C.sample =>
    islossless C.backward =>
    islossless TPExperiment(C, I).game.
  proof.
    move => invert_ll index_ll sample_ll backward_ll.
    proc => //.
    case (real).
      (* real *)
      rcondt 4.
        kill 3. call backward_ll; trivial.
        kill 2. call sample_ll; trivial.
        kill 1. call index_ll; trivial.
      trivial.
    call invert_ll; call backward_ll; call sample_ll; call index_ll.
    skip; trivial.
      (* !real *)
      rcondf 4.
        kill 3. call backward_ll; trivial.
        kill 2. call sample_ll; trivial.
        kill 1. call index_ll; trivial.
      trivial.
    call sample_ll; call backward_ll; call sample_ll; call index_ll.
    skip; trivial.
  qed.

  lemma tp_game_main_ll (C<: CollectionTP) (I<: Inverter):
    islossless I.invert =>
    islossless C.index =>
    islossless C.sample =>
    islossless C.backward =>
    islossless TPExperiment(C, I).main.
  proof.
    move => invert_ll index_ll sample_ll backward_ll.
    have game_ll: islossless TPExperiment(C, I).game by apply (tp_game_ll C I).
    proc; call game_ll; rnd; skip; progress; apply (dboolE predT).
  qed.

  (*
   * Total probability
   * Pr[Main] = 1/2 Pr[Real] + 1/2 Pr[Ideal]
   *)
  lemma tp_total_probability (C<: CollectionTP{TPExperiment}) (I<: Inverter{TPExperiment, C}) &m:
    Pr[TPExperiment(C, I).main() @ &m : res] = 1%r/2%r * (Pr[TPExperiment(C, I).game(true) @ &m : res] + Pr[TPExperiment(C, I).game(false) @ &m : !res]).
  proof.
    pose prReal := Pr[TPExperiment(C, I).game(true) @ &m : res].
    pose prIdeal := Pr[TPExperiment(C, I).game(false) @ &m : !res].
    byphoare (_: (glob TPExperiment(C, I)) = (glob TPExperiment(C, I)){m} ==> _) => //; proc => //.
    seq 1: (b) (1%r/2%r) prReal (1%r/2%r) prIdeal ((glob TPExperiment(C, I)) = (glob TPExperiment(C, I)){m}).
      rnd; wp; skip; smt.
      (* post = b *)
      rnd; wp; skip; smt.
      rewrite /prReal.
        (* b *)
        call (_: (glob TPExperiment(C, I)) = (glob TPExperiment(C, I)){m} /\ real ==> res) => //; last by skip; progress; smt.
        bypr; progress; byequiv => //; sim; progress; smt.
      (* post = !b *)
      rnd; wp; skip; smt.
      rewrite /prIdeal.
        (* !b *)
        call (_: (glob TPExperiment(C, I)) = (glob TPExperiment(C, I)){m} /\ !real ==> !res) => //; last by skip; progress; smt.
        bypr; progress; byequiv => //; sim; progress; smt.
    progress; smt.
  qed.

  (*
   *  Advantage: |2*Pr[Main] - 1| = Pr[Real] - Pr[Ideal]
   *)
  lemma tp_advantage (C<: CollectionTP{TPExperiment}) (I<: Inverter{TPExperiment, C}) &m:
    islossless I.invert =>
    islossless C.index =>
    islossless C.sample =>
    islossless C.backward =>
    2%r * Pr[TPExperiment(C, I).main() @ &m : res] - 1%r =
    Pr[TPExperiment(C, I).game(true) @ &m : res] - Pr[TPExperiment(C, I).game(false) @ &m : res].
  proof.
    move => invert_ll index_ll sample_ll backward_ll.
    pose prReal := Pr[TPExperiment(C, I).game(true) @ &m : res].
    have ->: Pr[TPExperiment(C, I).game(false) @ &m : res] = 1%r - Pr[TPExperiment(C, I).game(false) @ &m : !res].
      rewrite Pr [mu_not].
      have ->: Pr[TPExperiment(C, I).game(false) @ &m : true] = 1%r.
        byphoare => //; apply (tp_game_ll C I) => //.
      smt.
    pose prIdeal := Pr[TPExperiment(C, I).game(false) @ &m : !res].
    have ->: (2%r * Pr[TPExperiment(C, I).main() @ &m : res] - 1%r = prReal - (1%r - prIdeal)) = (Pr[TPExperiment(C, I).main() @ &m : res] = 1%r/2%r * (prReal + prIdeal)) by smt.
    apply (tp_total_probability C I &m).
  qed.

  (*
   * ====================================================
   *    Security of the ENHANCED trapdoor permutation.
   * ====================================================
   *)
  lemma etp_game_ll (C<: CollectionTP) (I<: EnhancedInverter):
    islossless I.invert =>
    islossless C.index =>
    islossless C.sample =>
    islossless C.sampleR =>
    islossless C.backward =>
    islossless ETPExperiment(C, I).game.
  proof.
    move => invert_ll index_ll sample_ll sampleR_ll backward_ll.
    proc => //.
    case (real).
      (* real *)
      rcondt 4.
        kill 3. call backward_ll; trivial.
        kill 2. call sampleR_ll; trivial.
        kill 1. call index_ll; trivial.
      trivial.
    call invert_ll; call backward_ll; call sampleR_ll; call index_ll.
    skip; trivial.
      (* !real *)
      rcondf 4.
        kill 3. call backward_ll; trivial.
        kill 2. call sampleR_ll; trivial.
        kill 1. call index_ll; trivial.
      trivial.
    call sample_ll; call backward_ll; call sampleR_ll; call index_ll.
    skip; trivial.
  qed.

  lemma etp_game_main_ll (C<: CollectionTP) (I<: EnhancedInverter):
    islossless I.invert =>
    islossless C.index =>
    islossless C.sample =>
    islossless C.sampleR =>
    islossless C.backward =>
    islossless ETPExperiment(C, I).main.
  proof.
    move => invert_ll index_ll sample_ll sampleR_ll backward_ll.
    have game_ll: islossless ETPExperiment(C, I).game by apply (etp_game_ll C I).
    proc; call game_ll; rnd; skip; progress; apply (dboolE predT).
  qed.

  (*
   * Total probability
   * Pr[Main] = 1/2 Pr[Real] + 1/2 Pr[Ideal]
   *)
  lemma etp_total_probability (C<: CollectionTP{ETPExperiment}) (I<: EnhancedInverter{ETPExperiment, C}) rt &m:
    Pr[ETPExperiment(C, I).main(rt) @ &m : res] = 1%r/2%r * (Pr[ETPExperiment(C, I).game(true, rt) @ &m : res] + Pr[ETPExperiment(C, I).game(false, rt) @ &m : !res]).
  proof.
    pose prReal := Pr[ETPExperiment(C, I).game(true, rt) @ &m : res].
    pose prIdeal := Pr[ETPExperiment(C, I).game(false, rt) @ &m : !res].
    byphoare (_: (glob ETPExperiment(C, I)) = (glob ETPExperiment(C, I)){m} /\ r = rt ==> _) => //; proc => //.
    seq 1: (b) (1%r/2%r) prReal (1%r/2%r) prIdeal ((glob ETPExperiment(C, I)) = (glob ETPExperiment(C, I)){m} /\ r = rt).
      rnd; wp; skip; smt.
      (* post = b *)
      rnd; wp; skip; smt.
      rewrite /prReal.
        (* b *)
        call (_: (glob ETPExperiment(C, I)) = (glob ETPExperiment(C, I)){m} /\ r = rt /\ real ==> res) => //; last by skip; progress; smt.
        bypr; progress;  byequiv => //; sim; progress; smt.
      (* post = !b *)
      rnd; wp; skip; smt.
      rewrite /prIdeal.
        (* !b *)
        call (_: (glob ETPExperiment(C, I)) = (glob ETPExperiment(C, I)){m} /\ r = rt /\ !real ==> !res) => //; last by skip; progress; smt.
        bypr; progress;  byequiv => //; sim; progress; smt.
    progress; smt.
  qed.

  (*
   *  Advantage: |2*Pr[Main] - 1| = Pr[Real] - Pr[Ideal]
   *)
  lemma etp_advantage (C<: CollectionTP{ETPExperiment}) (I<: EnhancedInverter{ETPExperiment, C}) rt &m:
    islossless I.invert =>
    islossless C.index =>
    islossless C.sample =>
    islossless C.sampleR =>
    islossless C.backward =>
    2%r * Pr[ETPExperiment(C, I).main(rt) @ &m : res] - 1%r =
    Pr[ETPExperiment(C, I).game(true, rt) @ &m : res] - Pr[ETPExperiment(C, I).game(false, rt) @ &m : res].
  proof.
    move => invert_ll index_ll sample_ll sampleR_ll backward_ll.
    pose prReal := Pr[ETPExperiment(C, I).game(true, rt) @ &m : res].
    have ->: Pr[ETPExperiment(C, I).game(false, rt) @ &m : res] = 1%r - Pr[ETPExperiment(C, I).game(false, rt) @ &m : !res].
      rewrite Pr [mu_not].
      have ->: Pr[ETPExperiment(C, I).game(false, rt) @ &m : true] = 1%r.
        byphoare => //; apply (etp_game_ll C I) => //.
      smt.
    pose prIdeal := Pr[ETPExperiment(C, I).game(false, rt) @ &m : !res].
    have ->: (2%r * Pr[ETPExperiment(C, I).main(rt) @ &m : res] - 1%r = prReal - (1%r - prIdeal)) = (Pr[ETPExperiment(C, I).main(rt) @ &m : res] = 1%r/2%r * (prReal + prIdeal)) by smt.
    apply (etp_total_probability C I rt &m).
  qed.

  (*
   * ====================================================================
   *    Properties of hard core predicates on the trapdoor permutation
   * ====================================================================
   *)
  lemma hc_game_ll (C<: CollectionTP) (I<: HCInverter):
    islossless I.invert =>
    islossless C.index =>
    islossless C.sample =>
    islossless C.backward =>
    islossless HCExperiment(C, I).game.
  proof.
    move => invert_ll index_ll sample_ll backward_ll.
    proc => //.
    case (real).
      (* real *)
      rcondt 5; wp.
        kill 3. call backward_ll; trivial.
        kill 2. call sample_ll; trivial.
        kill 1. call index_ll; trivial.
      trivial.
    call invert_ll; wp; call backward_ll; call sample_ll; call index_ll.
    skip; trivial.
      (* !real *)
      rcondf 5; wp.
        kill 3. call backward_ll; trivial.
        kill 2. call sample_ll; trivial.
        kill 1. call index_ll; trivial.
      trivial.
    rnd; wp; call backward_ll; call sample_ll; call index_ll.
    skip; smt.
  qed.

  lemma hc_main_ll (C<: CollectionTP) (I<: HCInverter):
    islossless I.invert =>
    islossless C.index =>
    islossless C.sample =>
    islossless C.backward =>
    islossless HCExperiment(C, I).main.
  proof.
    move => invert_ll index_ll sample_ll backward_ll.
    have game_ll: islossless HCExperiment(C, I).game by apply (hc_game_ll C I).
    proc; call game_ll; rnd; skip; progress; apply (dboolE predT).
  qed.

  (*
   * Total probability
   * Pr[Main] = 1/2 Pr[Real] + 1/2 Pr[Ideal]
   *)
  lemma hc_total_probability (C<: CollectionTP{HCExperiment}) (I<: HCInverter{HCExperiment, C}) &m:
    Pr[HCExperiment(C, I).main() @ &m : res] = 1%r/2%r * (Pr[HCExperiment(C, I).game(true) @ &m : res] + Pr[HCExperiment(C, I).game(false) @ &m : !res]).
  proof.
    pose prReal := Pr[HCExperiment(C, I).game(true) @ &m : res].
    pose prIdeal := Pr[HCExperiment(C, I).game(false) @ &m : !res].
    byphoare (_: (glob HCExperiment(C, I)) = (glob HCExperiment(C, I)){m} ==> _) => //; proc => //.
    seq 1: (b) (1%r/2%r) prReal (1%r/2%r) prIdeal ((glob HCExperiment(C, I)) = (glob HCExperiment(C, I)){m}).
      rnd; wp; skip; smt.
      (* post = b *)
      rnd; wp; skip; smt.
      rewrite /prReal.
        (* b *)
        call (_: (glob HCExperiment(C, I)) = (glob HCExperiment(C, I)){m} /\ real ==> res) => //; last by skip; progress; smt.
        bypr; progress;  byequiv => //; sim; progress; smt.
      (* post = !b *)
      rnd; wp; skip; smt.
      rewrite /prIdeal.
        (* !b *)
        call (_: (glob HCExperiment(C, I)) = (glob HCExperiment(C, I)){m} /\ !real ==> !res) => //; last by skip; progress; smt.
        bypr; progress;  byequiv => //; sim; progress; smt.
    progress; smt.
  qed.

  (*
   *  Advantage: |2*Pr[Main] - 1| = Pr[Real] - Pr[Ideal]
   *)
  lemma hc_advantage (C<: CollectionTP{HCExperiment}) (I<: HCInverter{HCExperiment, C}) &m:
    islossless I.invert =>
    islossless C.index =>
    islossless C.sample =>
    islossless C.backward =>
    2%r * Pr[HCExperiment(C, I).main() @ &m : res] - 1%r =
    Pr[HCExperiment(C, I).game(true) @ &m : res] - Pr[HCExperiment(C, I).game(false) @ &m : res].
  proof.
    move => invert_ll index_ll sample_ll backward_ll.
    pose prReal := Pr[HCExperiment(C, I).game(true) @ &m : res].
    have ->: Pr[HCExperiment(C, I).game(false) @ &m : res] = 1%r - Pr[HCExperiment(C, I).game(false) @ &m : !res].
      rewrite Pr [mu_not].
      have ->: Pr[HCExperiment(C, I).game(false) @ &m : true] = 1%r.
        byphoare => //; apply (hc_game_ll C I) => //.
      smt.
    pose prIdeal := Pr[HCExperiment(C, I).game(false) @ &m : !res].
    have ->: (2%r * Pr[HCExperiment(C, I).main() @ &m : res] - 1%r = prReal - (1%r - prIdeal)) = (Pr[HCExperiment(C, I).main() @ &m : res] = 1%r/2%r * (prReal + prIdeal)) by smt.
    apply (hc_total_probability C I &m).
  qed.

  (*
   * ---- Enhanced hard-core predicate ----
   *)
  lemma ehc_game_ll (C<: CollectionTP) (I<: EnhancedHCInverter):
    islossless I.invert =>
    islossless C.index =>
    islossless C.sampleR =>
    islossless C.backward =>
    islossless EHCExperiment(C, I).game.
  proof.
    move => invert_ll index_ll sample_ll backward_ll.
    proc => //.
    case (real).
      (* real *)
      rcondt 5; wp.
        kill 3. call backward_ll; trivial.
        kill 2. call sample_ll; trivial.
        kill 1. call index_ll; trivial.
      trivial.
    call invert_ll; wp; call backward_ll; call sample_ll; call index_ll.
    skip; trivial.
      (* !real *)
      rcondf 5; wp.
        kill 3. call backward_ll; trivial.
        kill 2. call sample_ll; trivial.
        kill 1. call index_ll; trivial.
      trivial.
    rnd; wp; call backward_ll; call sample_ll; call index_ll.
    skip; smt.
  qed.

  lemma ehc_main_ll (C<: CollectionTP) (I<: EnhancedHCInverter):
    islossless I.invert =>
    islossless C.index =>
    islossless C.sampleR =>
    islossless C.backward =>
    islossless EHCExperiment(C, I).main.
  proof.
    move => invert_ll index_ll sample_ll backward_ll.
    have game_ll: islossless EHCExperiment(C, I).game by apply (ehc_game_ll C I).
    proc; call game_ll; rnd; skip; progress; apply (dboolE predT).
  qed.

  (*
   * Total probability
   * Pr[Main] = 1/2 Pr[Real] + 1/2 Pr[Ideal]
   *)
  lemma ehc_total_probability (C<: CollectionTP{EHCExperiment}) (I<: EnhancedHCInverter{EHCExperiment, C}) rt &m:
    Pr[EHCExperiment(C, I).main(rt) @ &m : res] = 1%r/2%r * (Pr[EHCExperiment(C, I).game(true, rt) @ &m : res] + Pr[EHCExperiment(C, I).game(false, rt) @ &m : !res]).
  proof.
    pose prReal := Pr[EHCExperiment(C, I).game(true, rt) @ &m : res].
    pose prIdeal := Pr[EHCExperiment(C, I).game(false, rt) @ &m : !res].
    byphoare (_: (glob EHCExperiment(C, I)) = (glob EHCExperiment(C, I)){m} /\ c = rt ==> _) => //; proc => //.
    seq 1: (b) (1%r/2%r) prReal (1%r/2%r) prIdeal ((glob EHCExperiment(C, I)) = (glob EHCExperiment(C, I)){m} /\ c = rt).
      rnd; wp; skip; smt.
      (* post = b *)
      rnd; wp; skip; smt.
      rewrite /prReal.
        (* b *)
        call (_: (glob EHCExperiment(C, I)) = (glob EHCExperiment(C, I)){m} /\ c = rt /\ real ==> res) => //; last by skip; progress; smt.
        bypr; progress;  byequiv => //; sim; progress; smt.
      (* post = !b *)
      rnd; wp; skip; smt.
      rewrite /prIdeal.
        (* !b *)
        call (_: (glob EHCExperiment(C, I)) = (glob EHCExperiment(C, I)){m} /\ c = rt /\ !real ==> !res) => //; last by skip; progress; smt.
        bypr; progress;  byequiv => //; sim; progress; smt.
    progress; smt.
  qed.

  (*
   *  Advantage: |2*Pr[Main] - 1| = Pr[Real] - Pr[!Ideal]
   *)
  lemma ehc_advantage (C<: CollectionTP{EHCExperiment}) (I<: EnhancedHCInverter{EHCExperiment, C}) rt &m:
    islossless I.invert =>
    islossless C.index =>
    islossless C.sampleR =>
    islossless C.backward =>
    2%r * Pr[EHCExperiment(C, I).main(rt) @ &m : res] - 1%r =
    Pr[EHCExperiment(C, I).game(true, rt) @ &m : res] - Pr[EHCExperiment(C, I).game(false, rt) @ &m : res].
  proof.
    move => invert_ll index_ll sample_ll backward_ll.
    pose prReal := Pr[EHCExperiment(C, I).game(true, rt) @ &m : res].
    have ->: Pr[EHCExperiment(C, I).game(false, rt) @ &m : res] = 1%r - Pr[EHCExperiment(C, I).game(false, rt) @ &m : !res].
      rewrite Pr [mu_not].
      have ->: Pr[EHCExperiment(C, I).game(false, rt) @ &m : true] = 1%r.
        byphoare => //; apply (ehc_game_ll C I) => //.
      smt.
    pose prIdeal := Pr[EHCExperiment(C, I).game(false, rt) @ &m : !res].
    have ->: (2%r * Pr[EHCExperiment(C, I).main(rt) @ &m : res] - 1%r = prReal - (1%r - prIdeal)) = (Pr[EHCExperiment(C, I).main(rt) @ &m : res] = 1%r/2%r * (prReal + prIdeal)) by smt.
    apply (ehc_total_probability C I rt &m).
  qed.

  (*
   * ==============================================
   *    Implementation of a generic CTP and ECPT
   * ==============================================
   *)
  module CTP: CollectionTP = {
    proc index(): keypair = {
      var k, r;

      r =$ dcoins;
      k = (index \o singleton_rtape) r;

      return k;
    }

    proc sample(a: alpha): D = {
      var x;

      x =$ dD a;

      return x;
    }

    proc forward(a: alpha, x: D): D = {
      var y;

      y = forward a x;

      return y;
    }

    proc backward(t: tau, y: D): D = {
      var x;

      x = backward t y;

      return x;
    }

    proc validk(k: keypair): bool = {
      return (fst k) = owf (snd k);
    }

    proc validx(k: keypair, x: D): bool = {
      var a, t, y, x';

      (a, t) <- k;
      y  <- forward a x;
      x' <- backward t y;

      return (x = x');
    }

    (* Deterministic versions of index and sample *)
    proc indexR(r: rtape): keypair = {
      var k;

      k = index r;

      return k;
    }

    proc sampleR(a: alpha, r: rtape): D = {
      var x, y;

      x = sample a r;
      y = sample a r;

      return x;
    }
  }.

  (* Enhanced CTP has a reverse domain function/algorithm *)
  module ECTP: CollectionTP, ReverseDomain = {
    proc index    = CTP.index
    proc sample   = CTP.sample
    proc forward  = CTP.forward
    proc backward = CTP.backward
    proc validk   = CTP.validk
    proc validx   = CTP.validx
    proc indexR   = CTP.indexR
    proc sampleR  = CTP.sampleR
  
    (* ReverseDomain *)
    proc rdsample(a: alpha, x: D) = {
      var r;

      r = rdsample a x;

      return r;
    }
  }.

  (*
   * =================================
   *    Security properties for CTP
   * =================================
   *)
  lemma ctp_index_ll:
    is_lossless dcoins =>
    islossless CTP.index
  by move => *; proc; auto.

  lemma ctp_sample_ll:
    (forall a, is_lossless (dD a)) =>
    islossless CTP.sample
  by move => *; proc; auto; progress; smt.

  lemma ctp_forward_ll:  islossless CTP.forward by proc; auto.
  lemma ctp_backward_ll: islossless CTP.backward by proc; auto.
  lemma ctp_validk_ll:   islossless CTP.validk by proc; auto.
  lemma ctp_validx_ll:   islossless CTP.validx by proc; auto.
  lemma ctp_sampleR_ll:  islossless CTP.sampleR by proc; auto.
  lemma ctp_indexR_ll:   islossless CTP.indexR by proc; auto.

  lemma nosmt ctp_correct_ct:
    hoare[Correctness(CTP).main : ct index sample forward backward ==> res].
  proof.
    rewrite /(-<) /cancel /=; move => *; proc.
    seq 3: (vx /\ (forward a) -< (backward t)); inline*; auto.
      progress; rewrite /(-<) /cancel /(\o) /=; smt.
    smt.
  qed.

  (*
   * ==================================
   *    Security properties for ECTP
   * ==================================
   *)
  lemma ectp_index_ll:
    is_lossless dcoins =>
    islossless ECTP.index
  by move => *; proc; auto.

  lemma ectp_sample_ll:
    (forall a, is_lossless (dD a)) =>
    islossless ECTP.sample
  by move => *; proc; auto; progress; smt.

  (* reverse domain *)
  lemma ectp_rdsample_ll: islossless ECTP.rdsample by proc; auto.

  lemma ectp_forward_ll:  islossless ECTP.forward by proc; auto.
  lemma ectp_backward_ll: islossless ECTP.backward by proc; auto.
  lemma ectp_validk_ll:   islossless ECTP.validk by proc; auto.
  lemma ectp_validx_ll:   islossless ECTP.validx by proc; auto.
  lemma ectp_sampleR_ll:  islossless ECTP.sampleR by proc; auto.
  lemma ectp_indexR_ll:   islossless ECTP.indexR by proc; auto.

  lemma nosmt ectp_correct_ctp:
    hoare[Correctness(ECTP).main : ct index sample forward backward ==> res].
  proof.
    rewrite /(-<) /cancel /=; move => *; proc.
    seq 3: (vx /\ (forward a) -< (backward t)); inline*; auto.
      progress; rewrite /(-<) /cancel /(\o) /=; smt.
    smt.
  qed.

end TrapdoorPermutation.
