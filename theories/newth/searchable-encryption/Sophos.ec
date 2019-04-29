

(*
 * Sophos.
 *)(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2018 - Roberto Metere <r.metere2@ncl.ac.uk>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)
require import Core.
require import TacticsExt.
require import Bool.
require import Int.
require import IntExtra.
require import IntExt.
require import LogicExt.
require import Ring Real StdRing.
require import RealExtra.
require import Finite.
require import DBool.
require import List.
require import Distr.
require (*--*) NewPRF IdealPRF.
require (*--*) PRFExt.
require (*--*) PRPExt.
require import TrapdoorPerm.
require import FSet.
require import FSetExt.
require import SmtMap.
require import SmtMapExt.
require import ListExt.
require (*--*) HashFunction.
require import SSE.
require (*--*) BitWord.

type stoken.
type alpha.
type key.
type mapquery.

(* These bitstring lenghts *)
const    utlen: { int | 0 < utlen } as utlen_gt0.
const indexlen: { int | 0 < indexlen } as indexlen_gt0.

type utoken.
type index.

(* Global oracle bound *)
const q : {int | 0 <= q } as q_ge0.

theory DBitstring.
  op len: { int | 0 < len } as len_gt0.

  clone import BitWord as Bitstring with
    op n = len
  rename "word" as "bitstring".

  op int2bs : int -> bitstring.

  clone include MFinite with
    type t <- bitstring,
    op Support.enum <- List.map int2bs (List.Iota.iota_ 0 (2^len)),
    op Support.card <- 2^len
  rename "dunifin" as "dbitstring".
end DBitstring.

clone import DBitstring as TokenDistribution with
  type Bitstring.bitstring <- utoken,
  op len = utlen
rename "dbitstring" as "dut"
       "bitstring" as "utoken".
import TokenDistribution.Bitstring.

clone import DBitstring as IndexDistribution with
  type Bitstring.bitstring <- index,
  op len = indexlen
rename "dbitstring" as "di"
       "bitstring" as "index".
import IndexDistribution.Bitstring.

lemma dut_pr: forall x, mu1 dut x = inv (2^utlen)%r by smt.
lemma  di_pr: forall x, mu1  di x = inv (2^indexlen)%r by smt.

op dkey: {      key distr | is_lossless dkey } as dkey_ll.
op  dmq: { mapquery distr | is_lossless dmq } as dmapquery_ll.
op   ds: {   stoken distr | is_lossless ds } as dstoken_ll.

(* Keys are sortable through a total-order relation *)
pred partialorder ['a] (R : 'a -> 'a -> bool) = reflexive R /\ antisymmetric R /\ transitive R.
pred totalorder ['a] (R : 'a -> 'a -> bool) = partialorder R /\ total R.
op (<=): { key rel | totalorder (<=) } as ko_to.

clone import SearchableSymmetricEncryption as SE with
  type stoken <- stoken,
  type utoken <- utoken,
  type index  <- index,
  type setupserver = alpha,

  type key <- key,
  type mapquery <- mapquery,

  op dkey <- dkey,
  op dmapquery = dmq,
  op dutoken = dut,
  op dstoken = ds,

  (* Sophos encrypted database are the tokens associated to indexes *)
  type encryptedstorage = (utoken, index) fmap,
  type state = (query, stoken * int) fmap,

  (* Oracle types (the same input for both hash functions) *)
  type SSEOracleTheory.sseo_args_t =  (mapquery * stoken),
  type SSEOracleTheory.sseo_res_t = utoken option * index option,

  (* Leakage *)
  type Lsetup  = unit,
  type Lupdate = operation,
  type Lquery  = int list * uhpattern.
import SE.SSEOracleTheory.

clone import TrapdoorPermutation as TP with
  type D <- stoken,
  type alpha <- alpha.
import TP.

clone import PRFExt as PRFTheory with
  type K <- key,
  type D <- query,
  type R <- mapquery,
  op dK <- dkey,
  op dR <- dmq
rename "RandomKeyedFunction" as "RKF".
import PRFTheory PRF.
import PRFTheory PRFi.

(*
 * At some point in the proof, we need to replace the functionality of pseudorandom functions
 * with that of pseudorandom permutations.
 * Distinguishing between the two is as easy as to call the oracle n <= |Range| times until we get
 * a collision, in which case the oracle must have called the pseudorandom function, otherwise
 * the distinguisher will claim that a pseudorandom permutation was called.
 * The probability of guessing is reconducible to the birthday problem.
 *
 * We therefore need to explicitly bound the calls to the oracle performed by the distinguisher.
 * We stress that this is NOT a restriction to the attacker, since by definition it is
 * supposed to be a probabilistic polynomial-time Turing Machine.
 *
 *
 * A function from query to mapquery is required to switch to a permutation.
 * Queries are picked from finite subsets of all strings. Realistically, the cardinality of
 * such subsets are comparable to dictionaries.
 * Even if it were "irrealistically" a huge number (yet polynomially bound), we could always
 * choose the mapquery set to have cardinality bigger or equal to that of queries.
 *
 * An important property that allows us to keep collisions under "control" is the injectivity of
 * the type converter from query to mapquery given that the conversion is done from a smaller
 * or equal set.
 *
 * In the other case when query is bigger than mapquery, collisions may occur.
 * If query is much bigger a set, then consistency of the simulating game is not achieved.
 * If query is just bit bigger a set, then consistency is "computationally" achieved but the proofs
 * become quite burdensome.
 * We stress that, in a real setting, mapquery is easily bigger than the space of queries
 * or can be extended to be as such.
 *
 * In brief.
 * query - finite subset of strings
 * mapquery - injective map from queries
 *)
op mq : query -> mapquery.
op mq_inv : { mapquery -> query | forall q, mq_inv (mq q) = q } as mq_mq_inv_cancel.

lemma mq_inj: injective mq by smt.

clone import PRPExt as PRPTheory with
  op q <- q,
  type K <- key,
  type D <- mapquery,
  op dK <- dkey,
  op dD <- dmq
rename "RandomKeyedPermutation" as "RKP".
import PRPTheory SPRP.
import PRPTheory SPRPi.

module OracleCallsCounter(D: SSEDistROM, SA: SSEAccess) = {
  module SSEAccessBounder = {
    var calls : int (* we count al the calls to available oracles *)

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var r = witness;

      if (calls < Top.q) {
        r <@ SA.update(o, q, i);
        calls <- calls + 1;
      }
      return r;
    }

    proc query(q: query): (mapquery * stoken * int) option * index list = {
      var r = witness;

      if (calls < Top.q) {
        r <@ SA.query(q);
        calls <- calls + 1;
      }
      return r;
    }

    proc o(x: int * sseo_args_t): sseo_res_t option = {
      var r = witness;

      if (calls < Top.q) {
        r <@ SA.o(x);
        calls <- calls + 1;
      }
      return r;
    }
  }

  proc distinguish(): bool = {
    var b;

    SSEAccessBounder.calls <- 0;
    b <@ D(SSEAccessBounder).distinguish();
    return b;
  }
}.

lemma occ_update_ll (D<: SSEDistROM) (SA<: SSEAccess):
  islossless SA.update =>
  islossless OracleCallsCounter(D,SA).SSEAccessBounder.update.
proof.
  move => update_ll.
  proc.
  sp; if => //; wp; call update_ll; wp; skip; progress.
qed.

lemma occ_query_ll (D<: SSEDistROM) (SA<: SSEAccess):
  islossless SA.query =>
  islossless OracleCallsCounter(D,SA).SSEAccessBounder.query.
proof.
  move => query_ll.
  proc.
  sp; if => //; wp; call query_ll; wp; skip; progress.
qed.

lemma occ_o_ll (D<: SSEDistROM) (SA<: SSEAccess):
  islossless SA.o =>
  islossless OracleCallsCounter(D,SA).SSEAccessBounder.o.
proof.
  move => o_ll.
  proc.
  sp; if => //; wp; call o_ll; wp; skip; progress.
qed.

lemma occ_distinguish_ll (D<: SSEDistROM) (SA<: SSEAccess):
  islossless D(OracleCallsCounter(D,SA).SSEAccessBounder).distinguish =>
  islossless OracleCallsCounter(D,SA).distinguish.
proof.
  move => distinguish_ll.
  proc; call distinguish_ll; wp; skip; progress.
qed.

clone import HashFunction as HFTheory1 with
  op q <- q,
  type D <- mapquery * stoken,
  type C <- utoken,
  op cdistr <- dut
rename "HashOracleTheory" as "HashOracleTheory1"
       "HashOracle" as "HashOracle1"
       "OracleAccess" as "OracleAccess1"
       "HashFunction" as "HashFunction1"
       "HashExp" as "HashExp1"
       "ROM" as "ROM1".

clone import HashFunction as HFTheory2 with
  op q <- q,
  type D <- mapquery * stoken,
  type C <- index,
  op cdistr <- di
rename "HashOracleTheory" as "HashOracleTheory2"
       "HashOracle" as "HashOracle2"
       "OracleAccess" as "OracleAccess2"
       "HashFunction" as "HashFunction2"
       "HashExp" as "HashExp2"
       "ROM" as "ROM2".

import HFTheory1 HashOracleTheory1 ROM1.
import HFTheory2 HashOracleTheory2 ROM2.

(* We need two hash random oracles, and two hash oracles built from hash functions *)
clone import HashROM1 as HR1
rename "RO" as "RO1".
clone import HashROM2 as HR2
rename "RO" as "RO2".
clone import HashOracleTheory1 as HT1
rename "HOracle" as "HO1".
clone import HashOracleTheory2 as HT2
rename "HOracle" as "HO2".

module HashRO1: HashOracle1 = {
  proc init = RO1.init
  proc hash(x: mapquery * stoken): utoken = {
    var y;

    y <@ RO1.o(x);

    return y;
  }
}.

module HashRO2: HashOracle2 = {
  proc init = RO2.init
  proc hash(x: mapquery * stoken): index = {
    var y;

    y <@ RO2.o(x);

    return y;
  }
}.

(* Oracle call macros, just indexes *)
const HASH1 = 1.
const HASH2 = 2.

theory SophosImplementation.
  module SophosClient(F: PRF, H1: HashFunction1, H2: HashFunction2): SSEClient = {
    var k: key
    var sk: tau
    var ws: state

    proc setup(): setupserver = {
      var pk;

      k <@ F.keygen();
      (pk, sk) <@ CTP.index();
      ws <- empty;

      return pk;
    }

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var kw, s, c, sc, ut, idx, ti;

      if (o = ADD) {
        kw <@ F.f(k, q);
        if (!dom ws q) {
          s <$ dstoken;
          c <- 0;
        } else {
          sc <- oget ws.[q];
          s <@ CTP.backward(sk, fst sc);
          c <- snd sc + 1;
        }
        ws.[q] <- (s, c);
        ut <@ H1.hash(kw, s);
        idx <@ H2.hash(kw, s);
        idx <- i +^ idx;
        ti <- Some(ut, idx);
      } else {
        ti <- None;
      }

      return ti;
    }

    proc query(q: query): (mapquery * stoken * int) option = {
      var kw, sc;
      var r: (mapquery * stoken * int) option;

      if (!dom ws q) {
        r <- None;
      } else {
        kw <@ F.f(k, q);
        sc <- oget ws.[q];
        r <- Some (kw, fst sc, snd sc);
      }

      return r;
    }

    proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
      var h1, h2, h;

      h <- None;
      if     (i = HASH1) {
        h1 <@ H1.hash(argv);
        h <- Some(Some(h1), None);
      } elif (i = HASH2) {
        h2 <@ H2.hash(argv);
        h <- Some(None, Some(h2));
      }

      return h;
    }
  }.

  module SophosServer(H1: HashFunction1, H2: HashFunction2): SSEServer = {
    var edb: encryptedstorage
    var pk: alpha

    proc setup(s: setupserver): unit = {
      pk <- s;
      edb <- empty;
    }

    proc update(o: operation, t: utoken, i: index): unit = {
      if (o = ADD) {
        edb.[t] <- i;
      }
    }

    proc query(kw: mapquery, t: stoken, c: int): index list = {
      var i, ut, ind;
      var r: index list;

      r <- [];
      i <- 0;
      while (i <= c) {
        (* We expect to have "mem (dom edb) ut" always true for all legitimate queries *)
        ut <@ H1.hash(kw, t);
        ind <@ H2.hash(kw, t);
        ind <- (oget edb.[ut]) +^ ind;
        r <- ind :: r;
        t <@ CTP.forward(pk, t);
        i <- i + 1;
      }

      return r;
    }
  }.
end SophosImplementation.
import SophosImplementation.

section Sophos.
  module Sophos(F: PRF, H1: HashFunction1, H2: HashFunction2) = SSEProtocol(SophosClient(F, H1, H2), SophosServer(H1, H2)).

  section SophosSecurity.
    lemma sophos_client_update_ll (F<: PRF) (H1<: HashFunction1) (H2<: HashFunction2):
      islossless F.f =>
      islossless H1.hash =>
      islossless H2.hash =>
      islossless SophosClient(F, H1, H2).update.
    proof.
      move => Ff_ll H1hash_ll H2hash_ll.
      proc; inline*. wp.
      if => //; last by wp; skip; trivial.
      seq 1: true => //.
        wp; call (_: true) => //.
      wp; call (_: true) => //; call (_: true) => //.
      if; first by wp; rnd; skip; progress; rewrite dstoken_ll //.
      (* else *) wp; wp; skip; progress; trivial.
    qed.

    lemma sophos_client_query_ll (F<: PRF{SophosClient}) (H1<: HashFunction1) (H2<: HashFunction2):
      islossless F.f =>
      islossless SophosClient(F, H1, H2).query.
    proof.
      move => Ff_ll; proc; inline*.
      if => //; first by wp; skip; progress; trivial.
      wp; call (_: true) => //.
    qed.

    lemma sophos_server_update_ll (H1<: HashFunction1) (H2<: HashFunction2):
      islossless SophosServer(H1, H2).update.
    proof.
      proc; inline*; wp; skip; trivial.
    qed.

    lemma sophos_server_query_ll (H1<: HashFunction1{SophosServer}) (H2<: HashFunction2{SophosServer}):
      islossless H1.hash =>
      islossless H2.hash =>
      islossless SophosServer(H1, H2).query.
    proof.
      move => H1hash_ll H2hash_ll.
      proc; inline*; sp.
      case (0 <= c).
        (* 0 <= c *)
        while (0 <= i <= c + 1) (c - i + 1); progress.
          wp; call H2hash_ll; wp; call H1hash_ll; skip; progress.
          + rewrite (lez_trans i{hr}) // -(lez_add2l (-i{hr})) addzA //.
          + rewrite lez_add2r //.
          + rewrite IntID.opprD addzA /= -(ltz_add2l (- c{hr})) 3!addzA /= -(ltz_add2r (i{hr})) -addzA //.
        wp; skip; progress.
        + rewrite (lez_trans c{hr}) // -(lez_add2l (-c{hr})) addzA //.
        + rewrite lezNgt /= -lez_add1r -(lez_add2r (-i0)) /= -addzA addzC; assumption.
        (* ! 0 <= c *)
        rcondf 1; progress.
   qed.

  lemma sophos_setup_ll (F<: PRF) (H1<: HashFunction1) (H2<: HashFunction2):
    is_lossless dcoins =>
    islossless F.keygen =>
    islossless Sophos(F, H1, H2).setup.
  proof.
    move => dcoins_ll keygen_ll.
    proc; inline *.
    wp; rnd; wp; call keygen_ll; skip; progress.
  qed.

  lemma sophos_update_ll (F<: PRF{Sophos}) (H1<: HashFunction1) (H2<: HashFunction2):
    islossless F.f =>
    islossless H1.hash =>
    islossless H2.hash =>
    islossless Sophos(F, H1, H2).update.
  proof.
    move : dstoken_ll => _ sample_ll h1_ll h2_ll.
    proc; inline*.
    sp; if => //.
    + case (dom SophosClient.ws q0).
      * rcondf 2; progress; first by call (_: true) => //.
        wp; call h2_ll; call h1_ll; wp; call sample_ll; skip; progress.
      * rcondt 2; progress; first by call (_: true) => //.
        wp; call h2_ll; call h1_ll; wp; rnd; call sample_ll; skip; progress.
    + wp; skip; progress.
  qed.

  lemma sophos_query_ll (F<: PRF{Sophos}) (H1<: HashFunction1) (H2<: HashFunction2):
    islossless F.f =>
    islossless H1.hash =>
    islossless H2.hash =>
    islossless Sophos(F, H1, H2).query.
  proof.
    move => sample_ll h1_ll h2_ll.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i <= c + 1) (c + 1 - i) => //=; progress.
          wp; call h2_ll; call h1_ll; wp; skip; progress; smt.
        wp; skip; progress.
    + rcondf 5; progress; first by wp.
      case (0 <= (oget SophosClient.ws.[q0]).`2).
      - wp => /=; while (0 <= i <= c + 1) (c + 1 - i) => //=; progress.
          wp; call h2_ll; call h1_ll; wp; skip; progress; smt.
        wp; call sample_ll; skip; progress => //.
        + rewrite oget_some /=; smt.
        + smt.
      - rcondf 8; progress; first by wp; call (_: true) => //; skip; progress.
        wp; call sample_ll; skip; progress.
  qed.

  lemma sophos_o_ll (F<: PRF) (H1<: HashFunction1) (H2<: HashFunction2):
    islossless H1.hash =>
    islossless H2.hash =>
    islossless Sophos(F, H1, H2).o.
  proof.
    move => h1_ll h2_ll.
    proc; inline*.
    sp; if => //; first by wp; call h1_ll; skip; progress.
    sp; if => //; first by wp; call h2_ll; skip; progress.
  qed.

  (**
   * Leakage for Sophos
   *)
  module SophosLeakage: SSELeakage = {
    var h: history

    proc leakSetup() = {
      h <- [];
    }

    proc leakUpdate(o: operation, q: query, i: index): Lupdate = {
      var db;

      if (o = ADD) {
        db <- lastdb h;
        if (!(dom db i)) {
          db.[i] <- [q];
        } else {
          db.[i] <- (oget db.[i]) ++ [q];
        }
        h <- h ++ [(size h, (db, Some(o, q, i), None))];
      }
      (* Shall we record unsupported operations? *)

      return o;
    }

    proc leakQuery(q: query): Lquery = {
      var lq;

      h <- h ++ [(size h, (lastdb h, None, Some(q)))];
      lq <- (qp h q, ahpU h q);

      return lq;
    }
  }.

  lemma leaksetup_ll:
    islossless SophosLeakage.leakSetup.
  proof.
    proc; wp; progress.
  qed.

  lemma leakupdate_ll:
    islossless SophosLeakage.leakUpdate.
  proof.
    proc; wp; progress.
  qed.

  lemma leakquery_ll:
    islossless SophosLeakage.leakQuery.
  proof.
    proc; wp; progress.
  qed.

  module SophosSimulator(C: CollectionTP): SSESimulator = {
    var sk: tau
    var pk: alpha

    var t: int (* auto-incrementing timestamp *)
    var wssim: (int, stoken) fmap (* the state knows not the corresponding query *)
    var keys: (int, mapquery) fmap
    var utokens: (int, utoken) fmap
    var idxs: (int, index) fmap
    var h1t: (mapquery * stoken, utoken) fmap
    var h2t: (mapquery * stoken, index) fmap
    var edb: encryptedstorage

    proc f(w: int): mapquery = {
      if (!(dom keys w)) {
        keys.[w] <$ dmq;
      }

      return oget keys.[w];
    }

    proc ws(w: int): stoken = {
      if (!(dom wssim w)) {
        wssim.[w] <$ dstoken;
      }

      return oget wssim.[w];
    }

    proc hash1(hi: mapquery, s: stoken): utoken = {
      if (!(dom h1t (hi, s))) {
        h1t.[(hi, s)] <$ dutoken;
      }

      return oget h1t.[(hi, s)];
    }

    proc hash2(hi: mapquery, s: stoken): index = {
      if (!(dom h2t (hi, s))) {
        h2t.[(hi, s)] <$ di;
      }

      return oget h2t.[(hi, s)];
    }

    proc setup(ls: Lsetup): setupserver = {
      (pk, sk) <@ C.index();
      wssim   <- empty;
      t       <- 0;
      keys    <- empty;
      utokens <- empty;
      idxs    <- empty;
      h1t     <- empty;
      h2t     <- empty;
      edb     <- empty;

      return pk;
    }

    proc update(o: operation): (utoken * index) option = {
      var ti;

      if (o = ADD) {
        (* client part *)
        utokens.[t] <$ dut;
        idxs.[t] <$ di;
        ti <- Some(oget utokens.[t], oget idxs.[t]);

        (* server part *)
        edb.[oget utokens.[t]] <- oget idxs.[t];

        t <- t + 1;
      } else {
        ti <- None;
      }

      return ti;
    }

    proc query(spat: int list, uhpat: uhpattern): (mapquery * stoken * int) option * index list = {
      var qo, rl;
      var w, kw, i, j, s, z, o, ind, addpat;

      addpat <- filter (fun (x: int * operation * index) => x.`2 = ADD) uhpat;
      if (addpat <> []) {
        w <- head witness spat; (* assuming spat is already time-ordered *)
        kw <@ f(w);

        rl <- [];

        (* client part *)
        ws(w);
        s <- witness; (* avoid complaining about being uninitialised *)
        i <- 0;
        while (i < size addpat) {
          if (i = 0) {
            s <- oget wssim.[w];
          } else {
            s <@ C.backward(sk, s);
          }
          (j, o, ind) <- nth witness addpat i;
          h1t.[(kw, s)] <- oget utokens.[j];
          h2t.[(kw, s)] <- ind +^ oget idxs.[j];
          i <- i + 1;
        }

        (* server part *)
        z <- s;
        i <- 0;
        while (i < size addpat) {
          ind <- oget edb.[oget h1t.[(kw, z)]] +^ oget h2t.[(kw, z)];
          rl <- ind :: rl;
          z <@ C.forward(pk, z);

          i <- i + 1;
        }
        qo <- Some(kw, s, size addpat - 1);
      } else {
        qo <- None;
        rl <- [];
      }

      (* This is important to emulate the timestamp of the leakage function - yet another mistake in the original proof *)
      t <- t + 1;

      return (qo, rl);
    }

    proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
      var h1, h2, ho;

      ho <- None;
      if     (i = HASH1) {
        h1 <@ hash1(argv);
        ho <- Some(Some(h1), None);
      } elif (i = HASH2) {
        h2 <@ hash2(argv);
        ho <- Some(None, Some(h2));
      }

      return ho;
    }
  }.

  lemma sim_f_ll (C<: CollectionTP):
    islossless SophosSimulator(C).f.
  proof.
    proc; if => //.
    rnd; wp; skip; progress; rewrite dmapquery_ll //.
  qed.

  lemma sim_ws_ll (C<: CollectionTP):
    islossless SophosSimulator(C).ws.
  proof.
    proc; if => //.
    rnd; wp; skip; progress; rewrite dstoken_ll //.
  qed.

  lemma sim_hash1_ll (C<: CollectionTP):
    islossless SophosSimulator(C).hash1.
  proof.
    proc; if => //.
    rnd; wp; skip; progress; rewrite dut_ll //.
  qed.

  lemma sim_hash2_ll (C<: CollectionTP):
    islossless SophosSimulator(C).hash2.
  proof.
    proc; if => //.
    rnd; wp; skip; progress; rewrite di_ll //.
  qed.

  lemma sim_setup_ll (C<: CollectionTP):
    islossless C.index =>
    islossless SophosSimulator(C).setup.
  proof.
    move => i_ll.
    proc; inline*.
    wp; call i_ll; skip; progress.
  qed.

  lemma sim_update_ll (C<: CollectionTP):
    islossless SophosSimulator(C).update.
  proof.
    move : di_ll dut_ll => _ _.
    proc; if => //.
    + wp; rnd; rnd; skip; progress.
    + wp; progress.
  qed.

  lemma sim_query_ll (C<: CollectionTP):
    islossless C.forward =>
    islossless C.backward =>
    islossless SophosSimulator(C).query.
  proof.
    move : dmapquery_ll dstoken_ll => _ _ f_ll b_ll.
    proc; inline *.
    sp; if => //.
    +  wp => /=; while (0 <= i <= size addpat) (size addpat - i) => //; progress.
         wp; call f_ll; wp; skip; progress; smt.
       wp => /=; while (0 <= i <= size addpat) (size addpat - i) => //; progress.
         wp; if => //.
         * wp; skip; progress; smt.
         * call b_ll; skip; progress; smt.
       wp => /=; sp; if => //.
       * swap 4 -3; swap 5 -3; sp; if => //.
         - wp; rnd; rnd; skip; progress; smt.
         - wp; rnd; skip; progress; smt.
       * swap 3 -2; swap 4 -2; sp; if => //.
         - wp; rnd; skip; progress; smt.
         - wp; skip; progress; smt.
    + wp; progress.
  qed.

  lemma sim_o_ll (C<: CollectionTP):
    islossless SophosSimulator(C).o.
  proof.
    move : dut_ll di_ll => _ _.
    proc; inline *.
    sp; if => //.
    + sp; if => //.
      * wp; rnd; skip; progress.
      * wp; skip; progress.
    + if => //; sp; if => //.
      * wp; rnd; skip; progress.
      * wp; skip; progress.
  qed.

  (*
   * === Part1 ===
   * Indistinguishable game using true random instead of PRF
   *)
  clone SophosImplementation as Game1
  rename "SophosClient" as "Client"
  rename "SophosServer" as "Server".

  module G1(H1: HashFunction1, H2: HashFunction2) = SSEProtocol(Game1.Client(RKF, H1, H2), Game1.Server(H1, H2)).

  lemma G1_setup_ll (H1<: HashFunction1) (H2<: HashFunction2):
    is_lossless dcoins =>
    islossless G1(H1, H2).setup.
  proof.
    move : dkey_ll => _ dcoins_ll.
    proc; inline *.
    wp; rnd; wp; rnd; skip; progress.
  qed.

  lemma G1_update_ll (H1<: HashFunction1) (H2<: HashFunction2):
    islossless H1.hash =>
    islossless H2.hash =>
    islossless G1(H1, H2).update.
  proof.
    move : dmapquery_ll dstoken_ll => _ _ h1_ll h2_ll.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * swap 3 -2; if => //.
        - wp; call h2_ll; call h1_ll; wp; rnd; wp; rnd; skip; progress.
        - wp; call h2_ll; call h1_ll; wp; rnd; wp; skip; progress.
      * sp; if => //.
        - wp; call h2_ll; call h1_ll; wp; rnd; wp; skip; progress.
        - wp; call h2_ll; call h1_ll; wp; skip; progress.
    + wp; skip; progress.
  qed.

  lemma G1_query_ll (H1<: HashFunction1) (H2<: HashFunction2):
    islossless H1.hash =>
    islossless H2.hash =>
    islossless G1(H1, H2).query.
  proof.
    move : dmapquery_ll dstoken_ll => _ _ h1_ll h2_ll.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i <= c + 1) (c + 1 - i) => //=; progress.
          wp; call h2_ll; call h1_ll; wp; skip; progress; smt.
        wp; skip; progress.
    + sp; if => //.
      * rcondf 6; progress; first by wp; rnd; skip; progress.
        case (0 <= (oget Game1.Client.ws.[q0]).`2).
        - wp => /=; while (0 <= i <= c + 1) (c + 1 - i) => //=; progress.
            wp; call h2_ll; call h1_ll; wp; skip; progress; smt.
          wp; rnd (predT); skip; progress => //.
          + rewrite oget_some get_set_sameE oget_some /=; smt.
          + smt.
        - rcondf 9; progress; first by wp; rnd; skip; progress.
          wp; rnd; progress.
      * sp; if => //; first by wp; skip; progress.
        case (0 <= (oget Game1.Client.ws.[q0]).`2).
        - wp => /=; while (0 <= i <= c + 1) (c + 1 - i) => //=; progress.
            wp; call h2_ll; call h1_ll; wp; skip; progress; smt.
          wp; skip; progress => //.
          + rewrite oget_some /=; smt.
          + smt.
        - rcondf 4; progress; first by wp; skip; progress.
          wp; progress.
  qed.

  lemma G1_o_ll (H1<: HashFunction1) (H2<: HashFunction2):
    islossless H1.hash =>
    islossless H2.hash =>
    islossless G1(H1, H2).o.
  proof.
    move => h1_ll h2_ll.
    proc; inline*.
    sp; if => //; first by wp; call h1_ll; skip; progress.
    sp; if => //; first by wp; call h2_ll; skip; progress.
  qed.

  (* Sophos-Pseudorandom Function Reduction *)
  module SP_Red(H1: HashFunction1, H2: HashFunction2, D: SSEDistROM, F: PRFOracleAccess) (* : PRFDist, SSEAccess *) = {

    module Client: SSEClient = {
      var sk: tau
      var ws: state

      proc setup(): setupserver = {
        var pk;

        (* No keygen call *)
        (pk, sk) <@ CTP.index();
        ws <- empty;

        return pk;
      }

      proc update(o: operation, q: query, i: index): (utoken * index) option = {
        var kw, s, c, sc, ut, idx, ti;

        if (o = ADD) {
          kw <@ F.f(q); (* Oracle access *)
          if (!dom ws q) {
            s <$ dstoken;
            c <- 0;
          } else {
            sc <- oget ws.[q];
            s <@ CTP.backward(sk, fst sc);
            c <- snd sc + 1;
          }
          ws.[q] <- (s, c);
          ut <@ H1.hash(kw, s);
          idx <@ H2.hash(kw, s);
          idx <- i +^ idx;
          ti <- Some(ut, idx);
        } else {
          ti <- None;
        }

        return ti;
      }

      proc query(q: query): (mapquery * stoken * int) option = {
        var kw, sc;
        var r: (mapquery * stoken * int) option;

        if (!dom ws q) {
          r <- None;
        } else {
          kw <@ F.f(q); (* Oracle access *)
          sc <- oget ws.[q];
          r <- Some (kw, fst sc, snd sc);
        }

        return r;
      }

      proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
        var h1, h2, ho;

        ho <- None;
        if     (i = HASH1) {
          h1 <@ H1.hash(argv);
          ho <- Some(Some(h1), None);
        } elif (i = HASH2) {
          h2 <@ H2.hash(argv);
          ho <- Some(None, Some(h2));
        }

        return ho;
      }
    }

    module Server = SophosServer(H1, H2)

    module Scheme = SSEProtocol(Client, Server)

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var t, idx, ti;

      ti <@ Client.update(o, q, i);
      if (ti <> None) {
        (t, idx) <- oget ti;
        Server.update(o, t, idx);
      }

      return ti;
    }

    proc query(q: query): (mapquery * stoken * int) option * index list = {
      var qo, rl;

      qo <@ Client.query(q);
      if (qo = None) {
        rl <- [];
      } else {
        rl <@ Server.query(oget qo);
      }

      return (qo, rl);
    }

    proc distinguish(): bool = {
      var g;

      Scheme.setup();
      g <@ D(Scheme).distinguish();

      return g;
    }
  }.

  lemma sophos_G1_reduction_to_prfexp
    (F <:                PRF{SP_Red,RKF,PRFO1.PRFO1,PRFO2.PRFO2,Sophos,G1,OracleCallsCounter})
    (H1<:    HashFunction1{F,SP_Red,RKF,PRFO1.PRFO1,PRFO2.PRFO2,Sophos,G1,OracleCallsCounter})
    (H2<: HashFunction2{H1,F,SP_Red,RKF,PRFO1.PRFO1,PRFO2.PRFO2,Sophos,G1,OracleCallsCounter})
    (D <: SSEDistROM{H2,H1,F,SP_Red,RKF,PRFO1.PRFO1,PRFO2.PRFO2,Sophos,G1,OracleCallsCounter}) &m:
    Pr[SSEExpROM(Sophos(F, H1, H2), G1(H1, H2), OracleCallsCounter(D)).main() @ &m : res] = Pr[PRFExp(F, RKF, SP_Red(H1, H2, OracleCallsCounter(D))).main() @ &m : res].
  proof.
    byequiv (_: ={glob D, glob F, glob CTP, glob H1, glob H2, glob RKF, glob OracleCallsCounter} ==> ={res}) => //.
    proc.
    seq 1 1: (={b, glob D, glob F, glob CTP, glob H1, glob H2, glob RKF, glob OracleCallsCounter}).
      rnd; skip; trivial.
    inline*.
    seq 1 1: (={b, real, glob D, glob F, glob CTP, glob H1, glob H2, glob RKF, glob OracleCallsCounter}).
      wp; skip; trivial.
    if => //.
      (* Real *)
      wp.
      seq 10 10: (={b, real, glob SophosServer, glob D, glob F, glob CTP, glob H1, glob H2, glob OracleCallsCounter}
                /\ ( SophosClient.k,  SophosClient.sk,  SophosClient.ws){1}
                 = (  PRFO1.PRFO1.k, SP_Red.Client.sk, SP_Red.Client.ws){2}
                /\ real{1}).
        wp; rnd; call (_: true) => //; skip; progress.
      call (_: ={glob SophosServer, glob F, glob CTP, glob H1, glob H2, glob OracleCallsCounter}
                /\ ( SophosClient.k,  SophosClient.sk,  SophosClient.ws){1}
                 = (  PRFO1.PRFO1.k, SP_Red.Client.sk, SP_Red.Client.ws){2}) => //=;
        first 3 by proc; inline*; sim.
      (* Ideal *)
      seq 11 11: (={b, real, glob D, glob F, glob CTP, glob H1, glob H2, glob RKF, glob OracleCallsCounter}
                /\ ( Game1.Client.k,  Game1.Client.sk,  Game1.Client.ws,  Game1.Server.pk,  Game1.Server.edb){1}
                 = (  PRFO2.PRFO2.k, SP_Red.Client.sk, SP_Red.Client.ws,  SophosServer.pk,  SophosServer.edb){2}
                /\ !real{1}).
        wp; rnd; wp; rnd; skip; progress.
      wp; call (_: ={glob F, glob CTP, glob H1, glob H2, glob RKF, glob OracleCallsCounter}
                /\ ( Game1.Client.k,  Game1.Client.sk,  Game1.Client.ws,  Game1.Server.pk,  Game1.Server.edb){1}
                 = (  PRFO2.PRFO2.k, SP_Red.Client.sk, SP_Red.Client.ws,  SophosServer.pk,  SophosServer.edb){2}) => //=;
        first 3 by proc; inline*; sim.
  qed.

  (*
   * === Part2 ===
   * Indistinguishable game using H1 random oracle
   *)
  clone SophosImplementation as Game2
  rename "SophosClient" as "Client"
  rename "SophosServer" as "Server".

  module G2(H2: HashFunction2) = SSEProtocol(Game2.Client(RKF, HashRO1, H2), Game2.Server(HashRO1, H2)).

  lemma G2_setup_ll (H2<: HashFunction2):
    is_lossless dcoins =>
    islossless G2(H2).setup.
  proof.
    move : dkey_ll => _ dcoins_ll.
    proc; inline *.
    wp; rnd; wp; rnd; skip; progress.
  qed.

  lemma G2_update_ll (H2<: HashFunction2):
    islossless H2.hash =>
    islossless G2(H2).update.
  proof.
    move : dmapquery_ll dut_ll dstoken_ll cdistr_ful => dmq_ll _ _ [cd_ll cd_fun] h2_ll.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * swap 3 -2; if => //.
        - wp; call h2_ll; wp; rnd; wp; rnd (predT); wp; rnd; skip; progress.
          rewrite /csample /=.
          have ->//: (fun (_ : stoken) => weight dmq = 1%r && forall (v : mapquery), v \in dmq => predT v <=> mu dut (fun (_ : utoken) => true) = 1%r) = predT.
            rewrite fun_ext /= => x.
            rewrite dmq_ll /predT eq_iff //.
        - wp; call h2_ll; wp; rnd; wp; rnd (predT); wp; skip; progress.
      * sp; if => //.
        - wp; call h2_ll; wp; rnd; wp; rnd; skip; progress.
          rewrite /csample /=.
          have ->//: (fun (_ : stoken) => mu dut (fun (_ : utoken) => true) = 1%r) = predT.
            rewrite fun_ext /= => x.
            rewrite /predT eq_iff //.
        - wp; call h2_ll; wp; rnd; wp; skip; progress.
    + wp; skip; progress.
  qed.

  lemma G2_query_ll (H2<: HashFunction2):
    islossless H2.hash =>
    islossless G2(H2).query.
  proof.
    move : dmapquery_ll dstoken_ll => _ _ h2_ll.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i <= c + 1) (c + 1 - i) => //=; progress.
          wp; call h2_ll; wp; rnd; wp; skip; progress; smt.
        wp; skip; progress.
    + sp; if => //.
      * rcondf 6; progress; first by wp; rnd; skip; progress.
        case (0 <= (oget Game2.Client.ws.[q0]).`2).
        - wp => /=; while (0 <= i <= c + 1) (c + 1 - i) => //=; progress.
            wp; call h2_ll; wp; rnd; wp; skip; progress; smt.
          wp; rnd (predT); skip; progress => //.
          + rewrite oget_some get_set_sameE oget_some /=; smt.
          + smt.
        - rcondf 9; progress; first by wp; rnd; skip; progress.
          wp; rnd; progress.
      * sp; if => //; first by wp; skip; progress.
        case (0 <= (oget Game2.Client.ws.[q0]).`2).
        - wp => /=; while (0 <= i <= c + 1) (c + 1 - i) => //=; progress.
            wp; call h2_ll; wp; rnd; wp; skip; progress; smt.
          wp; skip; progress => //.
          + rewrite oget_some /=; smt.
          + smt.
        - rcondf 4; progress; first by wp; skip; progress.
          wp; progress.
  qed.

  lemma G2_o_ll (H2<: HashFunction2):
    islossless H2.hash =>
    islossless G2(H2).o.
  proof.
    move : dut_ll => _ h2_ll.
    proc; inline*.
    sp; if => //; first by wp; rnd; wp; skip; progress; rewrite /csample //.
    sp; if => //; first by wp; call h2_ll; skip; progress.
  qed.

  module SH1_Red(H2: HashFunction2, D: SSEDistROM, H1: OracleAccess1) (*: HDist *) = {
    var n: int (* bound parameter *)

    module Client: SSEClient = {
      var k: key
      var sk: tau
      var ws: state

      proc setup(): setupserver = {
        var pk;

        k <@ RKF.keygen();
        (pk, sk) <@ CTP.index();
        ws <- empty;

        return pk;
      }

      proc update(o: operation, q: query, i: index): (utoken * index) option = {
        var kw, s, c, sc, ut, idx, ti;

        if (o = ADD) {
          kw <@ RKF.f(k, q); (* Random function *)
          if (!dom ws q) {
            s <$ dstoken;
            c <- 0;
          } else {
            sc <- oget ws.[q];
            s <@ CTP.backward(sk, fst sc);
            c <- snd sc + 1;
          }
          ws.[q] <- (s, c);
          ut <@ H1.o(kw, s); (* Oracle access *)
          idx <@ H2.hash(kw, s);
          idx <- i +^ idx;
          ti <- Some(ut, idx);
        } else {
          ti <- None;
        }

        return ti;
      }

      proc query(q: query): (mapquery * stoken * int) option = {
        var kw, sc;
        var r: (mapquery * stoken * int) option;

        if (!dom ws q) {
          r <- None;
        } else {
          kw <@ RKF.f(k, q); (* Random function *)
          sc <- oget ws.[q];
          r <- Some (kw, fst sc, snd sc);
        }

        return r;
      }

      proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
        var h1, h2, ho;

        ho <- None;
        if     (i = HASH1) {
          h1 <@ H1.o(argv);
          ho <- Some(Some(h1), None);
        } elif (i = HASH2) {
          h2 <@ H2.hash(argv);
          ho <- Some(None, Some(h2));
        }

        return ho;
      }
    }

    module Server: SSEServer = {
      var edb: encryptedstorage
      var pk: alpha

      proc setup(s: setupserver): unit = {
        pk <- s;
        edb <- empty;
      }

      proc update(o: operation, t: utoken, i: index): unit = {
        if (o = ADD) {
          edb.[t] <- i;
        }
      }

      proc query(kw: mapquery, t: stoken, c: int): index list = {
        var i, ut, ind;
        var r: index list;

        r <- [];
        i <- 0;
        while (i <= c) {
          (* We expect to have "mem (dom edb) ut" always true for all legitimate queries *)
          ut <@ H1.o(kw, t); (* Oracle access *)
          ind <@ H2.hash(kw, t);
          ind <- (oget edb.[ut]) +^ ind;
          r <- ind :: r;
          t <@ CTP.forward(pk, t);
          i <- i + 1;
        }

        return r;
      }
    }

    module Scheme = SSEProtocol(Client, Server)

    proc distinguish(): bool = {
      var g;

      Scheme.setup();
      g <@ D(Scheme).distinguish();

      return g;
    }
  }.

  lemma G1_G2_reduction_to_hashexp1
    (H1<:    HashFunction1{SH1_Red,RKF,RO1,G1,G2,OracleCallsCounter})
    (H2<: HashFunction2{H1,SH1_Red,RKF,RO1,G1,G2,OracleCallsCounter})
    (D <: SSEDistROM{H2,H1,SH1_Red,RKF,RO1,G1,G2,OracleCallsCounter}) &m:
    Pr[SSEExpROM(G1(H1, H2), G2(H2), OracleCallsCounter(D)).main() @ &m : res] = Pr[HashExp1(H1, HashRO1, SH1_Red(H2, OracleCallsCounter(D))).main() @ &m : res].
  proof.
    byequiv (_: ={glob D, glob CTP, glob H1, glob H2, glob RKF, glob RO1, glob OracleCallsCounter} ==> ={res}) => //.
    proc.
    seq 1 1: (={b, glob D, glob CTP, glob H1, glob H2, glob RKF, glob RO1, glob OracleCallsCounter}).
      rnd; skip; trivial.
    inline*.
    seq 1 1: (={b, real, glob D, glob CTP, glob H1, glob H2, glob RKF, glob RO1, glob OracleCallsCounter}).
      wp; skip; trivial.
    case (real{1}).
      (* Real *)
      rcondt{1} 1 => //.
      rcondt{2} 1 => //.
      wp.
      seq 11 11: (={b, real, glob D, glob CTP, glob H1, glob H2, glob RKF, glob OracleCallsCounter}
                /\ (   Game1.Client.k,   Game1.Client.sk,   Game1.Client.ws,   Game1.Server.pk,   Game1.Server.edb){1}
                 = ( SH1_Red.Client.k, SH1_Red.Client.sk, SH1_Red.Client.ws, SH1_Red.Server.pk, SH1_Red.Server.edb){2}
                /\ real{1}).
        wp; rnd; wp; rnd; skip; progress.
      sp; call (_: ={glob CTP, glob H1, glob H2, glob RKF, glob OracleCallsCounter}
                /\ (   Game1.Client.k,   Game1.Client.sk,   Game1.Client.ws,   Game1.Server.pk,   Game1.Server.edb){1}
                 = ( SH1_Red.Client.k, SH1_Red.Client.sk, SH1_Red.Client.ws, SH1_Red.Server.pk, SH1_Red.Server.edb){2}) => //=.
      + (* UPDATE *)
        proc; sim; inline *.
        wp; sp; if => //.
        wp; sp; if => //=; last by wp; skip; progress.
        seq 4 4: (={kw, i1, q1, o0, glob CTP, glob H1, glob H2, glob RKF, glob OracleCallsCounter}
                /\ (   Game1.Client.k,   Game1.Client.sk,   Game1.Client.ws,   Game1.Server.pk,   Game1.Server.edb){1}
                 = ( SH1_Red.Client.k, SH1_Red.Client.sk, SH1_Red.Client.ws, SH1_Red.Server.pk, SH1_Red.Server.edb){2}).
          sim.
        wp; sp.
        call (_: true) => //; wp; sp.
        call (_: true) => //; wp; sp.
        if => //; first by wp; rnd; skip; progress.
        sp; wp; skip; progress.
      + (* SEARCH *)
        proc; inline *.
        wp; sp; if => //.
        wp; sp; if => //.
        - rcondt{1} 3; progress; first by wp; skip; progress.
          rcondt{2} 3; progress; first by wp; skip; progress.
          wp; skip; progress.
        - seq 4 4: (={kw, q1, glob CTP, glob H1, glob H2, glob RKF, glob OracleCallsCounter}
                /\ (   Game1.Client.k,   Game1.Client.sk,   Game1.Client.ws,   Game1.Server.pk,   Game1.Server.edb){1}
                 = ( SH1_Red.Client.k, SH1_Red.Client.sk, SH1_Red.Client.ws, SH1_Red.Server.pk, SH1_Red.Server.edb){2}).
            wp; sp; if => //; first by rnd; skip; progress; smt.
          rcondf{1} 4; progress; first by wp; skip; progress.
          rcondf{2} 4; progress; first by wp; skip; progress.
        wp; while (={kw0, t, c, i, qo, r1, glob CTP, glob H1, glob H2, glob RKF, glob OracleCallsCounter}
                /\ (   Game1.Client.k,   Game1.Client.sk,   Game1.Client.ws,   Game1.Server.pk,   Game1.Server.edb){1}
                 = ( SH1_Red.Client.k, SH1_Red.Client.sk, SH1_Red.Client.ws, SH1_Red.Server.pk, SH1_Red.Server.edb){2}).
          wp; call (_: true) => //; wp; call (_: true) => //; wp; skip; progress.
        wp; skip; progress.
      + (* o *)
        proc; inline*; sim.
      (* Ideal *)
      rcondf{1} 1 => //.
      rcondf{2} 1 => //.
      wp.
      seq 11 11: (={b, real, glob D, glob CTP, glob H1, glob H2, glob RKF, glob RO1, glob OracleCallsCounter}
                /\ (   Game2.Client.k,   Game2.Client.sk,   Game2.Client.ws,   Game2.Server.pk,   Game2.Server.edb){1}
                 = ( SH1_Red.Client.k, SH1_Red.Client.sk, SH1_Red.Client.ws, SH1_Red.Server.pk, SH1_Red.Server.edb){2}
                /\ !real{1}).
        wp; rnd; wp; rnd; skip; progress.
      sp; call (_: ={glob CTP, glob H1, glob H2, glob RKF, glob RO1, glob OracleCallsCounter}
                /\ (   Game2.Client.k,   Game2.Client.sk,   Game2.Client.ws,   Game2.Server.pk,   Game2.Server.edb){1}
                 = ( SH1_Red.Client.k, SH1_Red.Client.sk, SH1_Red.Client.ws, SH1_Red.Server.pk, SH1_Red.Server.edb){2}) => //=.
      + (* UPDATE *)
        proc; inline *; sim.
      + (* SEARCH *)
        proc; inline *; sim.
      + (* o *)
        proc; inline*; sim.
  qed.

  (*
   * === Part3 ===
   * Indistinguishable game using H2 random oracle
   *)
  clone SophosImplementation as Game3
  rename "SophosClient" as "Client"
  rename "SophosServer" as "Server".

  module G3 = SSEProtocol(Game3.Client(RKF, HashRO1, HashRO2), Game3.Server(HashRO1, HashRO2)).

  lemma G3_setup_ll:
    is_lossless dcoins =>
    islossless G3.setup.
  proof.
    move : dkey_ll => _ dcoins_ll.
    proc; inline *.
    wp; rnd; wp; rnd; skip; progress.
  qed.

  lemma G3_update_ll:
    islossless G3.update.
  proof.
    move : dmapquery_ll di_ll dut_ll dstoken_ll cdistr_ful => dmq_ll di_ll _ _ [cd_ll cd_fun].
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * swap 3 -2; if => //.
        - wp; rnd; wp; rnd; wp; rnd (predT); wp; rnd; skip; progress.
          rewrite /csample /=.
          have ->//: (fun (_ : stoken) => weight dmq = 1%r && forall (v : mapquery), v \in dmq => predT v <=> mu dut (fun (_ : utoken) => mu di (fun (_ : index) => true) = 1%r) = 1%r) = predT.
            rewrite fun_ext /= => x.
            rewrite dmq_ll /predT eq_iff /= => v _.
            rewrite di_ll /= dut_ll //.
        - wp; rnd; wp; rnd; wp; rnd (predT); wp; skip; progress => //.
          rewrite /csample /=.
          have ->//: (fun (_ : utoken) => mu di (fun (_ : index) => true) = 1%r) = predT.
            rewrite fun_ext /= => x.
            rewrite /predT eq_iff //.
      * sp; if => //.
        - wp; rnd; wp; rnd; wp; rnd; skip; progress.
          rewrite /csample /=.
          have ->/=: (fun (_ : utoken) => mu di (fun (_ : index) => true) = 1%r) = predT.
            rewrite fun_ext /= => x.
            rewrite /predT eq_iff //.
          rewrite dut_ll //.
        - wp; rnd; wp; rnd; wp; skip; progress.
          rewrite /csample /=.
          have ->//: (fun (_ : utoken) => mu di (fun (_ : index) => true) = 1%r) = predT.
            rewrite fun_ext /= => x.
            rewrite /predT eq_iff //.
    + wp; skip; progress.
  qed.

  lemma G3_query_ll:
    islossless G3.query.
  proof.
    move : dmapquery_ll dstoken_ll => _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i <= c + 1) (c + 1 - i) => //=; progress.
          wp; rnd; wp; rnd; wp; skip; progress; smt.
        wp; skip; progress.
    + sp; if => //.
      * rcondf 6; progress; first by wp; rnd; skip; progress.
        case (0 <= (oget Game3.Client.ws.[q0]).`2).
        - wp => /=; while (0 <= i <= c + 1) (c + 1 - i) => //=; progress.
            wp; rnd; wp; rnd; wp; skip; progress; smt.
          wp; rnd (predT); skip; progress => //.
          + rewrite oget_some get_set_sameE oget_some /=; smt.
          + smt.
        - rcondf 9; progress; first by wp; rnd; skip; progress.
          wp; rnd; progress.
      * sp; if => //; first by wp; skip; progress.
        case (0 <= (oget Game3.Client.ws.[q0]).`2).
        - wp => /=; while (0 <= i <= c + 1) (c + 1 - i) => //=; progress.
            wp; rnd; wp; rnd; wp; skip; progress; smt.
          wp; skip; progress => //.
          + rewrite oget_some /=; smt.
          + smt.
        - rcondf 4; progress; first by wp; skip; progress.
          wp; progress.
  qed.

  lemma G3_o_ll:
    islossless G3.o.
  proof.
    move : di_ll dut_ll => _ _.
    proc; inline*.
    sp; if => //; first by wp; rnd; wp; skip; progress; rewrite /csample //.
    sp; if => //; first by wp; rnd; wp; skip; progress; rewrite /csample //.
  qed.

  module SH2_Red(D: SSEDistROM, H2: OracleAccess2) (*: HDist *) = {

    module Client: SSEClient = {
      var k: key
      var sk: tau
      var ws: state

      proc setup(): setupserver = {
        var pk;

        k <@ RKF.keygen();
        (pk, sk) <@ CTP.index();
        ws <- empty;

        return pk;
      }

      proc update(o: operation, q: query, i: index): (utoken * index) option = {
        var kw, s, c, sc, ut, idx, ti;

        if (o = ADD) {
          kw <@ RKF.f(k, q); (* Random function *)
          if (!dom ws q) {
            s <$ dstoken;
            c <- 0;
          } else {
            sc <- oget ws.[q];
            s <@ CTP.backward(sk, fst sc);
            c <- snd sc + 1;
          }
          ws.[q] <- (s, c);
          ut <@ HashRO1.hash(kw, s); (* Random function *)
          idx <@ H2.o(kw, s); (* Oracle access *)
          idx <- i +^ idx;
          ti <- Some(ut, idx);
        } else {
          ti <- None;
        }

        return ti;
      }

      proc query(q: query): (mapquery * stoken * int) option = {
        var kw, sc;
        var r: (mapquery * stoken * int) option;

        if (!dom ws q) {
          r <- None;
        } else {
          kw <@ RKF.f(k, q); (* Random function *)
          sc <- oget ws.[q];
          r <- Some (kw, fst sc, snd sc);
        }

        return r;
      }

      proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
        var h1, h2, ho;

        ho <- None;
        if     (i = HASH1) {
          h1 <@ HashRO1.hash(argv);
          ho <- Some(Some(h1), None);
        } elif (i = HASH2) {
          h2 <@ H2.o(argv);
          ho <- Some(None, Some(h2));
        }

        return ho;
      }
    }

    module Server: SSEServer = {
      var edb: encryptedstorage
      var pk: alpha

      proc setup(s: setupserver): unit = {
        pk <- s;
        edb <- empty;
      }

      proc update(o: operation, t: utoken, i: index): unit = {
        if (o = ADD) {
          edb.[t] <- i;
        }
      }

      proc query(kw: mapquery, t: stoken, c: int): index list = {
        var i, ut, ind;
        var r: index list;

        r <- [];
        i <- 0;
        while (i <= c) {
          (* We expect to have "mem (dom edb) ut" always true for all legitimate queries *)
          ut <@ HashRO1.hash(kw, t); (* Random function *)
          ind <@ H2.o(kw, t); (* Oracle access *)
          ind <- (oget edb.[ut]) +^ ind;
          r <- ind :: r;
          t <@ CTP.forward(pk, t);
          i <- i + 1;
        }

        return r;
      }
    }

    proc setup(): setupserver = {
      var ss;

      ss <@ Client.setup();
      Server.setup(ss);

      return ss;
    }

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var t, idx, ti;

      ti <@ Client.update(o, q, i);
      if (ti <> None) {
        (t, idx) <- oget ti;
        Server.update(o, t, idx);
      }

      return ti;
    }

    proc query(q: query): (mapquery * stoken * int) option * index list = {
      var qo, rl;

      qo <@ Client.query(q);
      if (qo = None) {
        rl <- [];
      } else {
        rl <@ Server.query(oget qo);
      }

      return (qo, rl);
    }

    module Scheme = SSEProtocol(Client, Server)

    proc distinguish(): bool = {
      var g;

      Scheme.setup();
      g <@ D(Scheme).distinguish();

      return g;
    }
  }.

  lemma G2_G3_reduction_to_hashexp2
    (H2<: HashFunction2{SH2_Red,RKF,RO2,G2,G3,OracleCallsCounter})
    (D <: SSEDistROM{H2,SH2_Red,RKF,RO2,G2,G3,OracleCallsCounter}) &m:
    Pr[SSEExpROM(G2(H2), G3, OracleCallsCounter(D)).main() @ &m : res] = Pr[HashExp2(H2, HashRO2, SH2_Red(OracleCallsCounter(D))).main() @ &m : res].
  proof.
    byequiv (_: ={glob D, glob CTP, glob H2, glob RKF, glob HashRO1, glob RO2, glob OracleCallsCounter} ==> ={res}) => //.
    proc.
    seq 1 1: (={b, glob D, glob CTP, glob HashRO1, glob H2, glob RKF, glob RO2, glob OracleCallsCounter}).
      rnd; skip; trivial.
    inline*.
    seq 1 1: (={b, real, glob D, glob CTP, glob HashRO1, glob H2, glob RKF, glob RO2, glob OracleCallsCounter}).
      wp; skip; trivial.
    case (real{1}).
      (* Real *)
      rcondt{1} 1 => //.
      rcondt{2} 1 => //.
      wp.
      seq 11 11: (={b, real, glob D, glob CTP, glob HashRO1, glob H2, glob RKF, glob OracleCallsCounter}
                /\ (   Game2.Client.k,   Game2.Client.sk,   Game2.Client.ws,   Game2.Server.pk,   Game2.Server.edb){1}
                 = ( SH2_Red.Client.k, SH2_Red.Client.sk, SH2_Red.Client.ws, SH2_Red.Server.pk, SH2_Red.Server.edb){2}
                /\ real{1}).
        wp; rnd; wp; rnd; skip; progress.
      sp; call (_: ={glob CTP, glob HashRO1, glob H2, glob RKF, glob OracleCallsCounter}
                /\ (   Game2.Client.k,   Game2.Client.sk,   Game2.Client.ws,   Game2.Server.pk,   Game2.Server.edb){1}
                 = ( SH2_Red.Client.k, SH2_Red.Client.sk, SH2_Red.Client.ws, SH2_Red.Server.pk, SH2_Red.Server.edb){2}) => //=.
      + (* UPDATE *)
        proc; sim; inline *.
        wp; sp; if => //=.
        wp; sp; if => //=; last by wp; skip; progress.
        seq 4 4: (={kw, i1, q1, o0, glob CTP, glob HashRO1, glob H2, glob RKF, glob OracleCallsCounter}
                /\ (   Game2.Client.k,   Game2.Client.sk,   Game2.Client.ws,   Game2.Server.pk,   Game2.Server.edb){1}
                 = ( SH2_Red.Client.k, SH2_Red.Client.sk, SH2_Red.Client.ws, SH2_Red.Server.pk, SH2_Red.Server.edb){2}).
          sim.
        wp; call (_: true) => //; wp; rnd; wp.
        if => //; first by wp; rnd; skip; progress.
        sp; wp => //.
      + (* SEARCH *)
        proc; inline *.
        wp; sp; if => //.
        wp; sp; if => //.
        - rcondt{1} 3; progress; first by wp; skip; progress.
          rcondt{2} 3; progress; first by wp; skip; progress.
          wp; skip; progress.
        - seq 4 4: (={kw, q1, glob CTP, glob HashRO1, glob H2, glob RKF, glob OracleCallsCounter}
                /\ (   Game2.Client.k,   Game2.Client.sk,   Game2.Client.ws,   Game2.Server.pk,   Game2.Server.edb){1}
                 = ( SH2_Red.Client.k, SH2_Red.Client.sk, SH2_Red.Client.ws, SH2_Red.Server.pk, SH2_Red.Server.edb){2}).
            wp; sp; if => //; first by rnd; skip; progress; smt.
          rcondf{1} 4; progress; first by wp; skip; progress.
          rcondf{2} 4; progress; first by wp; skip; progress.
        wp; while (={kw0, t, c, i, qo, r1, glob CTP, glob HashRO1, glob H2, glob RKF, glob OracleCallsCounter}
                /\ (   Game2.Client.k,   Game2.Client.sk,   Game2.Client.ws,   Game2.Server.pk,   Game2.Server.edb){1}
                 = ( SH2_Red.Client.k, SH2_Red.Client.sk, SH2_Red.Client.ws, SH2_Red.Server.pk, SH2_Red.Server.edb){2}).
          wp; call (_: true) => //; wp; rnd; wp; skip; progress.
        wp; skip; progress.
      + (* o *)
        proc; inline*; sim.
      (* Ideal *)
      rcondf{1} 1 => //.
      rcondf{2} 1 => //.
      wp.
      seq 11 11: (={b, real, glob D, glob CTP, glob HashRO1, glob H2, glob RKF, glob RO2, glob OracleCallsCounter}
                /\ (   Game3.Client.k,   Game3.Client.sk,   Game3.Client.ws,   Game3.Server.pk,   Game3.Server.edb){1}
                 = ( SH2_Red.Client.k, SH2_Red.Client.sk, SH2_Red.Client.ws, SH2_Red.Server.pk, SH2_Red.Server.edb){2}
                /\ !real{1}).
        wp; rnd; wp; rnd; skip; progress.
      sp; call (_: ={glob CTP, glob HashRO1, glob H2, glob RKF, glob RO2, glob OracleCallsCounter}
                /\ (   Game3.Client.k,   Game3.Client.sk,   Game3.Client.ws,   Game3.Server.pk,   Game3.Server.edb){1}
                 = ( SH2_Red.Client.k, SH2_Red.Client.sk, SH2_Red.Client.ws, SH2_Red.Server.pk, SH2_Red.Server.edb){2}) => //=.
      + (* UPDATE *)
        proc; inline *; sim.
      + (* SEARCH *)
        proc; inline *; sim.
      + (* o *)
        proc; inline*; sim.
  qed.

  (*
   * === Part4 ===
   * Getting rid of RKF and using just a Random Function.
   *)
  module G4_Client(H1: HashFunction1, H2: HashFunction2): SSEClient = {
    var sk: tau
    var ws: state

    proc setup(): setupserver = {
      var pk;

      (pk, sk) <@ CTP.index();
      RF.init();
      ws <- empty;

      return pk;
    }


    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var kw, s, c, sc, ut, idx, ti;

      if (o = ADD) {
        kw <@ RF.f(q);
        if (!dom ws q) {
          s <$ dstoken;
          c <- 0;
        } else {
          sc <- oget ws.[q];
          s <@ CTP.backward(sk, fst sc);
          c <- snd sc + 1;
        }
        ws.[q] <- (s, c);
        ut <@ H1.hash(kw, s);
        idx <@ H2.hash(kw, s);
        idx <- i +^ idx;
        ti <- Some(ut, idx);
      } else {
        ti <- None;
      }

      return ti;
    }

    proc query(q: query): (mapquery * stoken * int) option = {
      var kw, sc;
      var r: (mapquery * stoken * int) option;

      if (!dom ws q) {
        r <- None;
      } else {
        kw <@ RF.f(q);
        sc <- oget ws.[q];
        r <- Some (kw, fst sc, snd sc);
      }

      return r;
    }

    proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
      var h1, h2, h;

      h <- None;
      if     (i = HASH1) {
        h1 <@ H1.hash(argv);
        h <- Some(Some(h1), None);
      } elif (i = HASH2) {
        h2 <@ H2.hash(argv);
        h <- Some(None, Some(h2));
      }

      return h;
    }
  }.

  module G4_Server(H1: HashFunction1, H2: HashFunction2): SSEServer = {
    var edb: encryptedstorage
    var pk: alpha

    proc setup(s: setupserver): unit = {
      pk <- s;
      edb <- empty;
    }

    proc update(o: operation, t: utoken, i: index): unit = {
     if (o = ADD) {
       edb.[t] <- i;
      }
    }

    proc query(kw: mapquery, t: stoken, c: int): index list = {
      var i, ut, ind;
      var r: index list;

      r <- [];
      i <- 0;
      while (i <= c) {
        (* We expect to have "mem (dom edb) ut" always true for all legitimate queries *)
        ut <@ H1.hash(kw, t);
        ind <@ H2.hash(kw, t);
        ind <- (oget edb.[ut]) +^ ind;
        r <- ind :: r;
        t <@ CTP.forward(pk, t);
        i <- i + 1;
      }

      return r;
    }
  }.

  module G4 = SSEProtocol(G4_Client(HashRO1, HashRO2), G4_Server(HashRO1, HashRO2)).

  lemma G4_setup_ll:
    is_lossless dcoins =>
    islossless G4.setup.
  proof.
    move : dkey_ll => _ dcoins_ll.
    proc; inline *.
    wp; rnd; skip; progress.
  qed.

  lemma G4_update_ll:
    islossless G4.update.
  proof.
    move : dmapquery_ll di_ll dut_ll dstoken_ll cdistr_ful => dmq_ll di_ll _ _ [cd_ll cd_fun].
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * swap 3 -2; if => //.
        - wp; rnd; wp; rnd; wp; rnd (predT); wp; rnd; skip; progress.
          rewrite /csample /=.
          have ->//: (fun (_ : stoken) => weight dmq = 1%r && forall (v : mapquery), v \in dmq => predT v <=> mu dut (fun (_ : utoken) => mu di (fun (_ : index) => true) = 1%r) = 1%r) = predT.
            rewrite fun_ext /= => x.
            rewrite dmq_ll /predT eq_iff /= => v _.
            rewrite di_ll /= dut_ll //.
        - wp; rnd; wp; rnd; wp; rnd (predT); wp; skip; progress => //.
          rewrite /csample /=.
          have ->//: (fun (_ : utoken) => mu di (fun (_ : index) => true) = 1%r) = predT.
            rewrite fun_ext /= => x.
            rewrite /predT eq_iff //.
      * sp; if => //.
        - wp; rnd; wp; rnd; wp; rnd; skip; progress.
          rewrite /csample /=.
          have ->/=: (fun (_ : utoken) => mu di (fun (_ : index) => true) = 1%r) = predT.
            rewrite fun_ext /= => x.
            rewrite /predT eq_iff //.
          rewrite dut_ll //.
        - wp; rnd; wp; rnd; wp; skip; progress.
          rewrite /csample /=.
          have ->//: (fun (_ : utoken) => mu di (fun (_ : index) => true) = 1%r) = predT.
            rewrite fun_ext /= => x.
            rewrite /predT eq_iff //.
    + wp; skip; progress.
  qed.

  lemma G4_query_ll:
    islossless G4.query.
  proof.
    move : dmapquery_ll dstoken_ll => _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i <= c + 1) (c + 1 - i) => //=; progress.
          wp; rnd; wp; rnd; wp; skip; progress; smt.
        wp; skip; progress.
    + sp; if => //.
      * rcondf 6; progress; first by wp; rnd; skip; progress.
        case (0 <= (oget G4_Client.ws.[q0]).`2).
        - wp => /=; while (0 <= i <= c + 1) (c + 1 - i) => //=; progress.
            wp; rnd; wp; rnd; wp; skip; progress; smt.
          wp; rnd (predT); skip; progress => //.
          + rewrite oget_some get_set_sameE oget_some /=; smt.
          + smt.
        - rcondf 9; progress; first by wp; rnd; skip; progress.
          wp; rnd; progress.
      * sp; if => //; first by wp; skip; progress.
        case (0 <= (oget G4_Client.ws.[q0]).`2).
        - wp => /=; while (0 <= i <= c + 1) (c + 1 - i) => //=; progress.
            wp; rnd; wp; rnd; wp; skip; progress; smt.
          wp; skip; progress => //.
          + rewrite oget_some /=; smt.
          + smt.
        - rcondf 4; progress; first by wp; skip; progress.
          wp; progress.
  qed.

  lemma G4_o_ll:
    islossless G4.o.
  proof.
    move : di_ll dut_ll => _ _.
    proc; inline*.
    sp; if => //; first by wp; rnd; wp; skip; progress; rewrite /csample //.
    sp; if => //; first by wp; rnd; wp; skip; progress; rewrite /csample //.
  qed.

  lemma G3_G4_indistinguishable
    (D <: SSEDistROM{RO1,RO2,RKF,G3,G4,OracleCallsCounter}) &m:
    RKF.m{m} = empty =>
    Pr[SSEExpROM(G3, G4, OracleCallsCounter(D)).game(true) @ &m: res] = Pr[SSEExpROM(G3, G4, OracleCallsCounter(D)).game(false) @ &m: res].
  proof.
    move => empty_RFK.
    byequiv => //; proc.
    rcondt{1} 1 => //.
    rcondf{2} 1 => //.
    inline *.
    seq 11 10: (={glob D, glob CTP, glob RO1, glob RO2, glob OracleCallsCounter}
              /\ (glob Game3.Server, Game3.Client.sk, Game3.Client.ws){1}
               = (   glob G4_Server,    G4_Client.sk,    G4_Client.ws){2}
              /\ forall x, RF.m{2}.[x] = RKF.m{1}.[(Game3.Client.k{1}, x)]).
      inline *; wp; rnd; wp; rnd{1}; skip; progress.
      apply dkey_ll.
      rewrite empty_RFK 2!emptyE //.
    wp; call (_: ={glob CTP, glob RO1, glob RO2, glob OracleCallsCounter}
              /\ (glob Game3.Server, Game3.Client.sk, Game3.Client.ws){1}
               = (   glob G4_Server,    G4_Client.sk,    G4_Client.ws){2}
              /\ forall x, RF.m{2}.[x] = RKF.m{1}.[(Game3.Client.k{1}, x)]) => //.
    + (* UPDATE *)
      proc*; inline*.
      sp; wp; if => //.
      seq 6 6: (={o2, o1, q2, i2, glob CTP, glob RO1, glob RO2, glob OracleCallsCounter}
              /\ (glob Game3.Server, Game3.Client.sk, Game3.Client.ws){1}
               = (   glob G4_Server,    G4_Client.sk,    G4_Client.ws){2}
              /\ forall x, RF.m{2}.[x] = RKF.m{1}.[(Game3.Client.k{1}, x)]).
        wp; skip; trivial.
      if => //; last by wp; skip; progress.
      seq 4 3: (={o2, o1, q2, i2, kw, glob CTP, glob RO1, glob RO2, glob OracleCallsCounter}
              /\ (glob Game3.Server, Game3.Client.sk, Game3.Client.ws){1}
               = (   glob G4_Server,    G4_Client.sk,    G4_Client.ws){2}
              /\ forall x, RF.m{2}.[x] = RKF.m{1}.[(Game3.Client.k{1}, x)]).
        sp; if; first by progress; smt.
        + wp; rnd; skip; progress; smt.
        + wp; skip; progress; smt.
      seq 17 17: (={o1, o1, q2, i2, kw, ti, glob CTP, glob RO1, glob RO2, glob OracleCallsCounter}
              /\ (glob Game3.Server, Game3.Client.sk, Game3.Client.ws){1}
               = (   glob G4_Server,    G4_Client.sk,    G4_Client.ws){2}
              /\ forall x, RF.m{2}.[x] = RKF.m{1}.[(Game3.Client.k{1}, x)]).
        wp; if; first by progress; smt.
        + rnd; wp; rnd; wp; rnd; skip; progress; smt.
        + rnd; wp; rnd; wp;  skip; progress; smt.
      if => //; last by wp; progress.
      wp; skip; progress; smt.
    + (* SEARCH *)
      proc*; inline*.
      sp; wp; if => //.
        wp; sp; if => //.
        - rcondt{1} 3; progress; first by wp; skip; progress.
          rcondt{2} 3; progress; first by wp; skip; progress.
          wp; skip; progress.
        - seq 4 3: (={kw, q2, glob CTP, glob RO1, glob RO2, glob OracleCallsCounter}
              /\ (glob Game3.Server, Game3.Client.sk, Game3.Client.ws){1}
               = (   glob G4_Server,    G4_Client.sk,    G4_Client.ws){2}
              /\ forall x, RF.m{2}.[x] = RKF.m{1}.[(Game3.Client.k{1}, x)]).
            wp; sp; if; first by progress; smt.
            * rnd; skip; progress; smt.
            * skip; progress; smt.
          rcondf{1} 4; progress; first by wp; skip; progress.
          rcondf{2} 4; progress; first by wp; skip; progress.
        wp; while (={qo, i, c, kw0, r2, t, glob CTP, glob RO1, glob RO2, glob OracleCallsCounter}
              /\ (glob Game3.Server, Game3.Client.sk, Game3.Client.ws){1}
               = (   glob G4_Server,    G4_Client.sk,    G4_Client.ws){2}
              /\ forall x, RF.m{2}.[x] = RKF.m{1}.[(Game3.Client.k{1}, x)]).
          wp; rnd; wp; rnd; wp; skip; progress; smt.
        wp; skip; progress; smt.
    + (* o *)
      proc*; inline*.
      sp; wp; if => //.
      sp; if => //; first by wp; rnd; wp; skip; progress.
      if => //; first by wp; rnd; wp; skip; progress.
      wp; skip; progress.
  qed.

  (*
   * === Part5 ===
   * Construction of a simulator of both H1 and H2, apart from bad events.
   * We could spot 6 bad events.
   *
   * @see our inconsistency theorem
   *)
  module G5_Client: SSEClient = {
    var sk: tau
    var ws: (query, stoken list) fmap

    var utt: (query * int, utoken) fmap
    var et: (query * int, index) fmap
    var h1t: (mapquery * stoken, utoken) fmap
    var h2t: (mapquery * stoken, index) fmap

    var bad_rf_coll: bool (* collision in the random function *)
    var bad_update_bt: bool (* prediction in backup tables *)
    var bad_update_h1t: bool (* guess in h1t *)
    var bad_update_h2t: bool (* guess in h2t *)
    var bad_h1: bool (* bad event raised by h1 *)
    var bad_h2: bool (* bad event raised by h2 *)

    proc setup(): setupserver = {
      var pk;

      (pk, sk) <@ CTP.index();
      RF.init();
      ws <- empty;
      utt <- empty;
      et <- empty;
      h1t <- empty;
      h2t <- empty;

      bad_rf_coll <- false;
      bad_update_bt <- false;
      bad_update_h1t <- false;
      bad_update_h2t <- false;
      bad_h1 <- false;
      bad_h2 <- false;

      return pk;
    }

    (* Simulating the hash functions *)
    module SimH1: HashFunction1 = {
      proc hash(kw: mapquery, s: stoken): utoken = {
        var c, ls, y, qs, cand_ws, w;

        if (!(dom h1t (kw, s))) {
          (*
           * Additional care when h1t is not synced with utt (i.e. update was not called before it)
           *)
          qs <- fdom (filter (fun (_: query) k => k = kw) RF.m); (* queries mapping to kw *)
          cand_ws <- filter (fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts) ws; (* occurrences in the ws map *)
          if (cand_ws <> empty) { (* occurrence found *)
            bad_h1 <- true;
            w <- last witness (elems (fdom cand_ws)); (* this element always exists, notice that listing cand_ws elements give results that equal up to permutation, so no guarantee to get the same value in maps with cardinality greater than one *)
            ls <- oget cand_ws.[w];
            c <- find ((=) s) ls;
            h1t.[(kw, s)] <- oget utt.[(w, c)];
          } else {
            y <$ dutoken;
            h1t.[(kw, s)] <- y;
          }
        }

        return oget h1t.[(kw, s)];
      }
    }

    module SimH2: HashFunction2 = {
      proc hash(kw: mapquery, s: stoken): index = {
        var c, ls, y, qs, cand_ws, w;

        if (!(dom h2t (kw, s))) {
          (*
           * Additional care when h2t is not synced with et (i.e. update was not called before it)
           *)
          qs <- fdom (filter (fun (_: query) k => k = kw) RF.m); (* queries mapping to kw *)
          cand_ws <- filter (fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts) ws; (* occurrences in the ws map *)
          if (cand_ws <> empty) { (* occurrence found *)
            bad_h2 <- true;
            w <- last witness (elems (fdom cand_ws)); (* this element always exists, notice that listing cand_ws elements give results that equal up to permutation, so no guarantee to get the same value in maps with cardinality greater than one *)
            ls <- oget cand_ws.[w];
            c <- find ((=) s) ls;
            h2t.[(kw, s)] <- oget et.[(w, c)];
          } else {
            y <$ di;
            h2t.[(kw, s)] <- y;
          }
        }

        return oget h2t.[(kw, s)];
      }
    }

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var kw, s, c, sc, idx, ti, qs, cand_ws;

      if (o = ADD) {
        kw <@ RF.f(q);
        if (fmap_collision RF.m) {
          bad_rf_coll <- true;
          ti <- None;
        } else {
          if (!dom ws q) {
            sc <- [];
            s <$ dstoken;
            c <- 0;
          } else {
            sc <- oget ws.[q];
            c <- size sc;
            s <@ CTP.backward(sk, last witness sc);
          }
          ws.[q] <- sc ++ [s];
          if (dom h1t (kw, s)) {
            (* Rare event: We do not expect this value to be called (read guessed) in the past if not for a negligible probability *)
            bad_update_h1t <- true;
            ti <- None;
          } else {
            if (dom h2t (kw, s)) {
              (* Rare event: We do not expect this value to be called (read guessed) in the past if not for a negligible probability *)
              bad_update_h2t <- true;
              ti <- None;
            } else {
              (*
              * Additional care when h1t/h2t is not synced with utt/et (i.e. utt/et already contains what h1t/h2t would contain in the future).
              * This is not a proper bad event: It happens naturally for any duplicates and in the real world is not an issue.
              *)
              qs <- fdom (filter (fun (_: query) k => k = kw) RF.m); (* queries mapping to kw *)
              cand_ws <- filter (fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts) ws; (* occurrences in the ws map *)
              if (cand_ws <> empty) { (* occurrence found *)
                (* This is also unlikely to happen *)
                bad_update_bt <- true;
                ti <- None;
              } else {
                utt.[(q, c)] <$ dutoken;
                idx <$ di;
                et.[(q, c)] <- idx;
                idx <- i +^ idx;
                ti <- Some(oget utt.[(q, c)], idx);
              }
            }
          }
        }
      } else {
        ti <- None;
      }
     
      return ti;
    }

    proc query(q: query): (mapquery * stoken * int) option = {
      var kw, sc, c, i, s;
      var r: (mapquery * stoken * int) option;

      if (!dom ws q) {
        r <- None;
      } else {
        kw <@ RF.f(q);
        if (fmap_collision RF.m) {
          bad_rf_coll <- true;
        }
        sc <- oget ws.[q];
        c <- size sc - 1;
        r <- Some (kw, nth witness sc c, c);

        (* Lazily programming the hash tables *)
        i <- 0;
        while (i < size sc) {
          s <- nth witness sc i;
          h1t.[(kw, s)] <- oget utt.[(q, i)];
          h2t.[(kw, s)] <- oget et.[(q, i)];
          i <- i + 1;
        }
      }

      return r;
    }

    proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
      var h1, h2, h;

      h <- None;
      if     (i = HASH1) {
        h1 <@ SimH1.hash(argv);
        h <- Some(Some(h1), None);
      } elif (i = HASH2) {
        h2 <@ SimH2.hash(argv);
        h <- Some(None, Some(h2));
      }

      return h;
    }
  }.

  module G5 = SSEProtocol(G5_Client, G4_Server(G5_Client.SimH1, G5_Client.SimH2)).

  lemma G5_setup_ll:
    is_lossless dcoins =>
    islossless G5.setup.
  proof.
    move : dkey_ll => _ dcoins_ll.
    proc; inline *.
    wp; rnd; skip; progress.
  qed.

  lemma G5_update_ll:
    islossless G5.update.
  proof.
    move : dmapquery_ll di_ll dut_ll dstoken_ll cdistr_ful => dmq_ll di_ll _ _ [cd_ll cd_fun].
    proc; inline*.
    wp => /=; kill 4.
      if => //; last by wp; skip; progress.
      wp; kill 4.
        case (fmap_collision RF.m).
        + rcondt 1; progress.
          wp; skip; progress.
        + rcondf 1; progress.
          kill 3.
            if => //; first by wp; skip; progress.
            if => //; first by wp; skip; progress.
            sp; if => //; first by wp; skip; progress.
            wp; rnd; rnd; skip; progress.
          if => //.
          * wp; rnd; wp; skip; progress.
          * wp; skip; progress.
      wp => /=; sp; if => //; first by rnd; skip; progress.
    wp; skip; progress.
  qed.

  lemma G5_query_ll:
    islossless G5.query.
  proof.
    move : dmapquery_ll dstoken_ll di_ll dut_ll => _ _ _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //.
            sp; if => //.
            * wp; skip; progress.
            * wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //.
            sp; if => //.
            * wp; skip; progress.
            * wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress => //.
    + sp; if => //.
      * kill 10.
          if => //; first by wp; skip; progress.
          case (0 <= (oget qo).`3).
          - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
            wp => /=; kill 7.
              sp; if => //.
              sp; if => //.
              * wp; skip; progress.
              * wp; rnd; skip; progress.
            wp => /=; kill 3.
              sp; if => //.
              sp; if => //.
              * wp; skip; progress.
              * wp; rnd; skip; progress.
            wp; skip; progress; smt.
          wp; skip; progress; smt.
          - rcondf 4; progress; first by wp; skip; progress.
            wp; skip; progress.
        wp => /=; while (0 <= i <= size sc) (size sc - i) => //=; progress.
          wp; skip; progress; smt.
        wp => /=; rnd predT; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
      * kill 9.
          if => //; first by wp; skip; progress.
          case (0 <= (oget qo).`3).
          - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
            wp => /=; kill 7.
              sp; if => //.
              sp; if => //.
              * wp; skip; progress.
              * wp; rnd; skip; progress.
            wp => /=; kill 3.
              sp; if => //.
              sp; if => //.
              * wp; skip; progress.
              * wp; rnd; skip; progress.
            wp; skip; progress; smt.
          wp; skip; progress; smt.
          - rcondf 4; progress; first by wp; skip; progress.
            wp; skip; progress.
        wp => /=; while (0 <= i <= size sc) (size sc - i) => //=; progress.
          wp; skip; progress; smt.
        wp => /=; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
  qed.

  lemma G5_o_ll:
    islossless G5.o.
  proof.
    move : di_ll dut_ll => _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      - sp; if => //.
        * wp; skip; progress.
        * wp; rnd; skip; progress.
      - wp; skip; progress.
    + sp; if => //.
      - sp; if => //.
        * sp; if => //.
          + wp; skip; progress.
          + wp; rnd; skip; progress.
        * wp; skip; progress.
  qed.

  lemma eq_G4_G5_no_bad_events_update_consistency:
    equiv[G4.update ~ G5.update:
          ={o, q, i}
               (* UPDATE ASSUMPTIONS *)
            /\   (glob RF, glob G4_Server, G4_Client.sk){1}
               = (glob RF, glob G4_Server, G5_Client.sk){2}
            /\ (forall w c, dom G5_Client.utt (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO1.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.utt.[(w, c)]){2}
            /\ (forall w c, dom G5_Client.et (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO2.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.et.[(w, c)]){2}
            /\ (forall w c, !dom G5_Client.utt (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h1t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO1.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall w c, !dom G5_Client.et (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h2t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO2.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall kw s, dom RO1.m{1} (kw, s) => (RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO1.m{1}.[(kw, s)] = G5_Client.utt.[(w, c)])){2}
            /\ (forall kw s, dom RO2.m{1} (kw, s) => (RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO2.m{1}.[(kw, s)] = G5_Client.et.[(w, c)])){2}
            /\ (forall w, dom G4_Client.ws{1} w <=> dom G5_Client.ws{2} w)
            /\ (forall w, dom G4_Client.ws{1} w =>
                     G4_Client.ws{1}.[w] = Some (last witness (oget G5_Client.ws.[w]), size (oget G5_Client.ws.[w]) - 1)
                 /\ (forall c, (!0 <= c < size (oget G5_Client.ws.[w])) => !dom G5_Client.utt (w, c) /\ !dom G5_Client.et (w, c))
               ){2}
            /\ (forall w, !dom RF.m w => !dom G5_Client.ws w){2}
            /\ (forall kw, !rng RF.m kw => forall s, RO1.m.[(kw, s)] = G5_Client.h1t{2}.[(kw, s)] /\ RO2.m.[(kw, s)] = G5_Client.h2t{2}.[(kw, s)]){1} (* if neither update or search have been ever called in the past... *)
            /\ (!fmap_collision RF.m){1}
               (* SEARCH ASSUMPTIONS *)
            /\ (forall w, dom G4_Client.ws{1} w => (let sc = oget G5_Client.ws.[w] in
                       0 < size sc
                    /\ !dom G5_Client.utt (w, size sc)
                    /\ !dom G5_Client.et (w, size sc)
                    /\ (forall c, 0 <= c < size sc =>
                             dom G5_Client.utt (w, c)
                          /\ dom G5_Client.et (w, c)
                          /\ RO1.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.utt.[(w, c)]
                          /\ RO2.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.et.[(w, c)]
                       )
                    /\ (forall c, 0 < c < size sc => nth witness sc (c - 1) = forward G4_Server.pk (nth witness sc c))
                 )
               ){2}
               (* O(RACLES) ASSUMPTIONS *)
            /\ (forall kw s, dom G5_Client.h1t (kw, s) => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]){2}
            /\ (forall kw s, dom G5_Client.h2t (kw, s) => RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (forall kw s,
                  let g = fun (_: query) (k: mapquery) => k = kw in
                  let qs = fdom (filter g RF.m) in
                  let f = fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts in
                  filter f G5_Client.ws = empty => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)] /\ RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
          ==> (!G5_Client.bad_rf_coll /\ !G5_Client.bad_update_h1t /\ !G5_Client.bad_update_h2t /\ !G5_Client.bad_update_bt){2} => (={res}
               (* UPDATE ASSUMPTIONS *)
            /\   (glob RF, glob G4_Server, G4_Client.sk){1}
               = (glob RF, glob G4_Server, G5_Client.sk){2}
            /\ (forall w c, dom G5_Client.utt (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO1.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.utt.[(w, c)]){2}
            /\ (forall w c, dom G5_Client.et (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO2.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.et.[(w, c)]){2}
            /\ (forall w c, !dom G5_Client.utt (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h1t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO1.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall w c, !dom G5_Client.et (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h2t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO2.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall kw s, dom RO1.m{1} (kw, s) => (RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO1.m{1}.[(kw, s)] = G5_Client.utt.[(w, c)])){2}
            /\ (forall kw s, dom RO2.m{1} (kw, s) => (RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO2.m{1}.[(kw, s)] = G5_Client.et.[(w, c)])){2}
            /\ (forall w, dom G4_Client.ws{1} w <=> dom G5_Client.ws{2} w)
            /\ (forall w, dom G4_Client.ws{1} w =>
                     G4_Client.ws{1}.[w] = Some (last witness (oget G5_Client.ws.[w]), size (oget G5_Client.ws.[w]) - 1)
                 /\ (forall c, (!0 <= c < size (oget G5_Client.ws.[w])) => !dom G5_Client.utt (w, c) /\ !dom G5_Client.et (w, c))
               ){2}
            /\ (forall w, !dom RF.m w => !dom G5_Client.ws w){2}
            /\ (forall kw, !rng RF.m kw => forall s, RO1.m.[(kw, s)] = G5_Client.h1t{2}.[(kw, s)] /\ RO2.m.[(kw, s)] = G5_Client.h2t{2}.[(kw, s)]){1} (* if neither update or search have been ever called in the past... *)
            /\ (!fmap_collision RF.m){1}
               (* SEARCH ASSUMPTIONS *)
            /\ (forall w, dom G4_Client.ws{1} w => (let sc = oget G5_Client.ws.[w] in
                       0 < size sc
                    /\ !dom G5_Client.utt (w, size sc)
                    /\ !dom G5_Client.et (w, size sc)
                    /\ (forall c, 0 <= c < size sc =>
                             dom G5_Client.utt (w, c)
                          /\ dom G5_Client.et (w, c)
                          /\ RO1.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.utt.[(w, c)]
                          /\ RO2.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.et.[(w, c)]
                       )
                    /\ (forall c, 0 < c < size sc => nth witness sc (c - 1) = forward G4_Server.pk (nth witness sc c))
                 )
               ){2}
               (* O(RACLES) ASSUMPTIONS *)
            /\ (forall kw s, dom G5_Client.h1t (kw, s) => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]){2}
            /\ (forall kw s, dom G5_Client.h2t (kw, s) => RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (forall kw s,
                  let g = fun (_: query) (k: mapquery) => k = kw in
                  let qs = fdom (filter g RF.m) in
                  let f = fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts in
                  filter f G5_Client.ws = empty => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)] /\ RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
      )
    ].
  proof.
    proc.
    inline*; sp; if => //; last by wp; progress.
    sp; if => //; last first.
    + (* Else is easier *)
      rcondf{2} 2; first by progress; first by wp; skip; progress.
      (* no bad events so far *)
      seq 2 2: (={kw, s, c, i0, o, q}
               (* UPDATE ASSUMPTIONS *)
            /\   (glob RF, glob G4_Server, G4_Client.sk){1}
               = (glob RF, glob G4_Server, G5_Client.sk){2}
            /\ (forall w c, dom G5_Client.utt (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO1.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.utt.[(w, c)]){2}
            /\ (forall w c, dom G5_Client.et (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO2.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.et.[(w, c)]){2}
            /\ (forall w c, !dom G5_Client.utt (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h1t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO1.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall w c, !dom G5_Client.et (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h2t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO2.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall kw s, dom RO1.m{1} (kw, s) => (RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO1.m{1}.[(kw, s)] = G5_Client.utt.[(w, c)])){2}
            /\ (forall kw s, dom RO2.m{1} (kw, s) => (RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO2.m{1}.[(kw, s)] = G5_Client.et.[(w, c)])){2}
            /\ (forall w, dom G4_Client.ws{1} w <=> dom G5_Client.ws{2} w)
            /\ (forall w, dom G4_Client.ws{1} w =>
                     G4_Client.ws{1}.[w] = Some (last witness (oget G5_Client.ws.[w]), size (oget G5_Client.ws.[w]) - 1)
                 /\ (forall c, (!0 <= c < size (oget G5_Client.ws.[w])) => !dom G5_Client.utt (w, c) /\ !dom G5_Client.et (w, c))
               ){2}
            /\ (forall w, !dom RF.m w => !dom G5_Client.ws w){2}
            /\ (forall kw, !rng RF.m kw => forall s, RO1.m.[(kw, s)] = G5_Client.h1t{2}.[(kw, s)] /\ RO2.m.[(kw, s)] = G5_Client.h2t{2}.[(kw, s)]){1} (* if neither update or search have been ever called in the past... *)
            /\ (!fmap_collision RF.m){1}
               (* SEARCH ASSUMPTIONS *)
            /\ (forall w, dom G4_Client.ws{1} w => (let sc = oget G5_Client.ws.[w] in
                       0 < size sc
                    /\ !dom G5_Client.utt (w, size sc)
                    /\ !dom G5_Client.et (w, size sc)
                    /\ (forall c, 0 <= c < size sc =>
                             dom G5_Client.utt (w, c)
                          /\ dom G5_Client.et (w, c)
                          /\ RO1.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.utt.[(w, c)]
                          /\ RO2.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.et.[(w, c)]
                       )
                    /\ (forall c, 0 < c < size sc => nth witness sc (c - 1) = forward G4_Server.pk (nth witness sc c))
                 )
               ){2}
               (* O(RACLES) ASSUMPTIONS *)
            /\ (forall kw s, dom G5_Client.h1t (kw, s) => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]){2}
            /\ (forall kw s, dom G5_Client.h2t (kw, s) => RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (forall kw s,
                  let g = fun (_: query) (k: mapquery) => k = kw in
                  let qs = fdom (filter g RF.m) in
                  let f = fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts in
                  filter f G5_Client.ws = empty => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)] /\ RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (q0 = q /\ o = ADD){2}
            /\ (RF.m.[q] = Some kw){2}
            /\ (!dom G5_Client.utt (q, c)){2}
            /\ (!dom G5_Client.ws q => sc = [] /\ c = 0){2}
            /\ (dom G5_Client.ws q => sc = oget (G5_Client.ws.[q]) /\ c = size sc /\ s = backward G5_Client.sk (last witness sc)){2}).
        sp; if; first by progress; smt.
        * wp; rnd; wp; skip; progress.
          - rewrite -some_oget //.
          - smt.
          - smt.
          - smt.
        * wp; skip; progress.
          - move : (H6 q{2}).
            rewrite H15 /=.
            move => [rwme _].
            rewrite rwme oget_some //.
            move : (H6 q{2}).
            rewrite H15 /=.
            move => [rwme _].
            rewrite rwme oget_some /=; smt.
          - rewrite -some_oget //.
          - smt.
          - smt.
          - smt.

      case (dom G5_Client.h1t{2} (kw, s){2}).
      + (* Bad event related to h1t *)
        rcondt{2} 2; first by progress; first by wp; skip; progress.
        wp; simplify; kill{1} 10; first by rnd; skip; progress; smt.
        wp; kill{1} 4; first by rnd; skip; progress; smt.
        wp; skip; progress.
      + (* no bad events so far *)
        rcondf{2} 2; first by progress; first by wp; skip; progress.
      case (dom G5_Client.h2t{2} (kw, s){2}).
      + (* Bad event related to h2t *)
        rcondt{2} 2; first by progress; first by wp; skip; progress.
        wp; simplify; kill{1} 10; first by rnd; skip; progress; smt.
        wp; kill{1} 4; first by rnd; skip; progress; smt.
        wp; skip; progress.
      + (* no bad events so far *)
        rcondf{2} 2; first by progress; first by wp; skip; progress.
      case (let g = fun (_ : query) (k : mapquery) => k = kw{2} in
            let qs = fdom (filter g RF.m{2}) in
            let f = fun (q : query) (ts : stoken list) => (mem qs q) /\ has ((=) s{2}) ts in
            let cws = filter f G5_Client.ws{2}.[q0{2} <- sc{2} ++ [s{2}]] in
            cws <> empty).
      + rcondt{2} 4; first by progress; first by wp; skip; progress.
      + (* Bad event related to bt (either utt or et) *)
        wp; simplify; kill{1} 10; first by rnd; skip; progress; smt.
        wp; rnd{1}; wp; skip; progress; smt.
      + (* no bad events so far *)
        rcondf{2} 4; first by progress; first by wp; skip; progress.
        rcondt{1} 5; progress.
sp; rnd; skip.
progress.
(have kw_def: (oget RF.m.[q] = kw){m} by rewrite H14 oget_some //);
move : H20;
pose g := fun (_: query) (k: mapquery) => k = kw{m};
  pose qs := fdom (filter g RF.m{m});
  pose f := fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s{m}) ts;
move => filter0_set;
(have not_f_q_set: (!f q (sc ++ [s])){m} by
  move : filter0_set; apply absurd => //= ah; rewrite -fmap_eqP negb_forall /=; exists q{m}; rewrite filterE get_set_sameE emptyE /= ah //);
(have qs_q: ((mem qs q){m}) by rewrite /qs /g mem_fdom dom_filter domE H14 oget_some //);
(have scs_s: (!has ((=) s) (sc ++ [s])){m} by
  move : not_f_q_set; rewrite /f qs_q //=);
(have scs_not_s: (has ((=) s) (sc ++ [s])){m} by (* we can then introduce a clear contradiction *)
rewrite hasP; exists s{m}; rewrite //= mem_cat //);
move : scs_not_s; rewrite scs_s //.
        rcondt{1} 11; progress.
rnd; wp; rnd; wp; skip.
progress.
(have kw_def: (oget RF.m.[q] = kw){m} by rewrite H14 oget_some //);
move : H20;
pose g := fun (_: query) (k: mapquery) => k = kw{m};
  pose qs := fdom (filter g RF.m{m});
  pose f := fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s{m}) ts;
move => filter0_set;
(have not_f_q_set: (!f q (sc ++ [s])){m} by
  move : filter0_set; apply absurd => //= ah; rewrite -fmap_eqP negb_forall /=; exists q{m}; rewrite filterE get_set_sameE emptyE /= ah //);
(have qs_q: ((mem qs q){m}) by rewrite /qs /g mem_fdom dom_filter domE H14 oget_some //);
(have scs_s: (!has ((=) s) (sc ++ [s])){m} by
  move : not_f_q_set; rewrite /f qs_q //=);
(have scs_not_s: (has ((=) s) (sc ++ [s])){m} by (* we can then introduce a clear contradiction *)
rewrite hasP; exists s{m}; rewrite //= mem_cat //);
move : scs_not_s; rewrite scs_s //.

rcondt{1} 17; first by progress; first by wp; rnd; wp; rnd; wp; skip; progress.
rcondt{2} 10; first by progress; first by wp; rnd; wp; rnd; wp; skip; progress.
rcondt{1} 21; first by progress; first by wp; rnd; wp; rnd; wp; skip; progress.
rcondt{2} 14; first by progress; first by wp; rnd; wp; rnd; wp; skip; progress.


kill{2} 3; first by wp; skip; progress.
kill{2} 2; first by wp; skip; progress.

wp; rnd; wp; rnd; wp; skip; progress; first 39 by
(have kw_def: (oget RF.m.[q] = kw){2} by rewrite H14 oget_some //);
move : H20;
pose g := fun (_: query) (k: mapquery) => k = kw{2};
  pose qs := fdom (filter g RF.m{2});
  pose f := fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s{2}) ts;
move => filter0_set;
(have not_f_q_set: (!f q (sc ++ [s])){2} by
  move : filter0_set; apply absurd => //= ah; rewrite -fmap_eqP negb_forall /=; exists q{2}; rewrite filterE get_set_sameE emptyE /= ah //);
(have qs_q: ((mem qs q){2}) by rewrite /qs /g mem_fdom dom_filter domE H14 oget_some //);
(have scs_s: (!has ((=) s) (sc ++ [s])){2} by
  move : not_f_q_set; rewrite /f qs_q //=);
(have scs_not_s: (has ((=) s) (sc ++ [s])){2} by (* we can then introduce a clear contradiction *)
rewrite hasP; exists s{2}; rewrite //= mem_cat //);
move : scs_not_s; rewrite scs_s //.

    + (* Then part: this is thougher because we sample to RF.m *)
      seq 2 2: (={kw, i0, o, q, q0}
               (* UPDATE ASSUMPTIONS *)
            /\   (glob RF, glob G4_Server, G4_Client.sk){1}
               = (glob RF, glob G4_Server, G5_Client.sk){2}
            /\ (forall w c, dom G5_Client.utt (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO1.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.utt.[(w, c)]){2}
            /\ (forall w c, dom G5_Client.et (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO2.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.et.[(w, c)]){2}
            /\ (forall w c, !dom G5_Client.utt (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h1t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO1.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall w c, !dom G5_Client.et (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h2t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO2.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall kw s, dom RO1.m{1} (kw, s) => (RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO1.m{1}.[(kw, s)] = G5_Client.utt.[(w, c)])){2}
            /\ (forall kw s, dom RO2.m{1} (kw, s) => (RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO2.m{1}.[(kw, s)] = G5_Client.et.[(w, c)])){2}
            /\ (forall w, dom G4_Client.ws{1} w <=> dom G5_Client.ws{2} w)
            /\ (forall w, dom G4_Client.ws{1} w =>
                     G4_Client.ws{1}.[w] = Some (last witness (oget G5_Client.ws.[w]), size (oget G5_Client.ws.[w]) - 1)
                 /\ (forall c, (!0 <= c < size (oget G5_Client.ws.[w])) => !dom G5_Client.utt (w, c) /\ !dom G5_Client.et (w, c))
               ){2}
            /\ (forall w, !dom RF.m w => !dom G5_Client.ws w){2}
            /\ (forall kw, !rng RF.m kw => forall s, RO1.m.[(kw, s)] = G5_Client.h1t{2}.[(kw, s)] /\ RO2.m.[(kw, s)] = G5_Client.h2t{2}.[(kw, s)]){1} (* if neither update or search have been ever called in the past... *)
            (* /\ (!fmap_collision RF.m){1} *)
               (* SEARCH ASSUMPTIONS *)
            /\ (forall w, dom G4_Client.ws{1} w => (let sc = oget G5_Client.ws.[w] in
                       0 < size sc
                    /\ !dom G5_Client.utt (w, size sc)
                    /\ !dom G5_Client.et (w, size sc)
                    /\ (forall c, 0 <= c < size sc =>
                             dom G5_Client.utt (w, c)
                          /\ dom G5_Client.et (w, c)
                          /\ RO1.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.utt.[(w, c)]
                          /\ RO2.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.et.[(w, c)]
                       )
                    /\ (forall c, 0 < c < size sc => nth witness sc (c - 1) = forward G4_Server.pk (nth witness sc c))
                 )
               ){2}
               (* O(RACLES) ASSUMPTIONS *)
            /\ (forall kw s, dom G5_Client.h1t (kw, s) => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]){2}
            /\ (forall kw s, dom G5_Client.h2t (kw, s) => RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (forall kw s,
                  let g = fun (_: query) (k: mapquery) => k = kw in
                  let qs = fdom (filter g RF.m) in
                  let f = fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts in
                  filter f G5_Client.ws = empty => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)] /\ RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (q0 = q /\ o = ADD){2}
            /\ (RF.m.[q] = Some kw){2}).
         wp; rnd; skip; progress.
smt.
smt.
smt.
smt.
smt.
smt.
smt.
smt.
smt.
smt.
smt.
smt.

case (RO1.m{1}.[(kw0, s0)] = G5_Client.h1t{2}.[(kw0, s0)]) => //= ro1_h1t_sync.
move : (H3 kw0 s0).
rewrite H17 ro1_h1t_sync /=.
move => [sc w c] [sc_def] [c_range] [s0_def] [pre] ro1_utt_sync.
have concl: RF.m{2}.[q{2} <- kw0].[w] = Some kw0 by smt.
exists sc w c.
rewrite ro1_utt_sync sc_def c_range s0_def //=.
rewrite get_set_neqE; first by smt.
exact pre.

case (RO2.m{1}.[(kw0, s0)] = G5_Client.h2t{2}.[(kw0, s0)]) => //= ro2_h2t_sync.
move : (H4 kw0 s0).
rewrite H17 ro2_h2t_sync /=.
move => [sc w c] [sc_def] [c_range] [s0_def] [pre] ro2_et_sync.
have concl: RF.m{2}.[q{2} <- kw0].[w] = Some kw0 by smt.
exists sc w c.
rewrite ro2_et_sync sc_def c_range s0_def //=.
rewrite get_set_neqE; first by smt.
exact pre.


smt.

          have rng_kw0: !rng RF.m{2} kw0.
            move : H17.
            apply absurd => /=.
            rewrite 2!rngE /=.
            move => [w] f_w.
            exists w.
            rewrite get_set_neqE; first by smt.
          smt.
move : (H8 kw0).
rewrite rng_kw0 /= => pre_s.
move : (pre_s s0).
move => [concl] _.
exact concl.
          have rng_kw0: !rng RF.m{2} kw0.
            move : H17.
            apply absurd => /=.
            rewrite 2!rngE /=.
            move => [w] f_w.
            exists w.
            rewrite get_set_neqE; first by smt.
          smt.
move : (H8 kw0).
rewrite rng_kw0 /= => pre_s.
move : (pre_s s0).
move => [_] concl.
exact concl.

smt.
smt.

move : (H10 w).
rewrite H17 /=.
move => [sc0_notnil] [utt_outofbound] [concl] _.
exact concl.

move : (H10 w).
rewrite H17 /=.
move => [sc0_notnil] [utt_outofbound] [et_outofbound] [pre_c] _.
move : (pre_c c0).
rewrite H18 H19 /=.
move => [concl] _.
exact concl.

move : (H10 w).
rewrite H17 /=.
move => [sc0_notnil] [utt_outofbound] [et_outofbound] [pre_c] _.
move : (pre_c c0).
rewrite H18 H19 /=.
move => [_] [concl] _.
exact concl.

move : (H10 w).
rewrite H17 /=.
move => [sc0_notnil] [utt_outofbound] [et_outofbound] [pre_c] _.
move : (pre_c c0).
rewrite H18 H19 /=.
move => [_] [_] [concl] _.
have wq: w <> q{2} by move : (H7 w); apply absurd => //= wq; move : H17; rewrite negb_imply wq H5 H14 //.
rewrite get_set_neqE //.

move : (H10 w).
rewrite H17 /=.
move => [sc0_notnil] [utt_outofbound] [et_outofbound] [pre_c] _.
move : (pre_c c0).
rewrite H18 H19 /=.
move => [_] [_] [_] concl.
have wq: w <> q{2} by move : (H7 w); apply absurd => //= wq; move : H17; rewrite negb_imply wq H5 H14 //.
rewrite get_set_neqE //.

move : (H10 w).
rewrite H17 /=.
move => [sc0_notnil] [utt_outofbound] [et_outofbound] [_] pre_c.
move : (pre_c c0).
rewrite H18 H19 //=.

pose g := fun (_: query) (k: mapquery) => k = kw0;
  pose qs := fdom (filter g RF.m{2});
  pose f := fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s0) ts.
have filter0: filter f G5_Client.ws{2} = empty.
rewrite -H17.
rewrite filter_filter_eq => w ws_w.
have wq: w <> q{2} by move : (H7 w); apply absurd => //= wq; rewrite negb_imply ws_w wq H14 //.
rewrite /f /qs /g /=.
case (has ((=) s0) (oget G5_Client.ws{2}.[w])) => //= has_s_ws_w.
rewrite 2!mem_fdom 2!dom_filter /=.
rewrite mem_set get_set_neqE wq //=.
move : (H13 kw0 s0).
rewrite filter0 /=.
move => [concl] _.
exact concl.

pose g := fun (_: query) (k: mapquery) => k = kw0;
  pose qs := fdom (filter g RF.m{2});
  pose f := fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s0) ts.
have filter0: filter f G5_Client.ws{2} = empty.
rewrite -H17.
rewrite filter_filter_eq => w ws_w.
have wq: w <> q{2} by move : (H7 w); apply absurd => //= wq; rewrite negb_imply ws_w wq H14 //.
rewrite /f /qs /g /=.
case (has ((=) s0) (oget G5_Client.ws{2}.[w])) => //= has_s_ws_w.
rewrite 2!mem_fdom 2!dom_filter /=.
rewrite mem_set get_set_neqE wq //=.
move : (H13 kw0 s0).
rewrite filter0 /=.
move => [_] concl.
exact concl.

rewrite get_set_sameE oget_some //.

      if{2}.
      + (* Bad event related to collision *)
        wp; simplify; kill{1} 11; first by rnd; skip; progress; smt.
        wp; kill{1} 5; first by rnd; skip; progress; smt.
        if{1}.
        * wp; rnd{1}; skip; progress; smt.
        * wp; skip; progress.
      + (* no bad events so far *)
      seq 1 1: (={kw, s, c, i0, o, q}
               (* UPDATE ASSUMPTIONS *)
            /\   (glob RF, glob G4_Server, G4_Client.sk){1}
               = (glob RF, glob G4_Server, G5_Client.sk){2}
            /\ (forall w c, dom G5_Client.utt (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO1.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.utt.[(w, c)]){2}
            /\ (forall w c, dom G5_Client.et (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO2.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.et.[(w, c)]){2}
            /\ (forall w c, !dom G5_Client.utt (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h1t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO1.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall w c, !dom G5_Client.et (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h2t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO2.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall kw s, dom RO1.m{1} (kw, s) => (RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO1.m{1}.[(kw, s)] = G5_Client.utt.[(w, c)])){2}
            /\ (forall kw s, dom RO2.m{1} (kw, s) => (RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO2.m{1}.[(kw, s)] = G5_Client.et.[(w, c)])){2}
            /\ (forall w, dom G4_Client.ws{1} w <=> dom G5_Client.ws{2} w)
            /\ (forall w, dom G4_Client.ws{1} w =>
                     G4_Client.ws{1}.[w] = Some (last witness (oget G5_Client.ws.[w]), size (oget G5_Client.ws.[w]) - 1)
                 /\ (forall c, (!0 <= c < size (oget G5_Client.ws.[w])) => !dom G5_Client.utt (w, c) /\ !dom G5_Client.et (w, c))
               ){2}
            /\ (forall w, !dom RF.m w => !dom G5_Client.ws w){2}
            /\ (forall kw, !rng RF.m kw => forall s, RO1.m.[(kw, s)] = G5_Client.h1t{2}.[(kw, s)] /\ RO2.m.[(kw, s)] = G5_Client.h2t{2}.[(kw, s)]){1} (* if neither update or search have been ever called in the past... *)
            /\ (!fmap_collision RF.m){1}
               (* SEARCH ASSUMPTIONS *)
            /\ (forall w, dom G4_Client.ws{1} w => (let sc = oget G5_Client.ws.[w] in
                       0 < size sc
                    /\ !dom G5_Client.utt (w, size sc)
                    /\ !dom G5_Client.et (w, size sc)
                    /\ (forall c, 0 <= c < size sc =>
                             dom G5_Client.utt (w, c)
                          /\ dom G5_Client.et (w, c)
                          /\ RO1.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.utt.[(w, c)]
                          /\ RO2.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.et.[(w, c)]
                       )
                    /\ (forall c, 0 < c < size sc => nth witness sc (c - 1) = forward G4_Server.pk (nth witness sc c))
                 )
               ){2}
               (* O(RACLES) ASSUMPTIONS *)
            /\ (forall kw s, dom G5_Client.h1t (kw, s) => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]){2}
            /\ (forall kw s, dom G5_Client.h2t (kw, s) => RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (forall kw s,
                  let g = fun (_: query) (k: mapquery) => k = kw in
                  let qs = fdom (filter g RF.m) in
                  let f = fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts in
                  filter f G5_Client.ws = empty => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)] /\ RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (q0 = q /\ o = ADD){2}
            /\ (RF.m.[q] = Some kw){2}
            /\ (!dom G5_Client.utt (q, c)){2}
            /\ (!dom G5_Client.ws q => sc = [] /\ c = 0){2}
            /\ (dom G5_Client.ws q => sc = oget (G5_Client.ws.[q]) /\ c = size sc /\ s = backward G5_Client.sk (last witness sc)){2}).
if => //.
progress.
rewrite -H5 H15 //.
rewrite H5 H15 //.

- (* THEN *)
wp; rnd; wp; skip; progress.
smt.
smt.
smt.
        * wp; skip; progress.
          - move : (H6 q{2}).
            rewrite H15 /=.
            move => [rwme _].
            rewrite rwme oget_some //.
            move : (H6 q{2}).
            rewrite H15 /=.
            move => [rwme _].
            rewrite rwme oget_some /=; smt.
          - smt.
          - smt.
          - smt.

      case (dom G5_Client.h1t{2} (kw, s){2}).
      + (* Bad event related to h1t *)
        rcondt{2} 2; first by progress; first by wp; skip; progress.
        wp; simplify; kill{1} 10; first by rnd; skip; progress; smt.
        wp; kill{1} 4; first by rnd; skip; progress; smt.
        wp; skip; progress.
      + (* no bad events so far *)
        rcondf{2} 2; first by progress; first by wp; skip; progress.
      case (dom G5_Client.h2t{2} (kw, s){2}).
      + (* Bad event related to h2t *)
        rcondt{2} 2; first by progress; first by wp; skip; progress.
        wp; simplify; kill{1} 10; first by rnd; skip; progress; smt.
        wp; kill{1} 4; first by rnd; skip; progress; smt.
        wp; skip; progress.
      + (* no bad events so far *)
        rcondf{2} 2; first by progress; first by wp; skip; progress.
      case (let g = fun (_ : query) (k : mapquery) => k = kw{2} in
            let qs = fdom (filter g RF.m{2}) in
            let f = fun (q : query) (ts : stoken list) => (mem qs q) /\ has ((=) s{2}) ts in
            let cws = filter f G5_Client.ws{2}.[q0{2} <- sc{2} ++ [s{2}]] in
            cws <> empty).
      + rcondt{2} 4; first by progress; first by wp; skip; progress.
      + (* Bad event related to bt (either utt or et) *)
        wp; simplify; kill{1} 10; first by rnd; skip; progress; smt.
        wp; rnd{1}; wp; skip; progress; smt.
      + (* no bad events so far *)
        rcondf{2} 4; first by progress; first by wp; skip; progress.
        rcondt{1} 5; progress.
sp; rnd; skip.
progress.
(have kw_def: (oget RF.m.[q] = kw){m} by rewrite H14 oget_some //);
move : H20;
pose g := fun (_: query) (k: mapquery) => k = kw{m};
  pose qs := fdom (filter g RF.m{m});
  pose f := fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s{m}) ts;
move => filter0_set;
(have not_f_q_set: (!f q (sc ++ [s])){m} by
  move : filter0_set; apply absurd => //= ah; rewrite -fmap_eqP negb_forall /=; exists q{m}; rewrite filterE get_set_sameE emptyE /= ah //);
(have qs_q: ((mem qs q){m}) by rewrite /qs /g mem_fdom dom_filter domE H14 oget_some //);
(have scs_s: (!has ((=) s) (sc ++ [s])){m} by
  move : not_f_q_set; rewrite /f qs_q //=);
(have scs_not_s: (has ((=) s) (sc ++ [s])){m} by (* we can then introduce a clear contradiction *)
rewrite hasP; exists s{m}; rewrite //= mem_cat //);
move : scs_not_s; rewrite scs_s //.
        rcondt{1} 11; progress.
rnd; wp; rnd; wp; skip.
progress.
(have kw_def: (oget RF.m.[q] = kw){m} by rewrite H14 oget_some //);
move : H20;
pose g := fun (_: query) (k: mapquery) => k = kw{m};
  pose qs := fdom (filter g RF.m{m});
  pose f := fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s{m}) ts;
move => filter0_set;
(have not_f_q_set: (!f q (sc ++ [s])){m} by
  move : filter0_set; apply absurd => //= ah; rewrite -fmap_eqP negb_forall /=; exists q{m}; rewrite filterE get_set_sameE emptyE /= ah //);
(have qs_q: ((mem qs q){m}) by rewrite /qs /g mem_fdom dom_filter domE H14 oget_some //);
(have scs_s: (!has ((=) s) (sc ++ [s])){m} by
  move : not_f_q_set; rewrite /f qs_q //=);
(have scs_not_s: (has ((=) s) (sc ++ [s])){m} by (* we can then introduce a clear contradiction *)
rewrite hasP; exists s{m}; rewrite //= mem_cat //);
move : scs_not_s; rewrite scs_s //.

rcondt{1} 17; first by progress; first by wp; rnd; wp; rnd; wp; skip; progress.
rcondt{2} 10; first by progress; first by wp; rnd; wp; rnd; wp; skip; progress.
rcondt{1} 21; first by progress; first by wp; rnd; wp; rnd; wp; skip; progress.
rcondt{2} 14; first by progress; first by wp; rnd; wp; rnd; wp; skip; progress.


kill{2} 3; first by wp; skip; progress.
kill{2} 2; first by wp; skip; progress.

wp; rnd; wp; rnd; wp; skip; progress; first 39 by
(have kw_def: (oget RF.m.[q] = kw){2} by rewrite H14 oget_some //);
move : H20;
pose g := fun (_: query) (k: mapquery) => k = kw{2};
  pose qs := fdom (filter g RF.m{2});
  pose f := fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s{2}) ts;
move => filter0_set;
(have not_f_q_set: (!f q (sc ++ [s])){2} by
  move : filter0_set; apply absurd => //= ah; rewrite -fmap_eqP negb_forall /=; exists q{2}; rewrite filterE get_set_sameE emptyE /= ah //);
(have qs_q: ((mem qs q){2}) by rewrite /qs /g mem_fdom dom_filter domE H14 oget_some //);
(have scs_s: (!has ((=) s) (sc ++ [s])){2} by
  move : not_f_q_set; rewrite /f qs_q //=);
(have scs_not_s: (has ((=) s) (sc ++ [s])){2} by (* we can then introduce a clear contradiction *)
rewrite hasP; exists s{2}; rewrite //= mem_cat //);
move : scs_not_s; rewrite scs_s //.
  qed.

  lemma eq_G4_G5_no_bad_events_query_consistency:
    equiv[G4.query ~ G5.query:
          ={q}
               (* UPDATE ASSUMPTIONS *)
            /\   (glob RF, glob G4_Server, G4_Client.sk){1}
               = (glob RF, glob G4_Server, G5_Client.sk){2}
            /\ (forall w c, dom G5_Client.utt (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO1.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.utt.[(w, c)]){2}
            /\ (forall w c, dom G5_Client.et (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO2.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.et.[(w, c)]){2}
            /\ (forall w c, !dom G5_Client.utt (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h1t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO1.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall w c, !dom G5_Client.et (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h2t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO2.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall kw s, dom RO1.m{1} (kw, s) => (RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO1.m{1}.[(kw, s)] = G5_Client.utt.[(w, c)])){2}
            /\ (forall kw s, dom RO2.m{1} (kw, s) => (RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO2.m{1}.[(kw, s)] = G5_Client.et.[(w, c)])){2}
            /\ (forall w, dom G4_Client.ws{1} w <=> dom G5_Client.ws{2} w)
            /\ (forall w, dom G4_Client.ws{1} w =>
                     G4_Client.ws{1}.[w] = Some (last witness (oget G5_Client.ws.[w]), size (oget G5_Client.ws.[w]) - 1)
                 /\ (forall c, (!0 <= c < size (oget G5_Client.ws.[w])) => !dom G5_Client.utt (w, c) /\ !dom G5_Client.et (w, c))
               ){2}
            /\ (forall w, !dom RF.m w => !dom G5_Client.ws w){2}
            /\ (forall kw, !rng RF.m kw => forall s, RO1.m.[(kw, s)] = G5_Client.h1t{2}.[(kw, s)] /\ RO2.m.[(kw, s)] = G5_Client.h2t{2}.[(kw, s)]){1} (* if neither update or search have been ever called in the past... *)
            /\ (!fmap_collision RF.m){1}
               (* SEARCH ASSUMPTIONS *)
            /\ (forall w, dom G4_Client.ws{1} w => (let sc = oget G5_Client.ws.[w] in
                       0 < size sc
                    /\ !dom G5_Client.utt (w, size sc)
                    /\ !dom G5_Client.et (w, size sc)
                    /\ (forall c, 0 <= c < size sc =>
                             dom G5_Client.utt (w, c)
                          /\ dom G5_Client.et (w, c)
                          /\ RO1.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.utt.[(w, c)]
                          /\ RO2.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.et.[(w, c)]
                       )
                    /\ (forall c, 0 < c < size sc => nth witness sc (c - 1) = forward G4_Server.pk (nth witness sc c))
                 )
               ){2}
               (* O(RACLES) ASSUMPTIONS *)
            /\ (forall kw s, dom G5_Client.h1t (kw, s) => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]){2}
            /\ (forall kw s, dom G5_Client.h2t (kw, s) => RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (forall kw s,
                  let g = fun (_: query) (k: mapquery) => k = kw in
                  let qs = fdom (filter g RF.m) in
                  let f = fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts in
                  filter f G5_Client.ws = empty => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)] /\ RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
          ==> ={res} /\ (!G5_Client.bad_rf_coll{2} => (* consistency kept if no bad event happened *)
               (* UPDATE ASSUMPTIONS *)
                 (glob RF, glob G4_Server, G4_Client.sk){1}
               = (glob RF, glob G4_Server, G5_Client.sk){2}
            /\ (forall w c, dom G5_Client.utt (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO1.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.utt.[(w, c)]){2}
            /\ (forall w c, dom G5_Client.et (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO2.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.et.[(w, c)]){2}
            /\ (forall w c, !dom G5_Client.utt (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h1t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO1.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall w c, !dom G5_Client.et (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h2t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO2.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall kw s, dom RO1.m{1} (kw, s) => (RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO1.m{1}.[(kw, s)] = G5_Client.utt.[(w, c)])){2}
            /\ (forall kw s, dom RO2.m{1} (kw, s) => (RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO2.m{1}.[(kw, s)] = G5_Client.et.[(w, c)])){2}
            /\ (forall w, dom G4_Client.ws{1} w <=> dom G5_Client.ws{2} w)
            /\ (forall w, dom G4_Client.ws{1} w =>
                     G4_Client.ws{1}.[w] = Some (last witness (oget G5_Client.ws.[w]), size (oget G5_Client.ws.[w]) - 1)
                 /\ (forall c, (!0 <= c < size (oget G5_Client.ws.[w])) => !dom G5_Client.utt (w, c) /\ !dom G5_Client.et (w, c))
               ){2}
            /\ (forall w, !dom RF.m w => !dom G5_Client.ws w){2}
            /\ (forall kw, !rng RF.m kw => forall s, RO1.m.[(kw, s)] = G5_Client.h1t{2}.[(kw, s)] /\ RO2.m.[(kw, s)] = G5_Client.h2t{2}.[(kw, s)]){1} (* if neither update or search have been ever called in the past... *)
            /\ (!fmap_collision RF.m){1}
               (* SEARCH ASSUMPTIONS *)
            /\ (forall w, dom G4_Client.ws{1} w => (let sc = oget G5_Client.ws.[w] in
                       0 < size sc
                    /\ !dom G5_Client.utt (w, size sc)
                    /\ !dom G5_Client.et (w, size sc)
                    /\ (forall c, 0 <= c < size sc =>
                             dom G5_Client.utt (w, c)
                          /\ dom G5_Client.et (w, c)
                          /\ RO1.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.utt.[(w, c)]
                          /\ RO2.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.et.[(w, c)]
                       )
                    /\ (forall c, 0 < c < size sc => nth witness sc (c - 1) = forward G4_Server.pk (nth witness sc c))
                 )
               ){2}
               (* O(RACLES) ASSUMPTIONS *)
            /\ (forall kw s, dom G5_Client.h1t (kw, s) => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]){2}
            /\ (forall kw s, dom G5_Client.h2t (kw, s) => RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (forall kw s,
                  let g = fun (_: query) (k: mapquery) => k = kw in
                  let qs = fdom (filter g RF.m) in
                  let f = fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts in
                  filter f G5_Client.ws = empty => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)] /\ RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
      )
    ].
  proof.
    proc.
    seq 1 1: (={q, qo} /\ ((* Consistency *)
               (* UPDATE ASSUMPTIONS *)
                 (glob RF, glob G4_Server, G4_Client.sk){1}
               = (glob RF, glob G4_Server, G5_Client.sk){2}
            /\ (forall w c, dom G5_Client.utt (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO1.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.utt.[(w, c)]){2}
            /\ (forall w c, dom G5_Client.et (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO2.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.et.[(w, c)]){2}
            /\ (forall w c, !dom G5_Client.utt (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h1t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO1.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall w c, !dom G5_Client.et (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h2t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO2.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall kw s, dom RO1.m{1} (kw, s) => (RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO1.m{1}.[(kw, s)] = G5_Client.utt.[(w, c)])){2}
            /\ (forall kw s, dom RO2.m{1} (kw, s) => (RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO2.m{1}.[(kw, s)] = G5_Client.et.[(w, c)])){2}
            /\ (forall w, dom G4_Client.ws{1} w <=> dom G5_Client.ws{2} w)
            /\ (forall w, dom G4_Client.ws{1} w =>
                     G4_Client.ws{1}.[w] = Some (last witness (oget G5_Client.ws.[w]), size (oget G5_Client.ws.[w]) - 1)
                 /\ (forall c, (!0 <= c < size (oget G5_Client.ws.[w])) => !dom G5_Client.utt (w, c) /\ !dom G5_Client.et (w, c))
               ){2}
            /\ (forall w, !dom RF.m w => !dom G5_Client.ws w){2}
            /\ (forall kw, !rng RF.m kw => forall s, RO1.m.[(kw, s)] = G5_Client.h1t{2}.[(kw, s)] /\ RO2.m.[(kw, s)] = G5_Client.h2t{2}.[(kw, s)]){1} (* if neither update or search have been ever called in the past... *)
            /\ (!G5_Client.bad_rf_coll{2} => !fmap_collision RF.m){1}
               (* SEARCH ASSUMPTIONS *)
            /\ (forall w, dom G4_Client.ws{1} w => (let sc = oget G5_Client.ws.[w] in
                       0 < size sc
                    /\ !dom G5_Client.utt (w, size sc)
                    /\ !dom G5_Client.et (w, size sc)
                    /\ (forall c, 0 <= c < size sc =>
                             dom G5_Client.utt (w, c)
                          /\ dom G5_Client.et (w, c)
                          /\ RO1.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.utt.[(w, c)]
                          /\ RO2.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.et.[(w, c)]
                       )
                    /\ (forall c, 0 < c < size sc => nth witness sc (c - 1) = forward G4_Server.pk (nth witness sc c))
                 )
               ){2}
               (* O(RACLES) ASSUMPTIONS *)
            /\ (forall kw s, dom G5_Client.h1t (kw, s) => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]){2}
            /\ (forall kw s, dom G5_Client.h2t (kw, s) => RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (forall kw s,
                  let g = fun (_: query) (k: mapquery) => k = kw in
                  let qs = fdom (filter g RF.m) in
                  let f = fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts in
                  filter f G5_Client.ws = empty => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)] /\ RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            )
               (* consequence of query - independend from consistency *)
            /\ (qo{1} <> None => (dom RF.m q){1} /\ (dom G5_Client.ws q){2} /\ let kw = oget RF.m{1}.[q{1}] in let sc = oget G5_Client.ws{2}.[q{1}] in (qo = Some (kw, last witness sc, size sc - 1)){2} /\  forall s c, 0 <= c < size sc => s = nth witness sc c => dom RO1.m{1} (kw, s) /\ dom RO2.m{1} (kw, s) /\ RO1.m{1}.[(kw, s)] = G5_Client.h1t{2}.[(kw, s)] /\ RO2.m{1}.[(kw, s)] = G5_Client.h2t{2}.[(kw, s)])). (* The client part must sync h1t properly *)
      inline*.
        (* Bad event related to collision does not affect the result, yet we need the non-collision property to maintain consistency. *)
      sp; case ((!dom G5_Client.ws q){2}).
      + rcondt{1} 1; progress; first by  skip; progress; rewrite H5 H14 //.
        rcondt{2} 1; progress.
        wp; skip; progress.
      + rcondf{1} 1; progress; first by skip; progress; rewrite H5 H14 //.
        rcondf{2} 1; progress.
        swap{2} 10 -1; while{2} ((0 <= i <= size sc){2}
            /\ ={kw, q0, q, r, qo}
            /\ (q0 = q){2}
            /\ (qo = r){2}
            /\ (RF.m.[q] = Some kw){2}
            /\ (G5_Client.ws.[q] = Some sc){2}
            /\ (0 < size sc){2}
            /\ (c = size sc - 1){2}
            /\ (sc{1} = (last witness sc, c)){2}
            /\ (0 < i => s = nth witness sc (i - 1)){2}
            /\ (r = Some (kw, last witness sc, c)){2}
            /\ (forall j, 0 < j < size sc => nth witness sc (j - 1) = forward G4_Server.pk (nth witness sc j)){2}
            /\ (!dom G5_Client.utt (q, size sc)){2}
            /\ (forall j, 0 <= j < size sc =>
                    dom G5_Client.utt (q, j)
                 /\ dom G5_Client.et (q, j)
                 /\ RO1.m{1}.[(oget RF.m{1}.[q], nth witness sc j)] = G5_Client.utt.[(q, j)]
                 /\ RO2.m{1}.[(oget RF.m{1}.[q], nth witness sc j)] = G5_Client.et.[(q, j)]
               ){2}
            /\ (forall j, 0 <= j < i =>
                     RO1.m{1}.[(kw, nth witness sc j)] = G5_Client.utt.[(q, j)]
                  /\ RO1.m{1}.[(kw, nth witness sc j)] = G5_Client.h1t.[(kw, nth witness sc j)]
                  /\ RO2.m{1}.[(kw, nth witness sc j)] = G5_Client.et.[(q, j)]
                  /\ RO2.m{1}.[(kw, nth witness sc j)] = G5_Client.h2t.[(kw, nth witness sc j)]
               ){2}
               (* UPDATE ASSUMPTIONS *)
            /\   (glob RF, glob G4_Server, G4_Client.sk){1}
               = (glob RF, glob G4_Server, G5_Client.sk){2}
            /\ (forall w c, dom G5_Client.utt (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO1.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.utt.[(w, c)]){2}
            /\ (forall w c, dom G5_Client.et (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO2.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.et.[(w, c)]){2}
            /\ (forall w c, !dom G5_Client.utt (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h1t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO1.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall w c, !dom G5_Client.et (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h2t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO2.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall kw s, dom RO1.m{1} (kw, s) => (RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO1.m{1}.[(kw, s)] = G5_Client.utt.[(w, c)])){2}
            /\ (forall kw s, dom RO2.m{1} (kw, s) => (RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO2.m{1}.[(kw, s)] = G5_Client.et.[(w, c)])){2}
            /\ (forall w, dom G4_Client.ws{1} w <=> dom G5_Client.ws{2} w)
            /\ (forall w, dom G4_Client.ws{1} w =>
                     G4_Client.ws{1}.[w] = Some (last witness (oget G5_Client.ws.[w]), size (oget G5_Client.ws.[w]) - 1)
                 /\ (forall c, (!0 <= c < size (oget G5_Client.ws.[w])) => !dom G5_Client.utt (w, c) /\ !dom G5_Client.et (w, c))
               ){2}
            /\ (forall w, !dom RF.m w => !dom G5_Client.ws w){2}
            /\ (forall kw, !rng RF.m kw => forall s, RO1.m.[(kw, s)] = G5_Client.h1t{2}.[(kw, s)] /\ RO2.m.[(kw, s)] = G5_Client.h2t{2}.[(kw, s)]){1} (* if neither update or search have been ever called in the past... *)
            /\ (!G5_Client.bad_rf_coll{2} => !fmap_collision RF.m){1}
               (* SEARCH ASSUMPTIONS *)
            /\ (forall w, dom G4_Client.ws{1} w => (let sc = oget G5_Client.ws.[w] in
                       0 < size sc
                    /\ !dom G5_Client.utt (w, size sc)
                    /\ !dom G5_Client.et (w, size sc)
                    /\ (forall c, 0 <= c < size sc =>
                             dom G5_Client.utt (w, c)
                          /\ dom G5_Client.et (w, c)
                          /\ RO1.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.utt.[(w, c)]
                          /\ RO2.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.et.[(w, c)]
                       )
                    /\ (forall c, 0 < c < size sc => nth witness sc (c - 1) = forward G4_Server.pk (nth witness sc c))
                 )
               ){2}
               (* O(RACLES) ASSUMPTIONS *)
            /\ (forall kw s, dom G5_Client.h1t (kw, s) => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]){2}
            /\ (forall kw s, dom G5_Client.h2t (kw, s) => RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (forall kw s,
                  let g = fun (_: query) (k: mapquery) => k = kw in
                  let qs = fdom (filter g RF.m) in
                  let f = fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts in
                  filter f G5_Client.ws = empty => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)] /\ RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
        ) (size sc{2} - i{2}) => * /=.
          wp; skip; progress; first 2 by smt.
          + move : (H7 j).
            have ->: 0 <= j < size sc{hr} by smt.
            rewrite /=.
            have ->: (kw{hr} = oget RF.m{hr}.[q{hr}]) by smt.
            trivial.
          + move : (H7 j).
            have ->: 0 <= j < size sc{hr} by smt.
            rewrite /=.
            move => [_].
            move : (H7 i{hr}).
            have ->: 0 <= i{hr} < size sc{hr} by smt.
            rewrite /=.
            move => [_].
            have <-: (kw{hr} = oget RF.m{hr}.[q{hr}]) by smt.
            pose sj := nth witness sc{hr} j;
            pose si := nth witness sc{hr} i{hr}.
            case (si = sj) => si_sj.
            + rewrite si_sj get_set_sameE -some_oget //.
            + case (((kw, sj) = (kw, si)){hr}) => xi_xj.
              * rewrite xi_xj get_set_sameE -some_oget //.
              * rewrite get_set_neqE //; smt.
          + move : (H7 j).
            have ->: 0 <= j < size sc{hr} by smt.
            rewrite /=.
            have ->: (kw{hr} = oget RF.m{hr}.[q{hr}]) by smt.
            trivial.
          + move : (H7 j).
            have ->: 0 <= j < size sc{hr} by smt.
            rewrite /=.
            move => [_] [_].
            move : (H7 i{hr}).
            have ->: 0 <= i{hr} < size sc{hr} by smt.
            rewrite /=.
            move => [_] [_].
            have <-: (kw{hr} = oget RF.m{hr}.[q{hr}]) by smt.
            pose sj := nth witness sc{hr} j;
            pose si := nth witness sc{hr} i{hr}.
            case (si = sj) => si_sj.
            + rewrite si_sj get_set_sameE -some_oget //.
            + case (((kw, sj) = (kw, si)){hr}) => xi_xj.
              * rewrite xi_xj get_set_sameE -some_oget //.
              * rewrite get_set_neqE //; smt.
          + smt.
          + smt.
          +
case (kw0 = kw{hr}) => //= kw0kw.
rewrite kw0kw.
case (s0 = nth witness sc{hr} i{hr}) => //= s0_def.
move : (H7 i{hr}).
rewrite H H24 H1 /=.
move => [_] [_].
rewrite -s0_def oget_some get_set_sameE -some_oget //=.
move => [ro1_utt ro2_et].
left => //.
rewrite get_set_neqE //=.
case (RO1.m{m}.[(kw{hr}, s0)] = G5_Client.h1t{hr}.[(kw{hr}, s0)]) => //= notleft.
move : (H13 kw0 s0).
rewrite H25 kw0kw notleft /=.
move => [sc w c] concl.
exists sc w c.
exact concl.
rewrite get_set_neqE /=; first by rewrite kw0kw //=.
case (RO1.m{m}.[(kw0, s0)] = G5_Client.h1t{hr}.[(kw0, s0)]) => //= notleft.
move : (H13 kw0 s0).
rewrite H25 notleft /=.
move => [sc w c] concl.
exists sc w c.
exact concl.
+ case (kw0 = kw{hr}) => //= kw0kw.
rewrite kw0kw.
case (s0 = nth witness sc{hr} i{hr}) => //= s0_def.
move : (H7 i{hr}).
rewrite H H24 H1 /=.
move => [_] [_].
rewrite -s0_def oget_some get_set_sameE -some_oget //=.
move => [ro1_utt ro2_et].
left => //.
rewrite get_set_neqE //=.
case (RO2.m{m}.[(kw{hr}, s0)] = G5_Client.h2t{hr}.[(kw{hr}, s0)]) => //= notleft.
move : (H14 kw0 s0).
rewrite H25 kw0kw notleft /=.
move => [sc w c] concl.
exists sc w c.
exact concl.
rewrite get_set_neqE /=; first by rewrite kw0kw //=.
case (RO2.m{m}.[(kw0, s0)] = G5_Client.h2t{hr}.[(kw0, s0)]) => //= notleft.
move : (H14 kw0 s0).
rewrite H25 notleft /=.
move => [sc w c] concl.
exists sc w c.
exact concl.

case ((kw0, s0) = (kw, nth witness sc i){hr}) => x_def.
rewrite x_def.
move : (H7 i{hr}).
rewrite H H24 /=.
move => [utt_qi] [et_qi].
rewrite H1 oget_some get_set_sameE -some_oget //.
rewrite get_set_neqE //.
move : (H18 kw0).
rewrite H25 /= => pre_s.
move : (pre_s s0).
move => [concl] _.
exact concl.

case ((kw0, s0) = (kw, nth witness sc i){hr}) => x_def.
rewrite x_def.
move : (H7 i{hr}).
rewrite H H24 /=.
move => [utt_qi] [et_qi].
rewrite H1 oget_some get_set_sameE -some_oget //.
rewrite get_set_neqE //.
move : (H18 kw0).
rewrite H25 /= => pre_s.
move : (pre_s s0).
move => [_ concl].
exact concl.

case ((kw0, s0) = (kw, nth witness sc i){hr}) => x_def.
rewrite x_def.
move : (H7 i{hr}).
rewrite H H24 /=.
move => [utt_qi] [et_qi].
rewrite H1 oget_some get_set_sameE -some_oget //.
move : H25 (H21 kw0 s0).
rewrite mem_set x_def /= => pre.
rewrite pre // get_set_neqE //.

case ((kw0, s0) = (kw, nth witness sc i){hr}) => x_def.
rewrite x_def.
move : (H7 i{hr}).
rewrite H H24 /=.
move => [utt_qi] [et_qi].
rewrite H1 oget_some get_set_sameE -some_oget //.
move : H25 (H22 kw0 s0).
rewrite mem_set x_def /= => pre.
rewrite pre // get_set_neqE //.

case ((kw0, s0) = (kw, nth witness sc i){hr}) => x_def.
rewrite x_def.
move : (H7 i{hr}).
rewrite H H24 /=.
move => [utt_qi] [et_qi].
rewrite H1 oget_some get_set_sameE -some_oget //.
rewrite get_set_neqE //.
move : (H23 kw0 s0).
rewrite H25 /=.
move => [concl _].
exact concl.

case ((kw0, s0) = (kw, nth witness sc i){hr}) => x_def.
rewrite x_def.
move : (H7 i{hr}).
rewrite H H24 /=.
move => [utt_qi] [et_qi].
rewrite H1 oget_some get_set_sameE -some_oget //.
rewrite get_set_neqE //.
move : (H23 kw0 s0).
rewrite H25 /=.
move => [_ concl].
exact concl.

smt.
        * wp; sp; if => //.
          rnd; skip; progress; expect 106; first 106 by smt.
        + skip; progress; expect 50; first 26 by smt.
        * rewrite -H5 in H14.
          move : (H6 q{2} H14) => [ws_def _ ].
          rewrite ws_def oget_some nth_last //=.
        * rewrite -H5 in H14.
          move : (H6 q{2} H14) => [ws_def _ ].
          rewrite ws_def oget_some //=.
        * rewrite -H5 in H14.
          move : (H6 q{2} H14) => [ws_def _ ].
          rewrite ws_def oget_some nth_last //=.
        * rewrite -H5 in H14.
          move : (H6 q{2} H14) => [ws_def _ ].
          rewrite ws_def oget_some //=.
          + smt.
          + smt.
          + smt.
          + smt.
          + smt.
          + smt.
          + smt.
          + smt.
          + smt.
          + smt.
          + smt.
          + smt.
          + smt.
          + smt.
          + smt.
          + smt.
        * rewrite -H5 in H14.
          move : (H10 q{2} H14) => [_ [_ [_ [pre_c _] ]]].
          move : (pre_c c0).
          rewrite H48 H49 /=.
          move => [concl [_ [rwme _] ]].
          rewrite domE rwme -domE concl.
        * rewrite -H5 in H14.
          move : (H10 q{2} H14) => [_ [_ [_ [pre_c _] ]]].
          move : (pre_c c0).
          rewrite H48 H49 /=.
          move => [_ [concl [_ rwme] ]].
          rewrite domE rwme -domE concl.
          + smt.
          + smt.
if => //. wp; skip; progress.
apply H9 => //.
inline*.
    + (* The server does something *)
      wp; while ((0 <= i <= c + 1){2}
            /\ ={q, qo, kw, t, c, r, i}
            /\ ={glob RF, glob G4_Server}
            /\ (RF.m.[q] = Some kw){2}
            /\ (dom G5_Client.ws q){2}
            /\ (let sc = (oget G5_Client.ws.[q]){2} in
                   (0 < size sc){2}
                /\ (c = size sc - 1){2}
                /\ (i <= c => t = nth witness sc (c - i)){2}
                /\ (forall j, 0 < j <= c => nth witness sc (j - 1) = forward G4_Server.pk (nth witness sc j)){2}
                /\ (!dom G5_Client.utt (q, size sc)){2}
                /\ (forall j, 0 <= j <= c =>
                         dom G5_Client.utt (q, j)
                      /\ dom G5_Client.et (q, j)
                      /\ RO1.m{1}.[(kw, nth witness sc j)] = G5_Client.utt.[(q, j)]
                      /\ RO1.m{1}.[(kw, nth witness sc j)] = G5_Client.h1t.[(kw, nth witness sc j)]
                      /\ RO2.m{1}.[(kw, nth witness sc j)] = G5_Client.et.[(q, j)]
                      /\ RO2.m{1}.[(kw, nth witness sc j)] = G5_Client.h2t.[(kw, nth witness sc j)]
                   ){2}
               )
               (* UPDATE ASSUMPTIONS *)
            /\   (glob RF, glob G4_Server, G4_Client.sk){1}
               = (glob RF, glob G4_Server, G5_Client.sk){2}
            /\ (forall w c, dom G5_Client.utt (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO1.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.utt.[(w, c)]){2}
            /\ (forall w c, dom G5_Client.et (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO2.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.et.[(w, c)]){2}
            /\ (forall w c, !dom G5_Client.utt (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h1t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO1.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall w c, !dom G5_Client.et (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h2t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO2.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall kw s, dom RO1.m{1} (kw, s) => (RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO1.m{1}.[(kw, s)] = G5_Client.utt.[(w, c)])){2}
            /\ (forall kw s, dom RO2.m{1} (kw, s) => (RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO2.m{1}.[(kw, s)] = G5_Client.et.[(w, c)])){2}
            /\ (forall w, dom G4_Client.ws{1} w <=> dom G5_Client.ws{2} w)
            /\ (forall w, dom G4_Client.ws{1} w =>
                     G4_Client.ws{1}.[w] = Some (last witness (oget G5_Client.ws.[w]), size (oget G5_Client.ws.[w]) - 1)
                 /\ (forall c, (!0 <= c < size (oget G5_Client.ws.[w])) => !dom G5_Client.utt (w, c) /\ !dom G5_Client.et (w, c))
               ){2}
            /\ (forall w, !dom RF.m w => !dom G5_Client.ws w){2}
            /\ (forall kw, !rng RF.m kw => forall s, RO1.m.[(kw, s)] = G5_Client.h1t{2}.[(kw, s)] /\ RO2.m.[(kw, s)] = G5_Client.h2t{2}.[(kw, s)]){1} (* if neither update or search have been ever called in the past... *)
            /\ (!G5_Client.bad_rf_coll{2} => !fmap_collision RF.m){1}
               (* SEARCH ASSUMPTIONS *)
            /\ (forall w, dom G4_Client.ws{1} w => (let sc = oget G5_Client.ws.[w] in
                       0 < size sc
                    /\ !dom G5_Client.utt (w, size sc)
                    /\ !dom G5_Client.et (w, size sc)
                    /\ (forall c, 0 <= c < size sc =>
                             dom G5_Client.utt (w, c)
                          /\ dom G5_Client.et (w, c)
                          /\ RO1.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.utt.[(w, c)]
                          /\ RO2.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.et.[(w, c)]
                       )
                    /\ (forall c, 0 < c < size sc => nth witness sc (c - 1) = forward G4_Server.pk (nth witness sc c))
                 )
               ){2}
               (* O(RACLES) ASSUMPTIONS *)
            /\ (forall kw s, dom G5_Client.h1t (kw, s) => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]){2}
            /\ (forall kw s, dom G5_Client.h2t (kw, s) => RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (forall kw s,
                  let g = fun (_: query) (k: mapquery) => k = kw in
                  let qs = fdom (filter g RF.m) in
                  let f = fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts in
                  filter f G5_Client.ws = empty => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)] /\ RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (dom RF.m q /\ dom G5_Client.ws q /\ kw = oget RF.m.[q] /\ let sc = oget G5_Client.ws.[q] in qo = Some (kw, last witness sc, size sc - 1) /\ (forall s c, 0 <= c < size sc => s = nth witness sc c => dom RO1.m{1} (kw, s) /\ dom RO2.m{1} (kw, s) /\ RO1.m{1}.[(kw, s)] = G5_Client.h1t{2}.[(kw, s)] /\ RO2.m{1}.[(kw, s)] = G5_Client.h2t{2}.[(kw, s)])){2}
      ) => //.
        rcondf{1} 4; progress.
          rnd; wp; skip; progress.
          pose sc := (oget G5_Client.ws.[q]){m};
            pose kw := (oget RF.m.[q]){m};
            pose c := size sc - 1.
          move : H4 (H7 (c - i{m})).
          have ->: 0 <= c - i{m} <= c by smt.
          have ->: i{m} <= c by smt.
          rewrite /=.
          move => t_def [utt_qc] [et_qc] [rwme] _.
          rewrite t_def domE rwme //.
        kill{1} 3; first by progress; first by rnd; skip; progress; smt.
        rcondf{2} 3; progress.
          wp; skip; progress.
          pose sc := (oget G5_Client.ws.[q]){hr};
            pose kw := (oget RF.m.[q]){hr};
            pose c := size sc - 1.
          move : (H7 (c - i{hr})).
          smt.
        rcondf{1} 8; progress.
          rnd; wp; skip; progress.
          pose sc := (oget G5_Client.ws.[q]){m};
            pose kw := (oget RF.m.[q]){m};
            pose c := size sc - 1.
          move : H4 (H7 (c - i{m})).
          have ->: 0 <= c - i{m} <= c by smt.
          have ->: i{m} <= c by smt.
          rewrite /=.
          move => t_def [utt_qc] [et_qc] [_] [_] [rwme] _.
          rewrite t_def domE rwme //.
        kill{1} 7; first by progress; first by rnd; skip; progress; smt.
        rcondf{2} 6; progress.
          wp; skip; progress.
          pose sc := (oget G5_Client.ws.[q]){hr};
            pose kw := (oget RF.m.[q]){hr};
            pose c := size sc - 1.
          move : (H7 (c - i{hr})).
          smt.
        wp; skip; progress; smt.
      wp; skip; progress.
      + move : H14; rewrite H15 /=.
        move => [f_q] [ws_q] [qo_def].
        smt.
      + move : H14; rewrite H15 /=.
        move => [f_q] [ws_q] [qo_def].
        rewrite qo_def /= oget_some //= -some_oget //.
      + move : H14; rewrite H15 //=.
      + move : H14; rewrite H15 /=.
        move => [f_q] [ws_q] [qo_def] _.
        move : (H10 q{2}). 
        rewrite H5 ws_q /=.
        move => [concl] _.
        exact concl.
      + move : H14; rewrite H15 /=.
        move => [f_q] [ws_q] [qo_def].
        rewrite qo_def /= oget_some //= -some_oget //.
      + move : H14; rewrite H15 /=.
        move => [f_q] [ws_q] [qo_def] pre_s_c.
        rewrite qo_def /= oget_some //= nth_last //.
      + move : H14; rewrite H15 /=.
        move => [f_q] [ws_q] [qo_def] _.
        move : (H10 q{2}). 
        rewrite H5 ws_q /=.
        move => [_] [_] [_] [_] pre_c.
        move : (pre_c j).
        smt.
      + smt.
      + move : H14; rewrite H15 /=.
        move => [f_q] [ws_q] [qo_def] _.
        move : (H10 q{2}). 
        rewrite H5 ws_q /=.
        move => [_] [_] [_] [pre_c] _.
        move : (pre_c j).
        smt.
      + move : H14; rewrite H15 /=.
        move => [f_q] [ws_q] [qo_def] _.
        move : (H10 q{2}).
        rewrite H5 ws_q /=.
        move => [_] [_] [_] [pre_c] _.
        move : (pre_c j).
        smt.
      + move : H14; rewrite H15 /=.
        move => [f_q] [ws_q] [qo_def] _.
        move : (H10 q{2}).
        rewrite H5 ws_q /=.
        move => [_] [_] [_] [pre_c] _.
        move : (pre_c j).
        smt.
      + move : H14; rewrite H15 /=.
        move => [f_q] [ws_q] [qo_def] pre.
        rewrite qo_def /= oget_some //=.
        move : (pre (nth witness (oget G5_Client.ws{2}.[q{2}]) j) j).
        have ->: 0 <= j < size (oget G5_Client.ws{2}.[q{2}]) by smt.
        rewrite /=.
        move => [_] [_] [concl] _.
        exact concl.
      + move : H14; rewrite H15 /=.
        move => [f_q] [ws_q] [qo_def] _.
        move : (H10 q{2}). 
        rewrite H5 ws_q /=.
        move => [_] [_] [_] [pre_c] _.
        move : (pre_c j).
        smt.
      + move : H14; rewrite H15 /=.
        move => [f_q] [ws_q] [qo_def] pre.
        rewrite qo_def /= oget_some //=.
        move : (pre (nth witness (oget G5_Client.ws{2}.[q{2}]) j) j).
        have ->: 0 <= j < size (oget G5_Client.ws{2}.[q{2}]) by smt.
        rewrite /=.
        move => [_] [_] [_] concl.
        exact concl.
      + move : H14; rewrite H15 //=.
      + move : H14; rewrite H15 //=.
      + move : H14; rewrite H15 //=.
      + move : H14; rewrite H15 //=.
      + move : H14; rewrite H15 /=.
        move => [f_q] [ws_q] [qo_def] pre.
        rewrite qo_def /= oget_some //=.
        move : (pre (nth witness (oget G5_Client.ws{2}.[q{2}]) c2) c2).
        rewrite H16 H17 //.
      + move : H14; rewrite H15 /=.
        move => [f_q] [ws_q] [qo_def] pre.
        rewrite qo_def /= oget_some //=.
        move : (pre (nth witness (oget G5_Client.ws{2}.[q{2}]) c2) c2).
        rewrite H16 H17 //.
      + move : H14; rewrite H15 /=.
        move => [f_q] [ws_q] [qo_def].
        rewrite qo_def oget_some /= => pre.
        move : (pre (nth witness (oget G5_Client.ws{2}.[q{2}]) c2) c2).
        rewrite H16 H17 //.
      + move : H14; rewrite H15 /=.
        move => [f_q] [ws_q] [qo_def].
        rewrite qo_def oget_some /= => pre.
        move : (pre (nth witness (oget G5_Client.ws{2}.[q{2}]) c2) c2).
        rewrite H16 H17 //.
      + apply H38 => //.
  qed.

  lemma eq_G4_G5_no_bad_events_hash_consistency:
    equiv[G4.o ~ G5.o:
          ={oin}
               (* UPDATE ASSUMPTIONS *)
            /\   (glob RF, glob G4_Server, G4_Client.sk){1}
               = (glob RF, glob G4_Server, G5_Client.sk){2}
            /\ (forall w c, dom G5_Client.utt (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO1.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.utt.[(w, c)]){2}
            /\ (forall w c, dom G5_Client.et (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO2.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.et.[(w, c)]){2}
            /\ (forall w c, !dom G5_Client.utt (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h1t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO1.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall w c, !dom G5_Client.et (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h2t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO2.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall kw s, dom RO1.m{1} (kw, s) => (RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO1.m{1}.[(kw, s)] = G5_Client.utt.[(w, c)])){2}
            /\ (forall kw s, dom RO2.m{1} (kw, s) => (RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO2.m{1}.[(kw, s)] = G5_Client.et.[(w, c)])){2}
            /\ (forall w, dom G4_Client.ws{1} w <=> dom G5_Client.ws{2} w)
            /\ (forall w, dom G4_Client.ws{1} w =>
                     G4_Client.ws{1}.[w] = Some (last witness (oget G5_Client.ws.[w]), size (oget G5_Client.ws.[w]) - 1)
                 /\ (forall c, (!0 <= c < size (oget G5_Client.ws.[w])) => !dom G5_Client.utt (w, c) /\ !dom G5_Client.et (w, c))
               ){2}
            /\ (forall w, !dom RF.m w => !dom G5_Client.ws w){2}
            /\ (forall kw, !rng RF.m kw => forall s, RO1.m.[(kw, s)] = G5_Client.h1t{2}.[(kw, s)] /\ RO2.m.[(kw, s)] = G5_Client.h2t{2}.[(kw, s)]){1} (* if neither update or search have been ever called in the past... *)
            /\ (!fmap_collision RF.m){1}
               (* SEARCH ASSUMPTIONS *)
            /\ (forall w, dom G4_Client.ws{1} w => (let sc = oget G5_Client.ws.[w] in
                       0 < size sc
                    /\ !dom G5_Client.utt (w, size sc)
                    /\ !dom G5_Client.et (w, size sc)
                    /\ (forall c, 0 <= c < size sc =>
                             dom G5_Client.utt (w, c)
                          /\ dom G5_Client.et (w, c)
                          /\ RO1.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.utt.[(w, c)]
                          /\ RO2.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.et.[(w, c)]
                       )
                    /\ (forall c, 0 < c < size sc => nth witness sc (c - 1) = forward G4_Server.pk (nth witness sc c))
                 )
               ){2}
               (* O(RACLES) ASSUMPTIONS *)
            /\ (forall kw s, dom G5_Client.h1t (kw, s) => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]){2}
            /\ (forall kw s, dom G5_Client.h2t (kw, s) => RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (forall kw s,
                  let g = fun (_: query) (k: mapquery) => k = kw in
                  let qs = fdom (filter g RF.m) in
                  let f = fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts in
                  filter f G5_Client.ws = empty => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)] /\ RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
          ==> (!G5_Client.bad_h1 /\ !G5_Client.bad_h2){2} => (={res}
               (* UPDATE ASSUMPTIONS *)
            /\   (glob RF, glob G4_Server, G4_Client.sk){1}
               = (glob RF, glob G4_Server, G5_Client.sk){2}
            /\ (forall w c, dom G5_Client.utt (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO1.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.utt.[(w, c)]){2}
            /\ (forall w c, dom G5_Client.et (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO2.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.et.[(w, c)]){2}
            /\ (forall w c, !dom G5_Client.utt (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h1t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO1.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall w c, !dom G5_Client.et (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h2t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO2.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall kw s, dom RO1.m{1} (kw, s) => (RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO1.m{1}.[(kw, s)] = G5_Client.utt.[(w, c)])){2}
            /\ (forall kw s, dom RO2.m{1} (kw, s) => (RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO2.m{1}.[(kw, s)] = G5_Client.et.[(w, c)])){2}
            /\ (forall w, dom G4_Client.ws{1} w <=> dom G5_Client.ws{2} w)
            /\ (forall w, dom G4_Client.ws{1} w =>
                     G4_Client.ws{1}.[w] = Some (last witness (oget G5_Client.ws.[w]), size (oget G5_Client.ws.[w]) - 1)
                 /\ (forall c, (!0 <= c < size (oget G5_Client.ws.[w])) => !dom G5_Client.utt (w, c) /\ !dom G5_Client.et (w, c))
               ){2}
            /\ (forall w, !dom RF.m w => !dom G5_Client.ws w){2}
            /\ (forall kw, !rng RF.m kw => forall s, RO1.m.[(kw, s)] = G5_Client.h1t{2}.[(kw, s)] /\ RO2.m.[(kw, s)] = G5_Client.h2t{2}.[(kw, s)]){1} (* if neither update or search have been ever called in the past... *)
            /\ (!fmap_collision RF.m){1}
               (* SEARCH ASSUMPTIONS *)
            /\ (forall w, dom G4_Client.ws{1} w => (let sc = oget G5_Client.ws.[w] in
                       0 < size sc
                    /\ !dom G5_Client.utt (w, size sc)
                    /\ !dom G5_Client.et (w, size sc)
                    /\ (forall c, 0 <= c < size sc =>
                             dom G5_Client.utt (w, c)
                          /\ dom G5_Client.et (w, c)
                          /\ RO1.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.utt.[(w, c)]
                          /\ RO2.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.et.[(w, c)]
                       )
                    /\ (forall c, 0 < c < size sc => nth witness sc (c - 1) = forward G4_Server.pk (nth witness sc c))
                 )
               ){2}
               (* O(RACLES) ASSUMPTIONS *)
            /\ (forall kw s, dom G5_Client.h1t (kw, s) => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]){2}
            /\ (forall kw s, dom G5_Client.h2t (kw, s) => RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (forall kw s,
                  let g = fun (_: query) (k: mapquery) => k = kw in
                  let qs = fdom (filter g RF.m) in
                  let f = fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts in
                  filter f G5_Client.ws = empty => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)] /\ RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
      )
    ].
  proof.
    proc.
    sp; if => //.
    + (* HASH1 *)
      inline *.
      case ((dom G5_Client.h1t argv){2}).
      + rcondf{2} 2; first by progress; first by wp; skip; progress; smt.
        rcondf{1} 4; first by progress; first by rnd; wp; skip; progress; smt.
        wp; rnd{1}; wp; skip; progress; smt.
      + rcondt{2} 2; first by progress; first by wp; skip; progress; smt.
        sp; if{2}.
        + (* Bad event related to some smart adversary *)
          wp; rnd{1}; skip; progress; smt.
        + (* Here we cannot have the value even in the real setting *)
          rcondt{1} 2; first by progress; first by rnd; skip; progress; rewrite domE /= in H14; move : (H13 kw{m} s{m}); rewrite H15 H14 //.
          wp; rnd; skip; progress.
          * smt(dut_ll).
          * smt.
          * smt.
          * smt.
          * smt.
          * smt.
          * pose kw0 := oget RF.m{2}.[w0];
              pose s0 := nth witness (oget G5_Client.ws{2}.[w0]) c0.
            have x0x: ((kw0, s0) <> (kw, s){2}).

move : H15.
apply absurd => //=.
rewrite andaE.
move => [kw0kw s0s].
rewrite -fmap_eqP negb_forall /=.
exists w0.
rewrite filterE.
move : (H w0 c0).
rewrite H21 /=.
move => [ws_w0] [c0_range] [f_w0] _.
move : ws_w0.
rewrite dom_exists.
move => [y] y_def.
rewrite y_def /= mem_fdom dom_filter f_w0 /=.
have ->: has ((=) s{2}) y.
  rewrite hasP.
  exists s{2}.
have ->: y = oget (G5_Client.ws{2}.[w0]) by rewrite y_def //.
rewrite -s0s mem_nth //.
rewrite -kw0kw /kw0 emptyE //=.
rewrite get_set_neqE //.
            move : (H w0 c0).
            rewrite H21 /=.
            move => [_] [_] [_] concl.
            exact concl.
          * smt.

move : H21.
case ((kw0, s0) = (kw, s){2}) => x0x.
+ rewrite x0x 2!get_set_sameE //.
+ rewrite mem_set x0x /= => f_x.
  rewrite get_set_neqE // get_set_neqE //.
  apply H3 => //.

          * smt.
          * smt.
          * smt.
          * smt.
          * smt.
          * smt.
          * smt.

have no_match: (RF.m.[w0] <> Some kw \/ (!has ((=) s) (oget G5_Client.ws.[w0]))){2}.
rewrite filter_nil in H15.
move : (H15 w0).
rewrite -H5 H21 /= negb_and.
case (! has ((=) s{2}) (oget G5_Client.ws.[w0]){2}) => //= s_found.
apply absurd => //= ah.
rewrite mem_fdom dom_filter /=.
rewrite ah oget_some domE ah //.
pose sc := (oget G5_Client.ws{2}.[w0]).
have x0x: ((oget RF.m.[w0], nth witness sc c0) <> (kw, s)){2}.
  move : no_match.
  apply absurd.
  rewrite /= andaE.
  move => [kw0kw s0s].
  move : (H7 w0).
  rewrite implybNN -H5 H21 /= => f_w0.
  rewrite -kw0kw -s0s -some_oget //=.
  rewrite hasP.
  exists s{2}.
  rewrite s0s /= -s0s mem_nth H22 H23 //.
rewrite get_set_neqE //.
move : (H10 w0).
rewrite H21 /=.
move => [_] [_] [_] [pre_c] _.
move : (pre_c c0).
rewrite H22 H23 /=.
move => [_] [_] [concl] _.
exact concl.
move : (H10 w0).
rewrite H21 /=.
move => [_] [_] [_] [pre_c] _.
move : (pre_c c0).
rewrite H22 H23 /=.
move => [_] [_] [_] concl.
exact concl.

move : (H10 w0).
rewrite H21 /=.
move => [_] [_] [_] [_] pre_c.
move : (pre_c c0).
rewrite H22 H23 //=.

move : H21.
case ((kw0, s0) = (kw, s){2}) => x0x.
+ rewrite x0x 2!get_set_sameE //.
+ rewrite mem_set x0x /= => h1t_x0.
  rewrite get_set_neqE // get_set_neqE //.
  apply H11 => //.

move : (H13 kw0 s0).
rewrite H21 /=.
move => [concl0] _.
move : (H13 kw{2} s{2}).
rewrite H15 /=.
move => [concl] _.
smt.
move : (H13 kw0 s0).
rewrite H21 /=.
move => [_] concl0.
move : (H13 kw{2} s{2}).
rewrite H15 /=.
move => [_] concl.
smt.

    + if => //.
    + (* HASH2 *)
      inline *.
      case ((dom G5_Client.h2t argv){2}).
      + rcondf{2} 2; first by progress; first by wp; skip; progress; smt.
        rcondf{1} 4; first by progress; first by rnd; wp; skip; progress; smt.
        wp; rnd{1}; wp; skip; progress; smt.
      + rcondt{2} 2; first by progress; first by wp; skip; progress; smt.
        sp; if{2}.
        + (* Bad event related to some smart adversary *)
          wp; rnd{1}; skip; progress; smt.
        + (* Here we cannot have the value even in the real setting *)
          rcondt{1} 2; first by progress; first by rnd; skip; progress; rewrite domE /= in H15; move : (H13 kw{m} s{m}); rewrite H16 H15 //.
          wp; rnd; skip; progress.
          * smt(dut_ll).
          * smt.
          * smt.
          * smt.
          * smt.
          * smt.
          * pose kw0 := oget RF.m{2}.[w0];
              pose s0 := nth witness (oget G5_Client.ws{2}.[w0]) c0.
            have x0x: ((kw0, s0) <> (kw, s){2}).

move : H16.
apply absurd => //=.
rewrite andaE.
move => [kw0kw s0s].
rewrite -fmap_eqP negb_forall /=.
exists w0.
rewrite filterE.
move : (H0 w0 c0).
rewrite H22 /=.
move => [ws_w0] [c0_range] [f_w0] _.
move : ws_w0.
rewrite dom_exists.
move => [y] y_def.
rewrite y_def /= mem_fdom dom_filter f_w0 /=.
have ->: has ((=) s{2}) y.
  rewrite hasP.
  exists s{2}.
have ->: y = oget (G5_Client.ws{2}.[w0]) by rewrite y_def //.
rewrite -s0s mem_nth //.
rewrite -kw0kw /kw0 emptyE //=.
rewrite get_set_neqE //.
            move : (H0 w0 c0).
            rewrite H22 /=.
            move => [_] [_] [_] concl.
            exact concl.
          * smt.

move : H22.
case ((kw0, s0) = (kw, s){2}) => x0x.
+ rewrite x0x 2!get_set_sameE //.
+ rewrite mem_set x0x /= => f_x.
  rewrite get_set_neqE // get_set_neqE //.
  apply H4 => //.

          * smt.
          * smt.
          * smt.
          * smt.
          * smt.
          * smt.
          * smt.

have no_match: (RF.m.[w0] <> Some kw \/ (!has ((=) s) (oget G5_Client.ws.[w0]))){2}.
rewrite filter_nil in H16.
move : (H16 w0).
rewrite -H5 H22 /= negb_and.
case (! has ((=) s{2}) (oget G5_Client.ws.[w0]){2}) => //= s_found.
apply absurd => //= ah.
rewrite mem_fdom dom_filter /=.
rewrite ah oget_some domE ah //.
pose sc := (oget G5_Client.ws{2}.[w0]).
have x0x: ((oget RF.m.[w0], nth witness sc c0) <> (kw, s)){2}.
  move : no_match.
  apply absurd.
  rewrite /= andaE.
  move => [kw0kw s0s].
  move : (H7 w0).
  rewrite implybNN -H5 H22 /= => f_w0.
  rewrite -kw0kw -s0s -some_oget //=.
  rewrite hasP.
  exists s{2}.
  rewrite s0s /= -s0s mem_nth H23 H24 //.
move : (H10 w0).
rewrite H22 /=.
move => [_] [_] [_] [pre_c] _.
move : (pre_c c0).
rewrite H23 H24 /=.
move => [_] [_] [concl] _.
exact concl.

have no_match: (RF.m.[w0] <> Some kw \/ (!has ((=) s) (oget G5_Client.ws.[w0]))){2}.
rewrite filter_nil in H16.
move : (H16 w0).
rewrite -H5 H22 /= negb_and.
case (! has ((=) s{2}) (oget G5_Client.ws.[w0]){2}) => //= s_found.
apply absurd => //= ah.
rewrite mem_fdom dom_filter /=.
rewrite ah oget_some domE ah //.
pose sc := (oget G5_Client.ws{2}.[w0]).
have x0x: ((oget RF.m.[w0], nth witness sc c0) <> (kw, s)){2}.
  move : no_match.
  apply absurd.
  rewrite /= andaE.
  move => [kw0kw s0s].
  move : (H7 w0).
  rewrite implybNN -H5 H22 /= => f_w0.
  rewrite -kw0kw -s0s -some_oget //=.
  rewrite hasP.
  exists s{2}.
  rewrite s0s /= -s0s mem_nth H23 H24 //.
rewrite get_set_neqE //.
move : (H10 w0).
rewrite H22 /=.
move => [_] [_] [_] [pre_c] _.
move : (pre_c c0).
rewrite H23 H24 /=.
move => [_] [_] [_] concl.
exact concl.

move : (H10 w0).
rewrite H22 /=.
move => [_] [_] [_] [_] pre_c.
move : (pre_c c0).
rewrite H23 H24 //=.

move : H22.
case ((kw0, s0) = (kw, s){2}) => x0x.
+ rewrite x0x 2!get_set_sameE //.
+ rewrite mem_set x0x /= => h2t_x0.
  rewrite get_set_neqE // get_set_neqE //.
  apply H12 => //.

move : (H13 kw0 s0).
rewrite H22 /=.
move => [concl] _.
exact concl.
move : (H13 kw0 s0).
rewrite H22 /=.
move => [_] concl0.
move : (H13 kw{2} s{2}).
rewrite H16 /=.
move => [_] concl.
case ((kw0, s0) = (kw, s){2}) => x0x.
+ rewrite x0x 2!get_set_sameE //.
+ rewrite get_set_neqE // get_set_neqE //.
  qed.

  lemma G4_G5_indistinguishable_uptobad
    (D <: SSEDistROM{RO2,RO1,RF,G4,G5,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
    (RO1.m, RO2.m){m} = (empty, empty) =>
    Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(true) @ &m : res] <= Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : res] + Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : !(!G5_Client.bad_rf_coll /\ !G5_Client.bad_update_h1t /\ !G5_Client.bad_update_h2t /\ !G5_Client.bad_update_bt /\ !G5_Client.bad_h1 /\ !G5_Client.bad_h2)].
  proof.
move : dut_ll di_ll dmapquery_ll dstoken_ll dkey_ll; rewrite /is_lossless => _ _ _ _ _.
    move => oracle_termination_implies_distinguisher_termination.
    rewrite pairS /=; move => [empty_hashro1 empty_hashro2].
    byequiv => //=.
    proc. 
rcondt{1} 1 => //.
rcondf{2} 1 => //.
inline*; wp.
 call (_: !(!G5_Client.bad_rf_coll /\ !G5_Client.bad_update_h1t /\ !G5_Client.bad_update_h2t /\ !G5_Client.bad_update_bt /\ !G5_Client.bad_h1 /\ !G5_Client.bad_h2),
            ={glob OracleCallsCounter}
               (* UPDATE ASSUMPTIONS *)
            /\   (glob RF, glob G4_Server, G4_Client.sk){1}
               = (glob RF, glob G4_Server, G5_Client.sk){2}
            /\ (forall w c, dom G5_Client.utt (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO1.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.utt.[(w, c)]){2}
            /\ (forall w c, dom G5_Client.et (w, c) => dom G5_Client.ws w /\ 0 <= c < size (oget G5_Client.ws.[w]) /\ dom RF.m w /\ RO2.m{1}.[(oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)] = G5_Client.et.[(w, c)]){2}
            /\ (forall w c, !dom G5_Client.utt (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h1t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO1.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall w c, !dom G5_Client.et (w, c) => dom RF.m w => dom G5_Client.ws w => !dom G5_Client.h2t (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c) => !dom RO2.m{1} (oget RF.m.[w], nth witness (oget G5_Client.ws.[w]) c)){2}
            /\ (forall kw s, dom RO1.m{1} (kw, s) => (RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO1.m{1}.[(kw, s)] = G5_Client.utt.[(w, c)])){2}
            /\ (forall kw s, dom RO2.m{1} (kw, s) => (RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]) \/ (exists sc w c, G5_Client.ws.[w] = Some sc /\ 0 <= c < size sc /\ s = nth witness sc c /\ RF.m{1}.[w] = Some kw /\ RO2.m{1}.[(kw, s)] = G5_Client.et.[(w, c)])){2}
            /\ (forall w, dom G4_Client.ws{1} w <=> dom G5_Client.ws{2} w)
            /\ (forall w, dom G4_Client.ws{1} w =>
                     G4_Client.ws{1}.[w] = Some (last witness (oget G5_Client.ws.[w]), size (oget G5_Client.ws.[w]) - 1)
                 /\ (forall c, (!0 <= c < size (oget G5_Client.ws.[w])) => !dom G5_Client.utt (w, c) /\ !dom G5_Client.et (w, c))
               ){2}
            /\ (forall w, !dom RF.m w => !dom G5_Client.ws w){2}
            /\ (forall kw, !rng RF.m kw => forall s, RO1.m.[(kw, s)] = G5_Client.h1t{2}.[(kw, s)] /\ RO2.m.[(kw, s)] = G5_Client.h2t{2}.[(kw, s)]){1} (* if neither update or search have been ever called in the past... *)
            /\ (!fmap_collision RF.m){1}
               (* SEARCH ASSUMPTIONS *)
            /\ (forall w, dom G4_Client.ws{1} w => (let sc = oget G5_Client.ws.[w] in
                       0 < size sc
                    /\ !dom G5_Client.utt (w, size sc)
                    /\ !dom G5_Client.et (w, size sc)
                    /\ (forall c, 0 <= c < size sc =>
                             dom G5_Client.utt (w, c)
                          /\ dom G5_Client.et (w, c)
                          /\ RO1.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.utt.[(w, c)]
                          /\ RO2.m{1}.[(oget RF.m{1}.[w], nth witness sc c)] = G5_Client.et.[(w, c)]
                       )
                    /\ (forall c, 0 < c < size sc => nth witness sc (c - 1) = forward G4_Server.pk (nth witness sc c))
                 )
               ){2}
               (* O(RACLES) ASSUMPTIONS *)
            /\ (forall kw s, dom G5_Client.h1t (kw, s) => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)]){2}
            /\ (forall kw s, dom G5_Client.h2t (kw, s) => RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
            /\ (forall kw s,
                  let g = fun (_: query) (k: mapquery) => k = kw in
                  let qs = fdom (filter g RF.m) in
                  let f = fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts in
                  filter f G5_Client.ws = empty => RO1.m{1}.[(kw, s)] = G5_Client.h1t.[(kw, s)] /\ RO2.m{1}.[(kw, s)] = G5_Client.h2t.[(kw, s)]){2}
      ) => //=.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: update
 *)
proc.
sp; if => //.
wp.
call eq_G4_G5_no_bad_events_update_consistency.
simplify.
skip; progress;
move : H36; rewrite H37 H38 H39 H40 andaE -andbA /=; move => [same_output] [same_memory] [same_edb] [th1] [th2] [th3] [th4] [th5] [th6] [th7] [th8] [th9] [th10] [th11] [th12] [th13] last_chunk => //; first 32 by smt.
move : last_chunk; move => [th14] th15.
move : (th15 kw s); rewrite H43 //.
move : last_chunk; move => [th14] th15.
move : (th15 kw s); rewrite H43 //.
(*
 * The update call in the real world is required to terminate
 *)
progress.
proc.
inline*.
sp; if => //.
wp => /=.
sp; if => //; last by wp; skip; progress.
wp; kill 14; first by rnd; skip; progress.
wp; kill 8; first by rnd; skip; progress.
wp => /=.
seq 3 : (true) => //.
  wp; sp; if => //; rnd; skip; progress.
if => //.
+ wp; rnd; skip; progress.
+ wp; skip; progress.
(*
 * update called in the bad-event state does not affect the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: !(!G5_Client.bad_rf_coll /\ !G5_Client.bad_update_h1t /\ !G5_Client.bad_update_h2t /\ !G5_Client.bad_update_bt /\ !G5_Client.bad_h1 /\ !G5_Client.bad_h2)) => //.
kill 2; first by if => //; inline*; wp; skip; progress.
inline*.
sp; if => //; last by wp; skip; progress.
sp; if => //.
  * seq 2: (!(!G5_Client.bad_rf_coll /\ !G5_Client.bad_update_h1t /\ !G5_Client.bad_update_h2t /\ !G5_Client.bad_update_bt /\ !G5_Client.bad_h1 /\ !G5_Client.bad_h2)) => //; last by hoare; wp; rnd; skip; progress.
      wp; rnd; skip; progress.
    sp; if => //; first by wp; skip; progress.
    if => //.
    - seq 2: (!(!G5_Client.bad_rf_coll /\ !G5_Client.bad_update_h1t /\ !G5_Client.bad_update_h2t /\ !G5_Client.bad_update_bt /\ !G5_Client.bad_h1 /\ !G5_Client.bad_h2)) => //; last by hoare; rnd; wp; skip; progress.
        rnd; wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress.
    - sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress.
  * sp; if => //; first by wp; skip; progress.
    if => //.
    - seq 2: (!(!G5_Client.bad_rf_coll /\ !G5_Client.bad_update_h1t /\ !G5_Client.bad_update_h2t /\ !G5_Client.bad_update_bt /\ !G5_Client.bad_h1 /\ !G5_Client.bad_h2)) => //; last by hoare; rnd; wp; skip; progress.
        rnd; wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress.
    - sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: query
 *)
proc.
sp; if => //.
wp.
call eq_G4_G5_no_bad_events_query_consistency.
simplify.
skip; progress;
move : H36; rewrite H37 /=; move => [same_output] [same_memory] [th1] [th2] [th3] [th4] [th5] [th6] [th7] [th8] [th9] [th10] [th11] [th12] [th13] th14 => //; first 27 by smt.
move : (th14 kw s); rewrite H43 //.
move : (th14 kw s); rewrite H43 //.
(*
 * The query call in the real world is required to terminate
 *)
progress.
proc.
inline*.
sp; if => //.
wp => /=.
kill 5.
  if => //; first by wp; skip; progress.
  case (0 <= (oget qo).`3).
  + wp => /=; sp; while (0 <= i <= c + 1) (c + 1 - i).
    * progress.
      wp; kill 9; first by rnd; skip; progress.
      wp; kill 3; first by rnd; skip; progress.
      wp => /=; skip; progress; smt.
    * skip; progress; smt.
  + rcondf 4; wp; skip; progress.
  wp; sp; if => //; first by wp; skip; progress.
  wp; sp; if => //; rnd; skip; progress.
(*
 * query called in the bad-event state must keep the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: !(!G5_Client.bad_rf_coll /\ !G5_Client.bad_update_h1t /\ !G5_Client.bad_update_h2t /\ !G5_Client.bad_update_bt /\ !G5_Client.bad_h1 /\ !G5_Client.bad_h2)) => //.
inline*.
sp; if => //; first by rcondt 3; wp; skip; progress.
rcondf 11.
  wp; while (0 <= i <= size sc); first by wp; skip; progress; smt.
  wp; sp; if => //.
  - wp; rnd; skip; progress; smt.
  - wp; skip; progress; smt.
wp; while (0 <= i0 <= c0 + 1 /\ !(!G5_Client.bad_rf_coll /\ !G5_Client.bad_update_h1t /\ !G5_Client.bad_update_h2t /\ !G5_Client.bad_update_bt /\ !G5_Client.bad_h1 /\ !G5_Client.bad_h2)) (c0 + 1 - i0); progress.
  wp; sp; if => //.
  wp; sp; if => //.
  wp; sp; if => //.
  wp; sp; if => //.
wp; skip; progress; smt.
wp; rnd; skip; progress; smt. 
wp; skip; progress; smt.
kill 3; first by wp; skip; progress.
kill 2; first by wp; skip; progress.
kill 1; first by wp; rnd; skip; progress.
sp; if => //.
sp; if => //.
wp; skip; progress.
wp; rnd; skip; progress; smt. 
skip; progress; smt.
sp; if => //.
sp; if => //.
wp; skip; progress; smt.
wp; rnd; skip; progress; smt. 
skip; progress; smt.
  wp; while (0 <= i) (size sc - i); progress; first by wp; skip; progress; smt.
  wp; sp; if => //.
  - wp; rnd (predT); skip; progress.
smt. 
rewrite oget_some get_set_sameE /= size_ge0 //. 
smt. 
smt. 
rewrite oget_some get_set_sameE /= size_ge0 //. 
smt. 
  - wp; skip; progress.
smt. 
rewrite oget_some /= size_ge0 //. 
smt. 
smt. 
rewrite oget_some /= size_ge0 //. 
smt. 
+
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: o
 *)
proc.
sp; if => //.
wp.
call eq_G4_G5_no_bad_events_hash_consistency.
simplify.
skip; progress.
(*
 * The o call in the real world is required to terminate
 *)
progress.
proc.
sp; if => //.
wp; inline*.
sp; if => //.
wp; rnd; wp; skip; progress.
sp; if => //.
wp; rnd; wp; skip; progress.
wp; skip; progress.
(*
 * o called in the bad-event state keeps the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: !(!G5_Client.bad_rf_coll /\ !G5_Client.bad_update_h1t /\ !G5_Client.bad_update_h2t /\ !G5_Client.bad_update_bt /\ !G5_Client.bad_h1 /\ !G5_Client.bad_h2)).
sp; if => //.
wp; inline*.
sp; if => //.
sp; if => //.
wp; skip; progress.
wp; rnd; skip; progress.
wp; skip; progress.
if => //.
inline *.
sp; if => //.
sp; if => //.
wp; skip; progress.
wp; rnd; wp; skip; progress.
wp; skip; progress.
skip; progress.
(*
 * No further procedures are left. Lastly, we need to prove that, in the meanwhile that the distinguisher does whatever she wants, the consistency, hence the indistinguishability, is kept in the case no bad events occur.
 *)
wp => /=; rnd; skip.
move => &1 &2. move => [_] [_] [_] [_] [_] [_] [_] [_] [_] [_] [_] [_] [_] _; subst => /=.
move => r rdom; rewrite rdom /=.
progress.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ rewrite mem_empty //.
+ rewrite /fmap_collision negb_exists /= => x.
  rewrite negb_exists /= => y.
  rewrite 2!negb_and mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H; rewrite mem_empty //.
+ move : H6; rewrite H7 H8 H9 H10 H11 H12 /=.
  move => [concl] _.
  rewrite -concl //.
  qed.

  local lemma ler_add2l (c a b: real): c + a <= c + b <=> a <= b by smt.

  lemma anybad_or_inequality  (D <: SSEDistROM{RO2,RO1,RF,G4,G5,OracleCallsCounter}) &m:
       Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : !(!G5_Client.bad_rf_coll /\ !G5_Client.bad_update_h1t /\ !G5_Client.bad_update_h2t /\ !G5_Client.bad_update_bt /\ !G5_Client.bad_h1 /\ !G5_Client.bad_h2)]
    <= Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_rf_coll]
    + Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_update_h1t]
    + Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_update_h2t]
    + Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_update_bt]
    + Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_h1]
    + Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_h2].
  proof.
    rewrite 5!negb_and 6!negbK -4!RField.addrA.
    rewrite Pr[mu_or] -RField.addrA ler_add2l.
    rewrite Pr[mu_or] -2!RField.addrA ler_add2l.
    rewrite Pr[mu_or] -2!RField.addrA ler_add2l.
    rewrite Pr[mu_or] -2!RField.addrA ler_add2l.
    rewrite Pr[mu_or] -2!RField.addrA ler_add2l.
    rewrite -RField.addr0 -RField.addrA ler_add2l.
    rewrite /=; smt.
  qed.

  local lemma ler_trans (y x z: real): x <= y => y <= z => x <= z by smt.

  lemma G4_G5_indistinguishable_uptobad_disjoint
    (D <: SSEDistROM{RO2,RO1,RF,G4,G5,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
    (RO1.m, RO2.m){m} = (empty, empty) =>
       Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(true) @ &m : res]
    <= Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : res]
    + Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_rf_coll]
    + Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_update_h1t]
    + Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_update_h2t]
    + Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_update_bt]
    + Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_h1]
    + Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_h2].
  proof.
    move => oracle_termination_implies_distinguisher_termination empty_hashes.
rewrite (ler_trans (Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : res] + Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : !(!G5_Client.bad_rf_coll /\ !G5_Client.bad_update_h1t /\ !G5_Client.bad_update_h2t /\ !G5_Client.bad_update_bt /\ !G5_Client.bad_h1 /\ !G5_Client.bad_h2)])).
    apply (G4_G5_indistinguishable_uptobad D &m oracle_termination_implies_distinguisher_termination empty_hashes).
    rewrite -5!RField.addrA ler_add2l 4!RField.addrA.
    apply (anybad_or_inequality D &m).
  qed.

  (*
   * === Part6 ===
   * We start not to handle the bad events, reducing to other experiments
   * -- bad_h2
   *)
  module G6_Client: SSEClient = {
    var sk: tau
    var ws: (query, stoken list) fmap

    var utt: (query * int, utoken) fmap
    var et: (query * int, index) fmap
    var h1t: (mapquery * stoken, utoken) fmap
    var h2t: (mapquery * stoken, index) fmap

    var bad_rf_coll: bool (* collision in the random function *)
    var bad_update_bt: bool (* prediction in backup tables *)
    var bad_update_h1t: bool (* guess in h1t *)
    var bad_update_h2t: bool (* guess in h2t *)
    var bad_h1: bool (* bad event raised by h1 *)
    var bad_h2: bool (* bad event raised by h2 *)

    proc setup(): setupserver = {
      var pk;

      (pk, sk) <@ CTP.index();
      RF.init();
      ws <- empty;
      utt <- empty;
      et <- empty;
      h1t <- empty;
      h2t <- empty;

      bad_rf_coll <- false;
      bad_update_bt <- false;
      bad_update_h1t <- false;
      bad_update_h2t <- false;
      bad_h1 <- false;
      bad_h2 <- false;

      return pk;
    }

    (* Simulating the hash functions *)
    module SimH1: HashFunction1 = {
      proc hash(kw: mapquery, s: stoken): utoken = {
        var c, ls, y, qs, cand_ws, w;

        if (!(dom h1t (kw, s))) {
          (*
           * Additional care when h1t is not synced with utt (i.e. update was not called before it)
           *)
          qs <- fdom (filter (fun (_: query) k => k = kw) RF.m); (* queries mapping to kw *)
          cand_ws <- filter (fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts) ws; (* occurrences in the ws map *)
          if (cand_ws <> empty) { (* occurrence found *)
            bad_h1 <- true;
            w <- last witness (elems (fdom cand_ws)); (* this element always exists, notice that listing cand_ws elements give results that equal up to permutation, so no guarantee to get the same value in maps with cardinality greater than one *)
            ls <- oget cand_ws.[w];
            c <- find ((=) s) ls;
            h1t.[(kw, s)] <- oget utt.[(w, c)];
          } else {
            y <$ dutoken;
            h1t.[(kw, s)] <- y;
          }
        }

        return oget h1t.[(kw, s)];
      }
    }

    module SimH2: HashFunction2 = {
      proc hash(kw: mapquery, s: stoken): index = {
        var y;

        if (!(dom h2t (kw, s))) {
          y <$ di;
          h2t.[(kw, s)] <- y;
        }

        return oget h2t.[(kw, s)];
      }
    }

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var kw, s, c, sc, idx, ti, qs, cand_ws;

      if (o = ADD) {
        kw <@ RF.f(q);
        if (fmap_collision RF.m) {
          bad_rf_coll <- true;
          ti <- None;
        } else {
          if (!dom ws q) {
            sc <- [];
            s <$ dstoken;
            c <- 0;
          } else {
            sc <- oget ws.[q];
            c <- size sc;
            s <@ CTP.backward(sk, last witness sc);
          }
          ws.[q] <- sc ++ [s];
          if (dom h1t (kw, s)) {
            (* Rare event: We do not expect this value to be called (read guessed) in the past if not for a negligible probability *)
            bad_update_h1t <- true;
            ti <- None;
          } else {
            if (dom h2t (kw, s)) {
              (* Rare event: We do not expect this value to be called (read guessed) in the past if not for a negligible probability *)
              bad_update_h2t <- true;
              ti <- None;
            } else {
              (*
              * Additional care when h1t/h2t is not synced with utt/et (i.e. utt/et already contains what h1t/h2t would contain in the future).
              * This is not a proper bad event: It happens naturally for any duplicates and in the real world is not an issue.
              *)
              qs <- fdom (filter (fun (_: query) k => k = kw) RF.m); (* queries mapping to kw *)
              cand_ws <- filter (fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts) ws; (* occurrences in the ws map *)
              if (cand_ws <> empty) { (* occurrence found *)
                (* This is also unlikely to happen *)
                bad_update_bt <- true;
                ti <- None;
              } else {
                utt.[(q, c)] <$ dutoken;
                idx <$ di;
                et.[(q, c)] <- idx;
                idx <- i +^ idx;
                ti <- Some(oget utt.[(q, c)], idx);
              }
            }
          }
        }
      } else {
        ti <- None;
      }
     
      return ti;
    }

    proc query(q: query): (mapquery * stoken * int) option = {
      var kw, sc, c, i, s;
      var r: (mapquery * stoken * int) option;

      if (!dom ws q) {
        r <- None;
      } else {
        kw <@ RF.f(q);
        if (fmap_collision RF.m) {
          bad_rf_coll <- true;
        }

        sc <- oget ws.[q];
        c <- size sc - 1;
        r <- Some (kw, nth witness sc c, c);

        (* Lazily programming the hash tables *)
        i <- 0;
        while (i < size sc) {
          s <- nth witness sc i;
          h1t.[(kw, s)] <- oget utt.[(q, i)];
          h2t.[(kw, s)] <- oget et.[(q, i)];
          i <- i + 1;
        }
      }

      return r;
    }

    proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
      var h1, h2, h;

      h <- None;
      if     (i = HASH1) {
        h1 <@ SimH1.hash(argv);
        h <- Some(Some(h1), None);
      } elif (i = HASH2) {
        h2 <@ SimH2.hash(argv);
        h <- Some(None, Some(h2));
      }

      return h;
    }
  }.

  module G6 = SSEProtocol(G6_Client, G4_Server(G6_Client.SimH1, G6_Client.SimH2)).

  lemma G6_setup_ll:
    is_lossless dcoins =>
    islossless G6.setup.
  proof.
    move : dkey_ll => _ dcoins_ll.
    proc; inline *.
    wp; rnd; skip; progress.
  qed.

  lemma G6_update_ll:
    islossless G6.update.
  proof.
    move : dmapquery_ll di_ll dut_ll dstoken_ll cdistr_ful => dmq_ll di_ll _ _ [cd_ll cd_fun].
    proc; inline*.
    wp => /=; kill 4.
      if => //; last by wp; skip; progress.
      wp; kill 4.
        case (fmap_collision RF.m).
        + rcondt 1; progress.
          wp; skip; progress.
        + rcondf 1; progress.
          kill 3.
            if => //; first by wp; skip; progress.
            if => //; first by wp; skip; progress.
            sp; if => //; first by wp; skip; progress.
            wp; rnd; rnd; skip; progress.
          if => //.
          * wp; rnd; wp; skip; progress.
          * wp; skip; progress.
      wp => /=; sp; if => //; first by rnd; skip; progress.
    wp; skip; progress.
  qed.

  lemma G6_query_ll:
    islossless G6.query.
  proof.
    move : dmapquery_ll dstoken_ll di_ll dut_ll => _ _ _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //.
            sp; if => //.
            * wp; skip; progress.
            * wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress => //.
    + sp; if => //.
      * kill 10.
          if => //; first by wp; skip; progress.
          case (0 <= (oget qo).`3).
          - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
            wp => /=; kill 7.
              sp; if => //; first by wp; rnd; skip; progress.
            wp => /=; kill 3.
              sp; if => //.
              sp; if => //.
              * wp; skip; progress.
              * wp; rnd; skip; progress.
            wp; skip; progress; smt.
          wp; skip; progress; smt.
          - rcondf 4; progress; first by wp; skip; progress.
            wp; skip; progress.
        wp => /=; while (0 <= i <= size sc) (size sc - i) => //=; progress.
          wp; skip; progress; smt.
        wp => /=; rnd predT; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
      * kill 9.
          if => //; first by wp; skip; progress.
          case (0 <= (oget qo).`3).
          - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
            wp => /=; kill 7.
              sp; if => //; first by wp; rnd; skip; progress.
            wp => /=; kill 3.
              sp; if => //.
              sp; if => //.
              * wp; skip; progress.
              * wp; rnd; skip; progress.
            wp; skip; progress; smt.
          wp; skip; progress; smt.
          - rcondf 4; progress; first by wp; skip; progress.
            wp; skip; progress.
        wp => /=; while (0 <= i <= size sc) (size sc - i) => //=; progress.
          wp; skip; progress; smt.
        wp => /=; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
  qed.

  lemma G6_o_ll:
    islossless G6.o.
  proof.
    move : di_ll dut_ll => _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      - sp; if => //.
        * wp; skip; progress.
        * wp; rnd; skip; progress.
      - wp; skip; progress.
    + sp; if => //.
      - sp; if => //.
        + wp; rnd; skip; progress.
        + wp; skip; progress.
  qed.

  local lemma G5_G6_indistinguishable_resnotbad
    (D <: SSEDistROM{G5,G6,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
    Pr[SSEExpROM(G5, G6, OracleCallsCounter(D)).game(true) @ &m : res /\ !G5_Client.bad_h2] <= Pr[SSEExpROM(G5, G6, OracleCallsCounter(D)).game(false) @ &m : res].
proof.
move => oracle.
byequiv => //.
symmetry.
proc*.
inline SSEExpROM(G5, G6, OracleCallsCounter(D)).game.
rcondf{1} 2; first by progress; first by wp; skip; progress.
rcondt{2} 2; first by progress; first by wp; skip; progress.
inline*; wp.
call (_: G5_Client.bad_h2, ={glob OracleCallsCounter, glob RF, G4_Server.pk}
         /\   (G5_Client.et, G5_Client.utt, G5_Client.ws, G5_Client.h1t, G5_Client.sk, G5_Client.bad_rf_coll, G5_Client.bad_h1, G5_Client.bad_update_bt){2}
            = (G6_Client.et, G6_Client.utt, G6_Client.ws, G6_Client.h1t, G6_Client.sk, G6_Client.bad_rf_coll, G6_Client.bad_h1, G6_Client.bad_update_bt){1}
         /\ (!G5_Client.bad_h2 => G6_Client.h2t{1} = G5_Client.h2t){2}
         /\ (G5_Client.bad_h2 => forall x, dom G6_Client.h2t{1} x = dom G5_Client.h2t x){2}
         /\ (!G5_Client.bad_h2 => ={G4_Server.edb}){2}
  ) => //.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: update
 *)
proc; sp; if => //; wp.
inline*.
sp; if => //.
seq 3 3: (={kw, q1, i1, o0, glob OracleCallsCounter, glob RF, G4_Server.pk}
         /\   (G5_Client.et, G5_Client.utt, G5_Client.ws, G5_Client.h1t, G5_Client.sk, G5_Client.bad_rf_coll, G5_Client.bad_h1, G5_Client.bad_update_bt){2}
            = (G6_Client.et, G6_Client.utt, G6_Client.ws, G6_Client.h1t, G6_Client.sk, G6_Client.bad_rf_coll, G6_Client.bad_h1, G6_Client.bad_update_bt){1}
         /\ (!G5_Client.bad_h2 => G6_Client.h2t{1} = G5_Client.h2t){2}
         /\ (G5_Client.bad_h2 => forall x, dom G6_Client.h2t{1} x = dom G5_Client.h2t x){2}
         /\ (!G5_Client.bad_h2 => ={G4_Server.edb}){2}
  ).
sp; if => //.
wp; rnd; skip; progress.
wp; skip; progress.
if => //.
wp; skip; progress.

seq 1 1: (={kw, q1, i1, o0, sc, c, s, glob OracleCallsCounter, glob RF, G4_Server.pk}
         /\   (G5_Client.et, G5_Client.utt, G5_Client.ws, G5_Client.h1t, G5_Client.sk, G5_Client.bad_rf_coll, G5_Client.bad_h1, G5_Client.bad_update_bt){2}
            = (G6_Client.et, G6_Client.utt, G6_Client.ws, G6_Client.h1t, G6_Client.sk, G6_Client.bad_rf_coll, G6_Client.bad_h1, G6_Client.bad_update_bt){1}
         /\ (!G5_Client.bad_h2 => G6_Client.h2t{1} = G5_Client.h2t){2}
         /\ (G5_Client.bad_h2 => forall x, dom G6_Client.h2t{1} x = dom G5_Client.h2t x){2}
         /\ (!G5_Client.bad_h2 => ={G4_Server.edb}){2}
  ).
if => //.
wp; rnd; wp; skip; progress.
wp; skip; progress.
sp; if => //.
wp; skip; progress.
if; progress.
case (G5_Client.bad_h2{2}) => pre.
- rewrite -(H0 pre) //.
- rewrite -H //.
case (G5_Client.bad_h2{2}) => pre.
- rewrite (H0 pre) //.
- rewrite H //.
wp; skip; progress.
sp; if => //.
wp; skip; progress.
wp; rnd; rnd; skip; progress. smt.
wp; skip; progress.
(*
 * The update call in the real world is required to terminate
 *)
progress.
proc.
inline*.
sp; if => //.
wp => /=.
sp; if => //; last by wp; skip; progress.
kill 4.
case (fmap_collision RF.m).
rcondt 1 => //.
wp; skip; progress.
rcondf 1 => //.
if => //.
kill 5.
if => //; first by wp; skip; progress.
if => //; first by wp; skip; progress.
sp; if => //; first by wp; skip; progress.
wp; rnd; rnd; skip; progress; smt.
wp; rnd; wp; skip; progress; smt.
wp; kill 8.
if => //; first by wp; skip; progress.
if => //; first by wp; skip; progress.
sp; if => //; first by wp; skip; progress.
wp; rnd; rnd; skip; progress; smt.
wp; skip; progress.
wp; sp; if => //.
rnd; skip; progress; smt.
(*
 * update called in the bad-event state does not affect the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G5_Client.bad_h2) => //.
kill 2; first by if => //; inline*; wp; skip; progress.
inline*.
sp; if => //; last by wp; skip; progress.
sp; if => //.
  * seq 2: (G5_Client.bad_h2) => //; last by hoare; wp; rnd; skip; progress.
      wp; rnd; skip; progress; smt.
    sp; if => //; first by wp; skip; progress.
    if => //.
    - seq 2: (G5_Client.bad_h2) => //; last by hoare; rnd; wp; skip; progress.
        rnd; wp; skip; progress; smt.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress; smt.
    - sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress; smt.
  * sp; if => //; first by wp; skip; progress.
    if => //.
    - seq 2: (G5_Client.bad_h2) => //; last by hoare; rnd; wp; skip; progress.
        rnd; wp; skip; progress; smt.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress; smt.
    - sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress; smt.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: query
 *)
proc; sp; if => //; wp.
inline*.
sp; if => //.
+ rcondt{1} 3; progress; first by wp; skip; progress.
  rcondt{2} 3; progress; first by wp; skip; progress.
  wp; skip; progress.
+ rcondf{2} 11; progress.
    swap 10 -1; kill 10.
      while (true) (size sc - i) => //; progress.
      * wp; skip; progress; smt.
      * skip; progress; smt.
    wp; sp; if => //.
    rnd; skip; progress.
  rcondf{1} 11; progress.
    swap 10 -1; kill 10.
      while (true) (size sc - i) => //; progress.
      * wp; skip; progress; smt.
      * skip; progress; smt.
    wp; sp; if => //.
    rnd; skip; progress.

seq 3 3: (={kw, q1, x, glob OracleCallsCounter, glob RF, G4_Server.pk}
         /\   (G5_Client.et, G5_Client.utt, G5_Client.ws, G5_Client.h1t, G5_Client.sk, G5_Client.bad_rf_coll, G5_Client.bad_h1, G5_Client.bad_update_bt){2}
            = (G6_Client.et, G6_Client.utt, G6_Client.ws, G6_Client.h1t, G6_Client.sk, G6_Client.bad_rf_coll, G6_Client.bad_h1, G6_Client.bad_update_bt){1}
         /\ (!G5_Client.bad_h2 => G6_Client.h2t{1} = G5_Client.h2t){2}
         /\ (G5_Client.bad_h2 => forall x, dom G6_Client.h2t{1} x = dom G5_Client.h2t x){2}
         /\ (!G5_Client.bad_h2 => ={G4_Server.edb}){2}
  ).
sp; if => //.
wp; rnd; skip; progress.
wp; skip; progress.
swap{1} 1 12; swap{2} 1 12.
wp => /=.
while (={kw0, i0, c0, t, glob OracleCallsCounter, glob RF, G4_Server.pk}
         /\   (G5_Client.et, G5_Client.utt, G5_Client.ws, G5_Client.h1t, G5_Client.sk, G5_Client.bad_rf_coll, G5_Client.bad_h1, G5_Client.bad_update_bt){2}
            = (G6_Client.et, G6_Client.utt, G6_Client.ws, G6_Client.h1t, G6_Client.sk, G6_Client.bad_rf_coll, G6_Client.bad_h1, G6_Client.bad_update_bt){1}
         /\ (!G5_Client.bad_h2 => G6_Client.h2t{1} = G5_Client.h2t){2}
         /\ (G5_Client.bad_h2 => forall x, dom G6_Client.h2t{1} x = dom G5_Client.h2t x){2}
         /\ (!G5_Client.bad_h2 => ={r1, G4_Server.edb}){2}).
wp; sp; if => //.
sp; if => //.
sp; if => //; first by progress; smt.
sp; if{2} => //.
wp; rnd{1}; skip; progress.
smt.
case ((x1 = (kw0, t)){2}) => // xval.
+ rewrite xval 2!mem_set //=.
+ rewrite 2!mem_set xval //=.
case (G5_Client.bad_h2{2}) => pre.
- rewrite -H0 //.
- rewrite H //.
wp; rnd; skip; progress; smt.
wp; skip; progress; smt.
case ((!dom G5_Client.h2t (kw0, t)){2}).
rcondt{2} 6. progress. wp; rnd; skip; progress.
rcondt{1} 6. progress. wp; rnd; skip; progress.
case (G5_Client.bad_h2{m0}) => pre.
rewrite H0 //.
rewrite (H pre) H6 //.
rcondf{2} 8; progress. wp; rnd; skip; progress.

wp; rnd; wp; rnd; skip; progress; smt.

rcondf{2} 6. progress. wp; rnd; skip; progress.
rcondf{1} 6. progress. wp; rnd; skip; progress.
case (G5_Client.bad_h2{m0}) => pre.
rewrite H0 //.
rewrite (H pre) H6 //.
wp; rnd; skip; progress; smt.

case ((!dom G5_Client.h2t (kw0, t)){2}).
rcondt{2} 4. progress. wp; skip; progress.
rcondt{1} 4. progress. wp; skip; progress.
case (G5_Client.bad_h2{m0}) => pre.
rewrite H0 //.
rewrite (H pre) H5 //.
sp; if{2} => //.
wp; rnd{1}; skip; progress.
smt.
case ((x1 = (kw0, t)){2}) => // xval.
+ rewrite xval 2!mem_set //=.
+ rewrite 2!mem_set xval //=.
case (G5_Client.bad_h2{2}) => pre.
- rewrite H0 //.
- rewrite -H //.
wp; rnd; skip; progress; smt.
rcondf{2} 4. progress. wp; skip; progress.
rcondf{1} 4. progress. wp; skip; progress.
case (G5_Client.bad_h2{m0}) => pre.
rewrite H0 //.
rewrite (H pre) H5 //.
wp; skip; progress; smt.

wp => /=.
while ((0 <= i <= size sc){2}
         /\ ={kw, sc, i, q1, glob OracleCallsCounter, glob RF, G4_Server.pk}
         /\   (G5_Client.et, G5_Client.utt, G5_Client.ws, G5_Client.h1t, G5_Client.sk, G5_Client.bad_rf_coll, G5_Client.bad_h1, G5_Client.bad_update_bt){2}
            = (G6_Client.et, G6_Client.utt, G6_Client.ws, G6_Client.h1t, G6_Client.sk, G6_Client.bad_rf_coll, G6_Client.bad_h1, G6_Client.bad_update_bt){1}
         /\ (!G5_Client.bad_h2 => G6_Client.h2t{1} = G5_Client.h2t){2}
         /\ (G5_Client.bad_h2 => forall x, dom G6_Client.h2t{1} x = dom G5_Client.h2t x){2}
         /\ (!G5_Client.bad_h2 => ={G4_Server.edb}){2}).
wp; skip; progress.
smt.
smt.
rewrite (H1 H6) //.
rewrite 2!mem_set (H2 H6) //.
wp; skip; progress.
smt.
smt.
smt.
smt.
smt.
+
(*
 * The query call in the real world is required to terminate
 *)
progress.
proc.
inline*.
sp; if => //.
wp => /=.
sp; if => //.
+ rcondt 3; progress; first by wp; skip; progress.
  wp; skip; progress.
+ rcondf 11; progress.
    swap 10 -1; kill 10.
      while (true) (size sc - i) => //; progress.
      * wp; skip; progress; smt.
      * skip; progress; smt.
    wp; sp; if => //.
    rnd; skip; progress.
  wp => /=; sp; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0); progress.
    wp; kill 7; first by if => //; wp; rnd; skip; progress; smt.
    wp; kill 3. if => //. sp; if => //. wp; skip; progress. wp; rnd; skip; progress; smt.
    wp => /=; skip; progress; smt.
  wp; while (true) (size sc - i) => //; progress.
    wp; skip; progress; smt.
  wp; sp; if => //.
  - rnd (predT); skip; progress; smt. 
  - wp; skip; progress; smt.
(*
 * query called in the bad-event state must keep the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G5_Client.bad_h2) => //.
inline*.
wp => /=.
sp; if => //.
+ rcondt 3; progress; first by wp; skip; progress.
  wp; skip; progress.
+ rcondf 11; progress.
    swap 10 -1; kill 10.
      while (true) (size sc - i) => //; progress.
      * wp; skip; progress; smt.
      * skip; progress; smt.
    wp; sp; if => //.
    rnd; skip; progress.
  wp => /=; sp; while (0 <= i0 <= c0 + 1 /\ G5_Client.bad_h2) (c0 + 1 - i0); progress.
    wp; sp; if => //.
    + sp; if => //.
      * sp; if => //.
        - sp; if => //.
          + wp; skip; progress; smt.
          + wp; rnd; skip; progress.
        - skip; progress; smt.
      * kill 3; first by wp; skip; progress.
        kill 2; first by wp; skip; progress.
        kill 1; first by wp; rnd; skip; progress; smt.
        sp; if => //.
        - sp; if => //.
          + wp; skip; progress; smt.
          + wp; rnd; skip; progress; smt.
        - skip; progress; smt.
    + sp; if => //.
      * sp; if => //.
        + wp; skip; progress; smt.
        + wp; rnd; skip; progress; smt.
      skip; progress; smt.
  wp; while (true) (size sc - i) => //; progress.
    wp; skip; progress; smt.
  wp; sp; if => //.
  - rnd (predT); skip; progress; smt. 
  - wp; skip; progress; smt.
+
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: o
 *)
proc; sp; if => //; wp.
inline*.
sp; if => //.
wp; sp; if => //.
wp; sp; if => //.
+ wp; skip; progress; smt.
+ wp; rnd; progress; smt.

wp; if => //.
wp; sp; if => //.
progress; smt.
sp; if{2} => //.
wp; rnd{1}; skip; progress; smt.
wp; rnd; skip; progress; smt.
skip; progress; smt.
+
(*
 * The o call in the real world is required to terminate
 *)
progress.
proc.
sp; if => //.
wp; inline*.
sp; if => //.
sp; if => //; last by wp; skip; progress.
sp; if => //; first by wp; skip; progress.
wp; rnd; wp; skip; progress; smt.
sp; if => //; last by wp; skip; progress.
sp; if => //; last by wp; skip; progress.
wp; rnd; wp; skip; progress; smt.
(*
 * o called in the bad-event state keeps the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G5_Client.bad_h2).
sp; if => //.
wp; inline*.
sp; if => //.
sp; if => //.
wp; skip; progress.
wp; rnd; skip; progress; smt(dut_ll).
wp; skip; progress.
if => //.
inline *.
sp; if => //.
sp; if => //.
wp; skip; progress.
wp; rnd; wp; skip; progress; smt.
wp; skip; progress.
skip; progress.
(*
 * No further procedures are left. Lastly, we need to prove that, in the meanwhile that the distinguisher does whatever she wants, the consistency, hence the indistinguishability, is kept in the case no bad events occur.
 *)
simplify.
wp; rnd; wp; skip; progress.
move : (H1 H3).
move => [rwme] _.
rewrite rwme //.
  qed.

  local lemma G5_G6_indistinguishable_uptoresbad
    (D <: SSEDistROM{G5,G6,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
      Pr[SSEExpROM(G5, G6, OracleCallsCounter(D)).game(true) @ &m : res]
    <= Pr[SSEExpROM(G5, G6, OracleCallsCounter(D)).game(false) @ &m : res]
    + Pr[SSEExpROM(G5, G6, OracleCallsCounter(D)).game(true) @ &m : res /\ G5_Client.bad_h2].
  proof.
    move => oracle.
    rewrite RField.addrC Pr[mu_split (G5_Client.bad_h2)] ler_add2l.
    apply (G5_G6_indistinguishable_resnotbad D &m oracle).
  qed.

  lemma G5_G6_indistinguishable_uptobad
    (D <: SSEDistROM{G5,G6,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
      Pr[SSEExpROM(G5, G6, OracleCallsCounter(D)).game(true) @ &m : res]
    <= Pr[SSEExpROM(G5, G6, OracleCallsCounter(D)).game(false) @ &m : res]
    + Pr[SSEExpROM(G5, G6, OracleCallsCounter(D)).game(true) @ &m : G5_Client.bad_h2].
  proof.
    move => oracle.
    pose p5 := Pr[SSEExpROM(G5, G6, OracleCallsCounter(D)).game(true) @ &m : res].
    pose p6 := Pr[SSEExpROM(G5, G6, OracleCallsCounter(D)).game(false) @ &m : res].
    rewrite RField.addrC RField.addrC Pr[mu_split res] andbC.
    pose prb := Pr[SSEExpROM(G5, G6, OracleCallsCounter(D)).game(true) @ &m : res /\ G5_Client.bad_h2].
    rewrite andbC RField.addrA.
    pose prCb := Pr[SSEExpROM(G5, G6, OracleCallsCounter(D)).game(true) @ &m : !res /\ G5_Client.bad_h2].
    rewrite (ler_trans (p6 + prb)).
    rewrite /p5 /p6 /prb.
    apply (G5_G6_indistinguishable_uptoresbad D &m oracle).
    rewrite -RField.addrA ler_add2l -RField.addr0 ler_add2l.
    smt.
  qed.

  (*
   * === Part7 ===
   * We start no to handle the bad events, reducing to other experiments
   * -- bad_h1
   *)
  module G7_Client: SSEClient = {
    var sk: tau
    var ws: (query, stoken list) fmap

    var utt: (query * int, utoken) fmap
    var et: (query * int, index) fmap
    var h1t: (mapquery * stoken, utoken) fmap
    var h2t: (mapquery * stoken, index) fmap

    var bad_rf_coll: bool (* collision in the random function *)
    var bad_update_bt: bool (* prediction in backup tables *)
    var bad_update_h1t: bool (* guess in h1t *)
    var bad_update_h2t: bool (* guess in h2t *)
    var bad_h1: bool (* bad event raised by h1 *)
    var bad_h2: bool (* bad event raised by h2 *)

    proc setup(): setupserver = {
      var pk;

      (pk, sk) <@ CTP.index();
      RF.init();
      ws <- empty;
      utt <- empty;
      et <- empty;
      h1t <- empty;
      h2t <- empty;

      bad_rf_coll <- false;
      bad_update_bt <- false;
      bad_update_h1t <- false;
      bad_update_h2t <- false;
      bad_h1 <- false;
      bad_h2 <- false;

      return pk;
    }

    (* Simulating the hash functions *)
    module SimH1: HashFunction1 = {
      proc hash(kw: mapquery, s: stoken): utoken = {
        var y;

        if (!(dom h1t (kw, s))) {
          y <$ dutoken;
          h1t.[(kw, s)] <- y;
        }

        return oget h1t.[(kw, s)];
      }
    }

    module SimH2: HashFunction2 = {
      proc hash(kw: mapquery, s: stoken): index = {
        var y;

        if (!(dom h2t (kw, s))) {
          y <$ di;
          h2t.[(kw, s)] <- y;
        }

        return oget h2t.[(kw, s)];
      }
    }

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var kw, s, c, sc, idx, ti, qs, cand_ws;

      if (o = ADD) {
        kw <@ RF.f(q);
        if (fmap_collision RF.m) {
          bad_rf_coll <- true;
          ti <- None;
        } else {
          if (!dom ws q) {
            sc <- [];
            s <$ dstoken;
            c <- 0;
          } else {
            sc <- oget ws.[q];
            c <- size sc;
            s <@ CTP.backward(sk, last witness sc);
          }
          ws.[q] <- sc ++ [s];
          if (dom h1t (kw, s)) {
            (* Rare event: We do not expect this value to be called (read guessed) in the past if not for a negligible probability *)
            bad_update_h1t <- true;
            ti <- None;
          } else {
            if (dom h2t (kw, s)) {
              (* Rare event: We do not expect this value to be called (read guessed) in the past if not for a negligible probability *)
              bad_update_h2t <- true;
              ti <- None;
            } else {
              (*
              * Additional care when h1t/h2t is not synced with utt/et (i.e. utt/et already contains what h1t/h2t would contain in the future).
              * This is not a proper bad event: It happens naturally for any duplicates and in the real world is not an issue.
              *)
              qs <- fdom (filter (fun (_: query) k => k = kw) RF.m); (* queries mapping to kw *)
              cand_ws <- filter (fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts) ws; (* occurrences in the ws map *)
              if (cand_ws <> empty) { (* occurrence found *)
                (* This is also unlikely to happen *)
                bad_update_bt <- true;
                ti <- None;
              } else {
                utt.[(q, c)] <$ dutoken;
                idx <$ di;
                et.[(q, c)] <- idx;
                idx <- i +^ idx;
                ti <- Some(oget utt.[(q, c)], idx);
              }
            }
          }
        }
      } else {
        ti <- None;
      }
     
      return ti;
    }

    proc query(q: query): (mapquery * stoken * int) option = {
      var kw, sc, c, i, s;
      var r: (mapquery * stoken * int) option;

      if (!dom ws q) {
        r <- None;
      } else {
        kw <@ RF.f(q);
        if (fmap_collision RF.m) {
          bad_rf_coll <- true;
        }

        sc <- oget ws.[q];
        c <- size sc - 1;
        r <- Some (kw, nth witness sc c, c);

        (* Lazily programming the hash tables *)
        i <- 0;
        while (i < size sc) {
          s <- nth witness sc i;
          h1t.[(kw, s)] <- oget utt.[(q, i)];
          h2t.[(kw, s)] <- oget et.[(q, i)];
          i <- i + 1;
        }
      }

      return r;
    }

    proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
      var h1, h2, h;

      h <- None;
      if     (i = HASH1) {
        h1 <@ SimH1.hash(argv);
        h <- Some(Some(h1), None);
      } elif (i = HASH2) {
        h2 <@ SimH2.hash(argv);
        h <- Some(None, Some(h2));
      }

      return h;
    }
  }.

  module G7 = SSEProtocol(G7_Client, G4_Server(G7_Client.SimH1, G7_Client.SimH2)).

  lemma G7_setup_ll:
    is_lossless dcoins =>
    islossless G7.setup.
  proof.
    move : dkey_ll => _ dcoins_ll.
    proc; inline *.
    wp; rnd; skip; progress.
  qed.

  lemma G7_update_ll:
    islossless G7.update.
  proof.
    move : dmapquery_ll di_ll dut_ll dstoken_ll cdistr_ful => dmq_ll di_ll _ _ [cd_ll cd_fun].
    proc; inline*.
    wp => /=; kill 4.
      if => //; last by wp; skip; progress.
      wp; kill 4.
        case (fmap_collision RF.m).
        + rcondt 1; progress.
          wp; skip; progress.
        + rcondf 1; progress.
          kill 3.
            if => //; first by wp; skip; progress.
            if => //; first by wp; skip; progress.
            sp; if => //; first by wp; skip; progress.
            wp; rnd; rnd; skip; progress.
          if => //.
          * wp; rnd; wp; skip; progress.
          * wp; skip; progress.
      wp => /=; sp; if => //; first by rnd; skip; progress.
    wp; skip; progress.
  qed.

  lemma G7_query_ll:
    islossless G7.query.
  proof.
    move : dmapquery_ll dstoken_ll di_ll dut_ll => _ _ _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //; first by wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress => //.
    + sp; if => //.
      * kill 10.
          if => //; first by wp; skip; progress.
          case (0 <= (oget qo).`3).
          - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
            wp => /=; kill 7.
              sp; if => //; first by wp; rnd; skip; progress.
            wp => /=; kill 3.
              sp; if => //; first by wp; rnd; skip; progress.
            wp; skip; progress; smt.
          wp; skip; progress; smt.
          - rcondf 4; progress; first by wp; skip; progress.
            wp; skip; progress.
        wp => /=; while (0 <= i <= size sc) (size sc - i) => //=; progress.
          wp; skip; progress; smt.
        wp => /=; rnd predT; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
      * kill 9.
          if => //; first by wp; skip; progress.
          case (0 <= (oget qo).`3).
          - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
            wp => /=; kill 7.
              sp; if => //; first by wp; rnd; skip; progress.
            wp => /=; kill 3.
              sp; if => //; first by wp; rnd; skip; progress.
            wp; skip; progress; smt.
          wp; skip; progress; smt.
          - rcondf 4; progress; first by wp; skip; progress.
            wp; skip; progress.
        wp => /=; while (0 <= i <= size sc) (size sc - i) => //=; progress.
          wp; skip; progress; smt.
        wp => /=; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
  qed.

  lemma G7_o_ll:
    islossless G7.o.
  proof.
    move : di_ll dut_ll => _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      - wp; rnd; skip; progress.
      - wp; skip; progress.
    + sp; if => //.
      - sp; if => //.
        + wp; rnd; skip; progress.
        + wp; skip; progress.
  qed.

  local lemma G6_G7_indistinguishable_resnotbad
    (D <: SSEDistROM{G6,G7,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
    Pr[SSEExpROM(G6, G7, OracleCallsCounter(D)).game(true) @ &m : res /\ !G6_Client.bad_h1] <= Pr[SSEExpROM(G6, G7, OracleCallsCounter(D)).game(false) @ &m : res].
proof.
move => oracle.
byequiv => //.
symmetry.
proc*.
inline SSEExpROM(G6, G7, OracleCallsCounter(D)).game.
rcondf{1} 2; first by progress; first by wp; skip; progress.
rcondt{2} 2; first by progress; first by wp; skip; progress.
inline*; wp.
call (_: G6_Client.bad_h1, ={glob OracleCallsCounter, glob RF, G4_Server.pk}
         /\   (G6_Client.et, G6_Client.utt, G6_Client.ws, G6_Client.h2t, G6_Client.sk, G6_Client.bad_rf_coll, G6_Client.bad_h2, G6_Client.bad_update_bt){2}
            = (G7_Client.et, G7_Client.utt, G7_Client.ws, G7_Client.h2t, G7_Client.sk, G7_Client.bad_rf_coll, G7_Client.bad_h2, G7_Client.bad_update_bt){1}
         /\ (!G6_Client.bad_h1 => G7_Client.h1t{1} = G6_Client.h1t){2}
         /\ (G6_Client.bad_h1 => forall x, dom G7_Client.h1t{1} x = dom G6_Client.h1t x){2}
         /\ (!G6_Client.bad_h1 => ={G4_Server.edb}){2}
  ) => //.
(* UPDATE *)
proc; sp; if => //; wp.
inline*.
sp; if => //.
seq 3 3: (={kw, q1, i1, o0, glob OracleCallsCounter, glob RF, G4_Server.pk}
         /\   (G6_Client.et, G6_Client.utt, G6_Client.ws, G6_Client.h2t, G6_Client.sk, G6_Client.bad_rf_coll, G6_Client.bad_h2, G6_Client.bad_update_bt){2}
            = (G7_Client.et, G7_Client.utt, G7_Client.ws, G7_Client.h2t, G7_Client.sk, G7_Client.bad_rf_coll, G7_Client.bad_h2, G7_Client.bad_update_bt){1}
         /\ (!G6_Client.bad_h1 => G7_Client.h1t{1} = G6_Client.h1t){2}
         /\ (G6_Client.bad_h1 => forall x, dom G7_Client.h1t{1} x = dom G6_Client.h1t x){2}
         /\ (!G6_Client.bad_h1 => ={G4_Server.edb}){2}
  ).
sp; if => //.
wp; rnd; skip; progress.
wp; skip; progress.
if => //.
wp; skip; progress.

seq 1 1: (={kw, q1, i1, o0, sc, c, s, glob OracleCallsCounter, glob RF, G4_Server.pk}
         /\   (G6_Client.et, G6_Client.utt, G6_Client.ws, G6_Client.h2t, G6_Client.sk, G6_Client.bad_rf_coll, G6_Client.bad_h2, G6_Client.bad_update_bt){2}
            = (G7_Client.et, G7_Client.utt, G7_Client.ws, G7_Client.h2t, G7_Client.sk, G7_Client.bad_rf_coll, G7_Client.bad_h2, G7_Client.bad_update_bt){1}
         /\ (!G6_Client.bad_h1 => G7_Client.h1t{1} = G6_Client.h1t){2}
         /\ (G6_Client.bad_h1 => forall x, dom G7_Client.h1t{1} x = dom G6_Client.h1t x){2}
         /\ (!G6_Client.bad_h1 => ={G4_Server.edb}){2}
  ).
if => //.
wp; rnd; wp; skip; progress.
wp; skip; progress.
sp; if; progress.
case (G6_Client.bad_h1{2}) => pre.
- rewrite -(H0 pre) //.
- rewrite -H //.
case (G6_Client.bad_h1{2}) => pre.
- rewrite (H0 pre) //.
- rewrite H //.
wp; skip; progress.
sp; if => //.
wp; skip; progress.

sp; if => //.
wp; skip; progress.
wp; rnd; rnd; skip; progress. smt.
wp; skip; progress.
(*
 * The update call in the real world is required to terminate
 *)
progress.
proc.
inline*.
sp; if => //.
wp => /=.
sp; if => //; last by wp; skip; progress.
kill 4.
case (fmap_collision RF.m).
rcondt 1 => //.
wp; skip; progress.
rcondf 1 => //.
if => //.
kill 5.
if => //; first by wp; skip; progress.
if => //; first by wp; skip; progress.
sp; if => //; first by wp; skip; progress.
wp; rnd; rnd; skip; progress; smt.
wp; rnd; wp; skip; progress; smt.
wp; kill 8.
if => //; first by wp; skip; progress.
if => //; first by wp; skip; progress.
sp; if => //; first by wp; skip; progress.
wp; rnd; rnd; skip; progress; smt.
wp; skip; progress.
wp; sp; if => //.
rnd; skip; progress; smt.
(*
 * update called in the bad-event state does not affect the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G6_Client.bad_h1) => //.
kill 2; first by if => //; inline*; wp; skip; progress.
inline*.
sp; if => //; last by wp; skip; progress.
sp; if => //.
  * seq 2: (G6_Client.bad_h1) => //; last by hoare; wp; rnd; skip; progress.
      wp; rnd; skip; progress; smt.
    sp; if => //; first by wp; skip; progress.
    if => //.
    - seq 2: (G6_Client.bad_h1) => //; last by hoare; rnd; wp; skip; progress.
        rnd; wp; skip; progress; smt.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress; smt.
    - sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress; smt.
  * sp; if => //; first by wp; skip; progress.
    if => //.
    - seq 2: (G6_Client.bad_h1) => //; last by hoare; rnd; wp; skip; progress.
        rnd; wp; skip; progress; smt.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress; smt.
    - sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress; smt.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: query
 *)
proc; sp; if => //; wp.
inline*.
sp; if => //.
+ rcondt{1} 3; progress; first by wp; skip; progress.
  rcondt{2} 3; progress; first by wp; skip; progress.
  wp; skip; progress.
+ rcondf{2} 11; progress.
    kill 9.
      while (true) (size sc - i) => //; progress.
        wp; skip; progress; smt.
      skip; progress; smt.
    wp; sp; if => //; first by rnd; skip; progress.
  rcondf{1} 11; progress.
    kill 9.
      while (true) (size sc - i) => //; progress.
        wp; skip; progress; smt.
      skip; progress; smt.
    wp; sp; if => //; first by rnd; skip; progress.
  seq 3 3: (={kw, q1, x, glob OracleCallsCounter, glob RF, G4_Server.pk}
         /\   (G6_Client.et, G6_Client.utt, G6_Client.ws, G6_Client.h2t, G6_Client.sk, G6_Client.bad_rf_coll, G6_Client.bad_h2, G6_Client.bad_update_bt){2}
            = (G7_Client.et, G7_Client.utt, G7_Client.ws, G7_Client.h2t, G7_Client.sk, G7_Client.bad_rf_coll, G7_Client.bad_h2, G7_Client.bad_update_bt){1}
         /\ (!G6_Client.bad_h1 => G7_Client.h1t{1} = G6_Client.h1t){2}
         /\ (G6_Client.bad_h1 => forall x, dom G7_Client.h1t{1} x = dom G6_Client.h1t x){2}
         /\ (!G6_Client.bad_h1 => ={G4_Server.edb}){2}
  ).
    sp; if => //.
    wp; rnd; skip; progress.
    wp; skip; progress.
  swap{1} 1 8; swap{2} 1 8; wp => /=.
  while (={kw0, i0, c0, t, glob OracleCallsCounter, glob RF, G4_Server.pk}
         /\   (G6_Client.et, G6_Client.utt, G6_Client.ws, G6_Client.h2t, G6_Client.sk, G6_Client.bad_rf_coll, G6_Client.bad_h2, G6_Client.bad_update_bt){2}
            = (G7_Client.et, G7_Client.utt, G7_Client.ws, G7_Client.h2t, G7_Client.sk, G7_Client.bad_rf_coll, G7_Client.bad_h2, G7_Client.bad_update_bt){1}
         /\ (!G6_Client.bad_h1 => G7_Client.h1t{1} = G6_Client.h1t){2}
         /\ (G6_Client.bad_h1 => forall x, dom G7_Client.h1t{1} x = dom G6_Client.h1t x){2}
         /\ (!G6_Client.bad_h1 => ={r1, G4_Server.edb}){2}).
    wp.
    case ((!dom G6_Client.h2t (kw0, t)){2}) => /=.
    * rcondt{2} 7; progress; wp.
        kill 3.
          if => //; sp; if => //.
          + wp; skip; progress.
          + wp; rnd; skip; progress; smt.
        wp; skip; progress.
      rcondt{1} 7; progress; wp.
        kill 3.
          if => //; wp; rnd; skip; progress; smt.
        wp; skip; progress.
      rnd; wp => /=.
      sp; if => //; first by progress; smt.
      + sp; if{2} => //. 
        - wp; rnd{1}; skip; rewrite /=; progress; first by smt.
          case (x1 = (kw0, t){2}) => x1_def.
          - rewrite x1_def 2!mem_set //=.
          - rewrite 2!mem_set x1_def /=.
            case (G6_Client.bad_h1{2}) => pre.
            - rewrite (H0 pre) //.
            - rewrite -H //.
        - wp; rnd; skip; progress; first by smt.
          * case (x1 = (kw0, t){2}) => x1_def.
            - rewrite x1_def 2!mem_set //=.
            - rewrite 2!mem_set x1_def /=.
              case (G6_Client.bad_h1{2}) => pre.
              - rewrite (H0 pre) //.
              - rewrite -H //.
          * smt.
          * smt.
          * smt.
      + skip; progress; smt.
    * rcondf{2} 7; progress; wp.
        kill 3.
          if => //; sp; if => //.
          + wp; skip; progress.
          + wp; rnd; skip; progress; smt.
        wp; skip; progress.
      rcondf{1} 7; progress; wp.
        kill 3.
          if => //; wp; rnd; skip; progress; smt.
        wp; skip; progress.
      sp; if => //; first by progress; smt.
      + sp; if{2} => //. 
        - wp; rnd{1}; skip; rewrite /=; progress; first by smt.
          case (x1 = (kw0, t){2}) => x1_def.
          - rewrite x1_def 2!mem_set //=.
          - rewrite 2!mem_set x1_def /=.
            case (G6_Client.bad_h1{2}) => pre.
            - rewrite (H0 pre) //.
            - rewrite -H //.
        - wp; rnd; skip; progress; first by smt.
          * case (x1 = (kw0, t){2}) => x1_def.
            - rewrite x1_def 2!mem_set //=.
            - rewrite 2!mem_set x1_def /=.
              case (G6_Client.bad_h1{2}) => pre.
              - rewrite (H0 pre) //.
              - rewrite -H //.
          * smt.
          * smt.
          * smt.
      + skip; progress; smt.
  wp; while ((0 <= i <= size sc){2}
         /\ ={kw, sc, i, q1, glob OracleCallsCounter, glob RF, G4_Server.pk}
         /\   (G6_Client.et, G6_Client.utt, G6_Client.ws, G6_Client.h2t, G6_Client.sk, G6_Client.bad_rf_coll, G6_Client.bad_h2, G6_Client.bad_update_bt){2}
            = (G7_Client.et, G7_Client.utt, G7_Client.ws, G7_Client.h2t, G7_Client.sk, G7_Client.bad_rf_coll, G7_Client.bad_h2, G7_Client.bad_update_bt){1}
         /\ (!G6_Client.bad_h1 => G7_Client.h1t{1} = G6_Client.h1t){2}
         /\ (G6_Client.bad_h1 => forall x, dom G7_Client.h1t{1} x = dom G6_Client.h1t x){2}
         /\ (!G6_Client.bad_h1 => ={G4_Server.edb}){2}).
    wp; skip; progress; smt.
  wp; skip; progress; smt.
(*
 * The query call in the real world is required to terminate
 *)
progress.
proc.
inline*.
sp; if => //.
wp => /=.
sp; if => //.
* rcondt 3; progress; first by wp; skip; progress.
  wp; skip; progress.
* rcondf 11; progress.
    wp; kill 9.
      while (true) (size sc - i); progress; first by wp; skip; progress; smt.
      wp; skip; progress; smt.
    wp => /=; sp; if => //.
  wp; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0); progress.
    wp; sp; if => //.
    - swap 4 -3; swap 5 -3; swap 6 -3; sp; if => //.
      + wp; rnd; wp; rnd; skip; progress; smt.
      + wp; rnd; skip; progress; smt.
    - sp; if => //.
      + wp; rnd; skip; progress; smt.
      + wp; skip; progress; smt.
  wp; while (true) (size sc - i); progress.
    wp; skip; progress; smt.
  wp => /=; sp; if => //.
  + rnd (predT); skip; progress; smt.
  + skip; progress; smt.
(*
 * query called in the bad-event state must keep the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G6_Client.bad_h1) => //.
inline*.
sp; if => //.
* rcondt 3; progress; first by wp; skip; progress.
  wp; skip; progress.
* rcondf 11; progress.
    wp; kill 9.
      while (true) (size sc - i); progress; first by wp; skip; progress; smt.
      wp; skip; progress; smt.
    wp => /=; sp; if => //.
  wp; while (G6_Client.bad_h1) (c0 + 1 - i0); progress.
    wp => /=; kill 7.
      if => //; first by wp; rnd; skip; progress; smt.
    wp; sp; if => //; last by skip; progress; smt.
    sp; if => //; last by wp; rnd; skip; progress; smt.
      wp; skip; progress; smt.
  wp; kill 9.
    wp; while (true) (size sc - i); progress.
      wp; skip; progress; smt.
    wp; skip; progress; smt.
  rewrite /=.
  wp => /=; sp; if => //.
  + rnd (predT); skip; progress; smt.
  + skip; progress; smt.
+
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: o
 *)
proc; sp; if => //; wp.
inline*.
sp; if => //; last first.
sim; progress; smt.
wp; sp; if => //.
progress; smt.
sp; if{2} => //.
wp; rnd{1}; skip; progress; smt.
wp; rnd; skip; progress; smt.
skip; progress; smt.

(*
 * The o call in the real world is required to terminate
 *)
progress.
proc.
sp; if => //.
wp; inline*.
sp; if => //.
sp; if => //; last by wp; skip; progress.
wp; rnd; skip; progress; smt.
sp; if => //; last by wp; skip; progress.
sp; if => //; last by wp; skip; progress.
wp; rnd; skip; progress; smt.
(*
 * o called in the bad-event state keeps the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G6_Client.bad_h1).
sp; if => //.
wp; inline*.
sp; if => //.
sp; if => //.
wp; skip; progress.
wp; rnd; skip; progress; smt(dut_ll).
wp; skip; progress.
if => //.
inline *.
sp; if => //.
wp; rnd; wp; skip; progress; smt.
wp; skip; progress.
skip; progress.
(*
 * No further procedures are left. Lastly, we need to prove that, in the meanwhile that the distinguisher does whatever she wants, the consistency, hence the indistinguishability, is kept in the case no bad events occur.
 *)

wp; rnd; wp; skip; progress.
move : (H1 H3).
move => [rwme] _.
rewrite rwme //.
  qed.

  local lemma G6_G7_indistinguishable_uptoresbad
    (D <: SSEDistROM{G6,G7,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
      Pr[SSEExpROM(G6, G7, OracleCallsCounter(D)).game(true) @ &m : res]
    <= Pr[SSEExpROM(G6, G7, OracleCallsCounter(D)).game(false) @ &m : res]
    + Pr[SSEExpROM(G6, G7, OracleCallsCounter(D)).game(true) @ &m : res /\ G6_Client.bad_h1].
  proof.
    move => oracle.
    rewrite RField.addrC Pr[mu_split (G6_Client.bad_h1)] ler_add2l.
    apply (G6_G7_indistinguishable_resnotbad D &m oracle).
  qed.

  lemma G6_G7_indistinguishable_uptobad
    (D <: SSEDistROM{G6,G7,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
      Pr[SSEExpROM(G6, G7, OracleCallsCounter(D)).game(true) @ &m : res]
    <= Pr[SSEExpROM(G6, G7, OracleCallsCounter(D)).game(false) @ &m : res]
    + Pr[SSEExpROM(G6, G7, OracleCallsCounter(D)).game(true) @ &m : G6_Client.bad_h1].
  proof.
    move => oracle.
    pose p5 := Pr[SSEExpROM(G6, G7, OracleCallsCounter(D)).game(true) @ &m : res].
    pose p6 := Pr[SSEExpROM(G6, G7, OracleCallsCounter(D)).game(false) @ &m : res].
    rewrite RField.addrC RField.addrC Pr[mu_split res] andbC.
    pose prb := Pr[SSEExpROM(G6, G7, OracleCallsCounter(D)).game(true) @ &m : res /\ G6_Client.bad_h1].
    rewrite andbC RField.addrA.
    pose prCb := Pr[SSEExpROM(G6, G7, OracleCallsCounter(D)).game(true) @ &m : !res /\ G6_Client.bad_h1].
    rewrite (ler_trans (p6 + prb)).
    rewrite /p5 /p6 /prb.
    apply (G6_G7_indistinguishable_uptoresbad D &m oracle).
    rewrite -RField.addrA ler_add2l -RField.addr0 ler_add2l.
    smt.
  qed.

  (*
   * === Part8 ===
   * We start no to handle the bad events, reducing to other experiments
   * -- bad_update_bt
   *)
  module G8_Client: SSEClient = {
    var sk: tau
    var ws: (query, stoken list) fmap

    var utt: (query * int, utoken) fmap
    var et: (query * int, index) fmap
    var h1t: (mapquery * stoken, utoken) fmap
    var h2t: (mapquery * stoken, index) fmap

    var bad_rf_coll: bool (* collision in the random function *)
    var bad_update_bt: bool (* prediction in backup tables *)
    var bad_update_h1t: bool (* guess in h1t *)
    var bad_update_h2t: bool (* guess in h2t *)
    var bad_h1: bool (* bad event raised by h1 *)
    var bad_h2: bool (* bad event raised by h2 *)

    proc setup(): setupserver = {
      var pk;

      (pk, sk) <@ CTP.index();
      RF.init();
      ws <- empty;
      utt <- empty;
      et <- empty;
      h1t <- empty;
      h2t <- empty;

      bad_rf_coll <- false;
      bad_update_bt <- false;
      bad_update_h1t <- false;
      bad_update_h2t <- false;
      bad_h1 <- false;
      bad_h2 <- false;

      return pk;
    }

    (* Simulating the hash functions *)
    module SimH1: HashFunction1 = {
      proc hash(kw: mapquery, s: stoken): utoken = {
        var y;

        if (!(dom h1t (kw, s))) {
          y <$ dutoken;
          h1t.[(kw, s)] <- y;
        }

        return oget h1t.[(kw, s)];
      }
    }

    module SimH2: HashFunction2 = {
      proc hash(kw: mapquery, s: stoken): index = {
        var y;

        if (!(dom h2t (kw, s))) {
          y <$ di;
          h2t.[(kw, s)] <- y;
        }

        return oget h2t.[(kw, s)];
      }
    }

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var kw, s, c, sc, idx, ti;

      if (o = ADD) {
        kw <@ RF.f(q);
        if (fmap_collision RF.m) {
          bad_rf_coll <- true;
          ti <- None;
        } else {
          if (!dom ws q) {
            sc <- [];
            s <$ dstoken;
            c <- 0;
          } else {
            sc <- oget ws.[q];
            c <- size sc;
            s <@ CTP.backward(sk, last witness sc);
          }
          ws.[q] <- sc ++ [s];
          if (dom h1t (kw, s)) {
            (* Rare event: We do not expect this value to be called (read guessed) in the past if not for a negligible probability *)
            bad_update_h1t <- true;
            ti <- None;
          } else {
            if (dom h2t (kw, s)) {
              (* Rare event: We do not expect this value to be called (read guessed) in the past if not for a negligible probability *)
              bad_update_h2t <- true;
              ti <- None;
            } else {
              utt.[(q, c)] <$ dutoken;
              idx <$ di;
              et.[(q, c)] <- idx;
              idx <- i +^ idx;
              ti <- Some(oget utt.[(q, c)], idx);
            }
          }
        }
      } else {
        ti <- None;
      }
     
      return ti;
    }

    proc query(q: query): (mapquery * stoken * int) option = {
      var kw, sc, c, i, s;
      var r: (mapquery * stoken * int) option;

      if (!dom ws q) {
        r <- None;
      } else {
        kw <@ RF.f(q);
        if (fmap_collision RF.m) {
          bad_rf_coll <- true;
        }

        sc <- oget ws.[q];
        c <- size sc - 1;
        r <- Some (kw, nth witness sc c, c);

        (* Lazily programming the hash tables *)
        i <- 0;
        while (i < size sc) {
          s <- nth witness sc i;
          h1t.[(kw, s)] <- oget utt.[(q, i)];
          h2t.[(kw, s)] <- oget et.[(q, i)];
          i <- i + 1;
        }
      }

      return r;
    }

    proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
      var h1, h2, h;

      h <- None;
      if     (i = HASH1) {
        h1 <@ SimH1.hash(argv);
        h <- Some(Some(h1), None);
      } elif (i = HASH2) {
        h2 <@ SimH2.hash(argv);
        h <- Some(None, Some(h2));
      }

      return h;
    }
  }.
  module G8 = SSEProtocol(G8_Client, G4_Server(G8_Client.SimH1, G8_Client.SimH2)).

  lemma G8_setup_ll:
    is_lossless dcoins =>
    islossless G8.setup.
  proof.
    move : dkey_ll => _ dcoins_ll.
    proc; inline *.
    wp; rnd; skip; progress.
  qed.

  lemma G8_update_ll:
    islossless G8.update.
  proof.
    move : dmapquery_ll di_ll dut_ll dstoken_ll cdistr_ful => dmq_ll di_ll _ _ [cd_ll cd_fun].
    proc; inline*.
    wp => /=; kill 4.
      if => //; last by wp; skip; progress.
      wp; kill 4.
        case (fmap_collision RF.m).
        + rcondt 1; progress.
          wp; skip; progress.
        + rcondf 1; progress.
          kill 3.
            if => //; first by wp; skip; progress.
            if => //; first by wp; skip; progress.
            wp; rnd; rnd; skip; progress.
          if => //.
          * wp; rnd; wp; skip; progress.
          * wp; skip; progress.
      wp => /=; sp; if => //; first by rnd; skip; progress.
    wp; skip; progress.
  qed.

  lemma G8_query_ll:
    islossless G8.query.
  proof.
    move : dmapquery_ll dstoken_ll di_ll dut_ll => _ _ _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //; first by wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress => //.
    + sp; if => //.
      * kill 10.
          if => //; first by wp; skip; progress.
          case (0 <= (oget qo).`3).
          - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
            wp => /=; kill 7.
              sp; if => //; first by wp; rnd; skip; progress.
            wp => /=; kill 3.
              sp; if => //; first by wp; rnd; skip; progress.
            wp; skip; progress; smt.
          wp; skip; progress; smt.
          - rcondf 4; progress; first by wp; skip; progress.
            wp; skip; progress.
        wp => /=; while (0 <= i <= size sc) (size sc - i) => //=; progress.
          wp; skip; progress; smt.
        wp => /=; rnd predT; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
      * kill 9.
          if => //; first by wp; skip; progress.
          case (0 <= (oget qo).`3).
          - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
            wp => /=; kill 7.
              sp; if => //; first by wp; rnd; skip; progress.
            wp => /=; kill 3.
              sp; if => //; first by wp; rnd; skip; progress.
            wp; skip; progress; smt.
          wp; skip; progress; smt.
          - rcondf 4; progress; first by wp; skip; progress.
            wp; skip; progress.
        wp => /=; while (0 <= i <= size sc) (size sc - i) => //=; progress.
          wp; skip; progress; smt.
        wp => /=; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
  qed.

  lemma G8_o_ll:
    islossless G8.o.
  proof.
    move : di_ll dut_ll => _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      - wp; rnd; skip; progress.
      - wp; skip; progress.
    + sp; if => //.
      - sp; if => //.
        + wp; rnd; skip; progress.
        + wp; skip; progress.
  qed.

  local lemma G7_G8_indistinguishable_resnotbad
    (D <: SSEDistROM{G7,G8,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
    Pr[SSEExpROM(G7, G8, OracleCallsCounter(D)).game(true) @ &m : res /\ !G7_Client.bad_update_bt] <= Pr[SSEExpROM(G7, G8, OracleCallsCounter(D)).game(false) @ &m : res].
proof.
move : dut_ll di_ll dmapquery_ll dstoken_ll dkey_ll; rewrite /is_lossless => _ _ _ _ _.
move => oracle.
byequiv => //.
symmetry.
proc*.
inline SSEExpROM(G7, G8, OracleCallsCounter(D)).game.
rcondf{1} 2; first by progress; first by wp; skip; progress.
rcondt{2} 2; first by progress; first by wp; skip; progress.
inline*; wp.
call (_: G7_Client.bad_update_bt, ={glob OracleCallsCounter, glob RF, glob G4_Server}
         /\   (G7_Client.et, G7_Client.utt, G7_Client.ws, G7_Client.h1t, G7_Client.h2t, G7_Client.sk, G7_Client.bad_rf_coll, G7_Client.bad_h1, G7_Client.bad_h2){2}
            = (G8_Client.et, G8_Client.utt, G8_Client.ws, G8_Client.h1t, G8_Client.h2t, G8_Client.sk, G8_Client.bad_rf_coll, G8_Client.bad_h1, G8_Client.bad_h2){1}
  ) => //. 
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: update
 *)
proc.
sp; if => //.
inline*.
sp; if => //; last by wp; skip; progress.
seq 3 3: (={kw, q1, i1, o0, x, glob OracleCallsCounter, glob RF, glob G4_Server}
         /\   (G7_Client.et, G7_Client.utt, G7_Client.ws, G7_Client.h1t, G7_Client.h2t, G7_Client.sk, G7_Client.bad_rf_coll, G7_Client.bad_h1, G7_Client.bad_h2){2}
            = (G8_Client.et, G8_Client.utt, G8_Client.ws, G8_Client.h1t, G8_Client.h2t, G8_Client.sk, G8_Client.bad_rf_coll, G8_Client.bad_h1, G8_Client.bad_h2){1}
         /\ (o0 = ADD){2}
  ).
sp; wp; if => //.
wp; rnd; skip; progress.

if => //; first by wp; skip; progress.
seq 1 1: (={kw, q1, i1, o0, x, sc, s, c, glob OracleCallsCounter, glob RF, glob G4_Server}
         /\   (G7_Client.et, G7_Client.utt, G7_Client.ws, G7_Client.h1t, G7_Client.h2t, G7_Client.sk, G7_Client.bad_rf_coll, G7_Client.bad_h1, G7_Client.bad_h2){2}
            = (G8_Client.et, G8_Client.utt, G8_Client.ws, G8_Client.h1t, G8_Client.h2t, G8_Client.sk, G8_Client.bad_rf_coll, G8_Client.bad_h1, G8_Client.bad_h2){1}
         /\ (o0 = ADD){2}
  ).
if => //.
wp; rnd; wp; skip; progress.
wp; skip; progress.
sp; if => //; first by wp; skip; progress.
if => //; first by wp; skip; progress.
sp; if{2}.
wp; rnd{1}; rnd{1}; wp; skip; progress.
wp; rnd; rnd; skip; progress.
(*
 * The update call in the real world is required to terminate
 *)
progress.
proc.
inline*.
sp; if => //.
wp; sp; if => //; last by wp; skip; progress.
simplify; kill 4.
case (fmap_collision RF.m).
rcondt 1 => //; first by wp; skip; progress
rcondf 1 => //.
if => //; first by wp; skip; progress.
kill 3.
if => //; first by wp; skip; progress.
if => //; first by wp; skip; progress.
wp; rnd; rnd; skip; progress.
if => //; last by wp; skip; progress.
wp; rnd; wp; skip; progress; smt.
wp; sp; if => //.
rnd; skip; progress; smt.
(*
 * update called in the bad-event state does not affect the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G7_Client.bad_update_bt) => //.
kill 2; first by if => //; inline*; wp; skip; progress.
inline*.
sp; if => //; last by wp; skip; progress.
sp; if => //.
  * seq 2: (G7_Client.bad_update_bt) => //; last by hoare; wp; rnd; skip; progress.
      wp; rnd; skip; progress.
    sp; if => //; first by wp; skip; progress.
    if => //.
    - seq 2: (G7_Client.bad_update_bt) => //; last by hoare; rnd; wp; skip; progress.
        rnd; wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress.
    - sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress.
  * sp; if => //; first by wp; skip; progress.
    if => //.
    - seq 2: (G7_Client.bad_update_bt) => //; last by hoare; rnd; wp; skip; progress.
        rnd; wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress.
    - sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress => //.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: query
 *)
sim.
(*
 * The query call in the real world is required to terminate
 *)
progress; proc; sp; if => //; wp.
inline*.
wp; kill 5.
    if => //; first by wp; skip; progress.
    wp => /=; sp; while (true) (c0 + 1 - i0); progress.
      wp; kill 7; first by if => //; wp; rnd; skip; progress.
      wp; kill 3; first by if => //; wp; rnd; skip; progress.
      wp => /=; skip; progress; smt.
    skip; progress; smt.
wp; kill 3.
  if => //; first by wp; skip; progress.
    wp => /=; sp; while (true) (size sc - i); progress.
      wp => /=; skip; progress; smt.
    wp; if => //; first by rnd (predT); skip; progress; smt.
    skip; progress; smt.
  wp; skip; progress; smt.
(*
 * query called in the bad-event state must keep the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G7_Client.bad_update_bt) => //.
inline*.
sp; if => //.
* rcondt 3; progress; first by wp; skip; progress.
  wp; skip; progress.
* rcondf 11; progress.
    wp; kill 9.
      while (true) (size sc - i); progress; first by wp; skip; progress; smt.
      wp; skip; progress; smt.
    wp => /=; sp; if => //.
  wp; while (G7_Client.bad_update_bt) (c0 + 1 - i0); progress.
    wp => /=; kill 7.
      if => //; first by wp; rnd; skip; progress; smt.
    wp; sp; if => //; last by skip; progress; smt.
    wp; rnd; skip; progress; smt.
  wp; kill 9.
    wp; while (true) (size sc - i); progress.
      wp; skip; progress; smt.
    wp; skip; progress; smt.
  rewrite /=.
  wp => /=; sp; if => //.
  + rnd (predT); skip; progress; smt.
  + skip; progress; smt.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: o
 *)
sim.
(*
 * The o call in the real world is required to terminate
 *)
progress.
proc.
sp; if => //.
wp; inline*.
sp; if => //.
sp; if => //; last by wp; skip; progress.
wp; rnd; wp; skip; progress.
sp; if => //; last by wp; skip; progress.
sp; if => //; last by wp; skip; progress.
wp; rnd; wp; skip; progress.
(*
 * o called in the bad-event state keeps the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G7_Client.bad_update_bt).
sp; if => //.
wp; inline*.
sp; if => //.
wp; rnd; skip; progress.
wp; skip; progress.
if => //.
inline *.
sp; if => //.
wp; rnd; wp; skip; progress.
wp; skip; progress.
skip; progress.
(*
 * No further procedures are left. Lastly, we need to prove that, in the meanwhile that the distinguisher does whatever she wants, the consistency, hence the indistinguishability, is kept in the case no bad events occur.
 *)
wp; rnd; wp; skip; progress.
move : (H1 H3).
move => [rwme] _.
rewrite rwme //.
qed.

  local lemma G7_G8_indistinguishable_uptoresbad
    (D <: SSEDistROM{G7,G8,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
      Pr[SSEExpROM(G7, G8, OracleCallsCounter(D)).game(true) @ &m : res]
    <= Pr[SSEExpROM(G7, G8, OracleCallsCounter(D)).game(false) @ &m : res]
    + Pr[SSEExpROM(G7, G8, OracleCallsCounter(D)).game(true) @ &m : res /\ G7_Client.bad_update_bt].
  proof.
    move => oracle.
    rewrite RField.addrC Pr[mu_split (G7_Client.bad_update_bt)] ler_add2l.
    apply (G7_G8_indistinguishable_resnotbad D &m oracle).
  qed.

  lemma G7_G8_indistinguishable_uptobad
    (D <: SSEDistROM{G7,G8,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
      Pr[SSEExpROM(G7, G8, OracleCallsCounter(D)).game(true) @ &m : res]
    <= Pr[SSEExpROM(G7, G8, OracleCallsCounter(D)).game(false) @ &m : res]
    + Pr[SSEExpROM(G7, G8, OracleCallsCounter(D)).game(true) @ &m : G7_Client.bad_update_bt].
  proof.
    move => oracle.
    pose p5 := Pr[SSEExpROM(G7, G8, OracleCallsCounter(D)).game(true) @ &m : res].
    pose p6 := Pr[SSEExpROM(G7, G8, OracleCallsCounter(D)).game(false) @ &m : res].
    rewrite RField.addrC RField.addrC Pr[mu_split res] andbC.
    pose prb := Pr[SSEExpROM(G7, G8, OracleCallsCounter(D)).game(true) @ &m : res /\ G7_Client.bad_update_bt].
    rewrite andbC RField.addrA.
    pose prCb := Pr[SSEExpROM(G7, G8, OracleCallsCounter(D)).game(true) @ &m : !res /\ G7_Client.bad_update_bt].
    rewrite (ler_trans (p6 + prb)).
    rewrite /p5 /p6 /prb.
    apply (G7_G8_indistinguishable_uptoresbad D &m oracle).
    rewrite -RField.addrA ler_add2l -RField.addr0 ler_add2l.
    smt.
  qed.

  (*
   * === Part9 ===
   * We start no to handle the bad events, reducing to other experiments
   * -- bad_update_h1t
   *)
  module G9_Client: SSEClient = {
    var sk: tau
    var ws: (query, stoken list) fmap

    var utt: (query * int, utoken) fmap
    var et: (query * int, index) fmap
    var h1t: (mapquery * stoken, utoken) fmap
    var h2t: (mapquery * stoken, index) fmap

    var bad_rf_coll: bool (* collision in the random function *)
    var bad_update_bt: bool (* prediction in backup tables *)
    var bad_update_h1t: bool (* guess in h1t *)
    var bad_update_h2t: bool (* guess in h2t *)
    var bad_h1: bool (* bad event raised by h1 *)
    var bad_h2: bool (* bad event raised by h2 *)

    proc setup(): setupserver = {
      var pk;

      (pk, sk) <@ CTP.index();
      RF.init();
      ws <- empty;
      utt <- empty;
      et <- empty;
      h1t <- empty;
      h2t <- empty;

      bad_rf_coll <- false;
      bad_update_bt <- false;
      bad_update_h1t <- false;
      bad_update_h2t <- false;
      bad_h1 <- false;
      bad_h2 <- false;

      return pk;
    }

    (* Simulating the hash functions *)
    module SimH1: HashFunction1 = {
      proc hash(kw: mapquery, s: stoken): utoken = {
        var y;

        if (!(dom h1t (kw, s))) {
          y <$ dutoken;
          h1t.[(kw, s)] <- y;
        }

        return oget h1t.[(kw, s)];
      }
    }

    module SimH2: HashFunction2 = {
      proc hash(kw: mapquery, s: stoken): index = {
        var y;

        if (!(dom h2t (kw, s))) {
          y <$ di;
          h2t.[(kw, s)] <- y;
        }

        return oget h2t.[(kw, s)];
      }
    }

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var kw, s, c, sc, idx, ti;

      if (o = ADD) {
        kw <@ RF.f(q);
        if (fmap_collision RF.m) {
          bad_rf_coll <- true;
          ti <- None;
        } else {
          if (!dom ws q) {
            sc <- [];
            s <$ dstoken;
            c <- 0;
          } else {
            sc <- oget ws.[q];
            c <- size sc;
            s <@ CTP.backward(sk, last witness sc);
          }
          ws.[q] <- sc ++ [s];
          if (dom h1t (kw, s)) {
            (* Rare event: We do not expect this value to be called (read guessed) in the past if not for a negligible probability *)
            bad_update_h1t <- true;
            ti <- None;
          } else {
            utt.[(q, c)] <$ dutoken;
            idx <$ di;
            et.[(q, c)] <- idx;
            idx <- i +^ idx;
            ti <- Some(oget utt.[(q, c)], idx);
          }
        }
      } else {
        ti <- None;
      }
     
      return ti;
    }

    proc query(q: query): (mapquery * stoken * int) option = {
      var kw, sc, c, i, s;
      var r: (mapquery * stoken * int) option;

      if (!dom ws q) {
        r <- None;
      } else {
        kw <@ RF.f(q);
        if (fmap_collision RF.m) {
          bad_rf_coll <- true;
        }

        sc <- oget ws.[q];
        c <- size sc - 1;
        r <- Some (kw, nth witness sc c, c);

        (* Lazily programming the hash tables *)
        i <- 0;
        while (i < size sc) {
          s <- nth witness sc i;
          h1t.[(kw, s)] <- oget utt.[(q, i)];
          h2t.[(kw, s)] <- oget et.[(q, i)];
          i <- i + 1;
        }
      }

      return r;
    }

    proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
      var h1, h2, h;

      h <- None;
      if     (i = HASH1) {
        h1 <@ SimH1.hash(argv);
        h <- Some(Some(h1), None);
      } elif (i = HASH2) {
        h2 <@ SimH2.hash(argv);
        h <- Some(None, Some(h2));
      }

      return h;
    }
  }.
  module G9 = SSEProtocol(G9_Client, G4_Server(G9_Client.SimH1, G9_Client.SimH2)).

  lemma G9_setup_ll:
    is_lossless dcoins =>
    islossless G9.setup.
  proof.
    move : dkey_ll => _ dcoins_ll.
    proc; inline *.
    wp; rnd; skip; progress.
  qed.

  lemma G9_update_ll:
    islossless G9.update.
  proof.
    move : dmapquery_ll di_ll dut_ll dstoken_ll cdistr_ful => dmq_ll di_ll _ _ [cd_ll cd_fun].
    proc; inline*.
    wp => /=; kill 4.
      if => //; last by wp; skip; progress.
      wp; kill 4.
        case (fmap_collision RF.m).
        + rcondt 1; progress.
          wp; skip; progress.
        + rcondf 1; progress.
          kill 3.
            if => //; first by wp; skip; progress.
            wp; rnd; rnd; skip; progress.
          if => //.
          * wp; rnd; wp; skip; progress.
          * wp; skip; progress.
      wp => /=; sp; if => //; first by rnd; skip; progress.
    wp; skip; progress.
  qed.

  lemma G9_query_ll:
    islossless G9.query.
  proof.
    move : dmapquery_ll dstoken_ll di_ll dut_ll => _ _ _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //; first by wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress => //.
    + sp; if => //.
      * kill 10.
          if => //; first by wp; skip; progress.
          case (0 <= (oget qo).`3).
          - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
            wp => /=; kill 7.
              sp; if => //; first by wp; rnd; skip; progress.
            wp => /=; kill 3.
              sp; if => //; first by wp; rnd; skip; progress.
            wp; skip; progress; smt.
          wp; skip; progress; smt.
          - rcondf 4; progress; first by wp; skip; progress.
            wp; skip; progress.
        wp => /=; while (0 <= i <= size sc) (size sc - i) => //=; progress.
          wp; skip; progress; smt.
        wp => /=; rnd predT; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
      * kill 9.
          if => //; first by wp; skip; progress.
          case (0 <= (oget qo).`3).
          - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
            wp => /=; kill 7.
              sp; if => //; first by wp; rnd; skip; progress.
            wp => /=; kill 3.
              sp; if => //; first by wp; rnd; skip; progress.
            wp; skip; progress; smt.
          wp; skip; progress; smt.
          - rcondf 4; progress; first by wp; skip; progress.
            wp; skip; progress.
        wp => /=; while (0 <= i <= size sc) (size sc - i) => //=; progress.
          wp; skip; progress; smt.
        wp => /=; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
  qed.

  lemma G9_o_ll:
    islossless G9.o.
  proof.
    move : di_ll dut_ll => _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      - wp; rnd; skip; progress.
      - wp; skip; progress.
    + sp; if => //.
      - sp; if => //.
        + wp; rnd; skip; progress.
        + wp; skip; progress.
  qed.

  local lemma G8_G9_indistinguishable_resnotbad
    (D <: SSEDistROM{G8,G9,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
    Pr[SSEExpROM(G8, G9, OracleCallsCounter(D)).game(true) @ &m : res /\ !G8_Client.bad_update_h2t] <= Pr[SSEExpROM(G8, G9, OracleCallsCounter(D)).game(false) @ &m : res].
  proof.
    move : dut_ll di_ll dmapquery_ll dstoken_ll dkey_ll; rewrite /is_lossless => _ _ _ _ _.
    move => oracle.
    byequiv => //.
    symmetry.
    proc*.
    inline SSEExpROM(G8, G9, OracleCallsCounter(D)).game.
    rcondf{1} 2; first by progress; first by wp; skip; progress.
    rcondt{2} 2; first by progress; first by wp; skip; progress.
    inline*; wp.
    call (_: G8_Client.bad_update_h2t, ={glob OracleCallsCounter, glob RF, glob G4_Server}
         /\   (G8_Client.et, G8_Client.utt, G8_Client.ws, G8_Client.h1t, G8_Client.h2t, G8_Client.sk, G8_Client.bad_rf_coll, G8_Client.bad_h1, G8_Client.bad_h2){2}
            = (G9_Client.et, G9_Client.utt, G9_Client.ws, G9_Client.h1t, G9_Client.h2t, G9_Client.sk, G9_Client.bad_rf_coll, G9_Client.bad_h1, G9_Client.bad_h2){1}
    ) => //.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: update
 *)
proc.
sp; if => //.
inline*.
sp; if => //; last by wp; skip; progress.
seq 3 3: (={kw, q1, i1, o0, x, glob OracleCallsCounter, glob RF, glob G4_Server}
         /\   (G8_Client.et, G8_Client.utt, G8_Client.ws, G8_Client.h1t, G8_Client.h2t, G8_Client.sk, G8_Client.bad_rf_coll, G8_Client.bad_h1, G8_Client.bad_h2){2}
            = (G9_Client.et, G9_Client.utt, G9_Client.ws, G9_Client.h1t, G9_Client.h2t, G9_Client.sk, G9_Client.bad_rf_coll, G9_Client.bad_h1, G9_Client.bad_h2){1}
         /\ (o0 = ADD){2}
  ).
sp; wp; if => //.
wp; rnd; skip; progress.

if => //; first by wp; skip; progress; smt.
seq 1 1: (={kw, q1, i1, o0, x, sc, s, c, glob OracleCallsCounter, glob RF, glob G4_Server}
         /\   (G8_Client.et, G8_Client.utt, G8_Client.ws, G8_Client.h1t, G8_Client.h2t, G8_Client.sk, G8_Client.bad_rf_coll, G8_Client.bad_h1, G8_Client.bad_h2){2}
            = (G9_Client.et, G9_Client.utt, G9_Client.ws, G9_Client.h1t, G9_Client.h2t, G9_Client.sk, G9_Client.bad_rf_coll, G9_Client.bad_h1, G9_Client.bad_h2){1}
         /\ (o0 = ADD){2}
  ).
if => //.
wp; rnd; wp; skip; progress.
wp; skip; progress.
sp; if => //; first by wp; skip; progress; smt.
sp; if{2} => //=.
wp; rnd{1}; rnd{1}; wp; skip; progress => //.
wp; rnd; rnd; skip; progress; smt.
(*
 * The update call in the real world is required to terminate
 *)
progress.
proc.
inline*.
sp; if => //.
wp; sp; if => //; last by wp; skip; progress.
simplify; kill 4.
case (fmap_collision RF.m).
rcondt 1 => //; first by wp; skip; progress
rcondf 1 => //.
if => //; first by wp; skip; progress.
kill 3.
if => //; first by wp; skip; progress.
wp; rnd; rnd; skip; progress.
if => //; last by wp; skip; progress.
wp; rnd; wp; skip; progress; smt.
wp; sp; if => //.
rnd; skip; progress; smt.
(*
 * update called in the bad-event state does not affect the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G8_Client.bad_update_h2t) => //.
kill 2; first by if => //; inline*; wp; skip; progress.
inline*.
sp; if => //; last by wp; skip; progress.
sp; if => //.
  * seq 2: (G8_Client.bad_update_h2t) => //; last by hoare; wp; rnd; skip; progress.
      wp; rnd; skip; progress.
    sp; if => //; first by wp; skip; progress.
    if => //.
    - seq 2: (G8_Client.bad_update_h2t) => //; last by hoare; rnd; wp; skip; progress.
        rnd; wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress.
    - sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress.
  * sp; if => //; first by wp; skip; progress.
    if => //.
    - seq 2: (G8_Client.bad_update_h2t) => //; last by hoare; rnd; wp; skip; progress.
        rnd; wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress.
    - sp; if => //; first by wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress => //.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: query
 *)
sim.
(*
 * The query call in the real world is required to terminate
 *)
progress.
proc.
inline*.
sp; if => //.
wp => /=.
sp; if => //.
* rcondt 3; progress; first by wp; skip; progress.
  wp; skip; progress.
* rcondf 11; progress.
    wp; kill 9.
      while (true) (size sc - i); progress; first by wp; skip; progress; smt.
      wp; skip; progress; smt.
    wp => /=; sp; if => //.
  wp; while (true) (c0 + 1 - i0); progress.
    wp; sp; if => //.
    - swap 4 -3; swap 5 -3; swap 6 -3; sp; if => //.
      + wp; rnd; wp; rnd; skip; progress; smt.
      + wp; rnd; skip; progress; smt.
    - sp; if => //.
      + wp; rnd; skip; progress; smt.
      + wp; skip; progress; smt.
  wp; while (true) (size sc - i); progress.
    wp; skip; progress; smt.
  wp => /=; sp; if => //.
  + rnd (predT); skip; progress; smt.
  + skip; progress; smt.
(*
 * query called in the bad-event state must keep the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G8_Client.bad_update_h2t) => //.
inline*.
sp; if => //.
* rcondt 3; progress; first by wp; skip; progress.
  wp; skip; progress.
* rcondf 11; progress.
    wp; kill 9.
      while (true) (size sc - i); progress; first by wp; skip; progress; smt.
      wp; skip; progress; smt.
    wp => /=; sp; if => //.
  wp; while (G8_Client.bad_update_h2t) (c0 + 1 - i0); progress.
    wp => /=; kill 7.
      if => //; first by wp; rnd; skip; progress; smt.
    wp; sp; if => //; last by skip; progress; smt.
    wp; rnd; skip; progress; smt.
  wp; kill 9.
    wp; while (true) (size sc - i); progress.
      wp; skip; progress; smt.
    wp; skip; progress; smt.
  rewrite /=.
  wp => /=; sp; if => //.
  + rnd (predT); skip; progress; smt.
  + skip; progress; smt.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: o
 *)
sim.
(*
 * The o call in the real world is required to terminate
 *)
progress.
proc.
sp; if => //.
wp; inline*.
sp; if => //.
sp; if => //; last by wp; skip; progress.
wp; rnd; wp; skip; progress.
sp; if => //; last by wp; skip; progress.
sp; if => //; last by wp; skip; progress.
wp; rnd; wp; skip; progress.
(*
 * o called in the bad-event state keeps the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G8_Client.bad_update_h2t).
sp; if => //.
wp; inline*.
sp; if => //.
wp; rnd; skip; progress.
wp; skip; progress.
if => //.
inline *.
sp; if => //.
wp; rnd; wp; skip; progress.
wp; skip; progress.
skip; progress.
(*
 * No further procedures are left. Lastly, we need to prove that, in the meanwhile that the distinguisher does whatever she wants, the consistency, hence the indistinguishability, is kept in the case no bad events occur.
 *)
wp; rnd; wp; skip; progress.
move : (H1 H3).
move => [rwme] _.
rewrite rwme //.
  qed.

  local lemma G8_G9_indistinguishable_uptoresbad
    (D <: SSEDistROM{G8,G9,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
      Pr[SSEExpROM(G8, G9, OracleCallsCounter(D)).game(true) @ &m : res]
    <= Pr[SSEExpROM(G8, G9, OracleCallsCounter(D)).game(false) @ &m : res]
    + Pr[SSEExpROM(G8, G9, OracleCallsCounter(D)).game(true) @ &m : res /\ G8_Client.bad_update_h2t].
  proof.
    move => oracle.
    rewrite RField.addrC Pr[mu_split (G8_Client.bad_update_h2t)] ler_add2l.
    apply (G8_G9_indistinguishable_resnotbad D &m oracle).
  qed.

  lemma G8_G9_indistinguishable_uptobad
    (D <: SSEDistROM{G8,G9,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
      Pr[SSEExpROM(G8, G9, OracleCallsCounter(D)).game(true) @ &m : res]
    <= Pr[SSEExpROM(G8, G9, OracleCallsCounter(D)).game(false) @ &m : res]
    + Pr[SSEExpROM(G8, G9, OracleCallsCounter(D)).game(true) @ &m : G8_Client.bad_update_h2t].
  proof.
    move => oracle.
    pose p5 := Pr[SSEExpROM(G8, G9, OracleCallsCounter(D)).game(true) @ &m : res].
    pose p6 := Pr[SSEExpROM(G8, G9, OracleCallsCounter(D)).game(false) @ &m : res].
    rewrite RField.addrC RField.addrC Pr[mu_split res] andbC.
    pose prb := Pr[SSEExpROM(G8, G9, OracleCallsCounter(D)).game(true) @ &m : res /\ G8_Client.bad_update_h2t].
    rewrite andbC RField.addrA.
    pose prCb := Pr[SSEExpROM(G8, G9, OracleCallsCounter(D)).game(true) @ &m : !res /\ G8_Client.bad_update_h2t].
    rewrite (ler_trans (p6 + prb)).
    rewrite /p5 /p6 /prb.
    apply (G8_G9_indistinguishable_uptoresbad D &m oracle).
    rewrite -RField.addrA ler_add2l -RField.addr0 ler_add2l.
    smt.
  qed.

  (*
   * === Part10 ===
   * We start no to handle the bad events, reducing to other experiments
   * -- bad_update_h1t
   *)
  module G10_Client: SSEClient = {
    var sk: tau
    var ws: (query, stoken list) fmap

    var utt: (query * int, utoken) fmap
    var et: (query * int, index) fmap
    var h1t: (mapquery * stoken, utoken) fmap
    var h2t: (mapquery * stoken, index) fmap

    var bad_rf_coll: bool (* collision in the random function *)
    var bad_update_bt: bool (* prediction in backup tables *)
    var bad_update_h1t: bool (* guess in h1t *)
    var bad_update_h2t: bool (* guess in h2t *)
    var bad_h1: bool (* bad event raised by h1 *)
    var bad_h2: bool (* bad event raised by h2 *)

    proc setup(): setupserver = {
      var pk;

      (pk, sk) <@ CTP.index();
      RF.init();
      ws <- empty;
      utt <- empty;
      et <- empty;
      h1t <- empty;
      h2t <- empty;

      bad_rf_coll <- false;
      bad_update_bt <- false;
      bad_update_h1t <- false;
      bad_update_h2t <- false;
      bad_h1 <- false;
      bad_h2 <- false;

      return pk;
    }

    (* Simulating the hash functions *)
    module SimH1: HashFunction1 = {
      proc hash(kw: mapquery, s: stoken): utoken = {
        var y;

        if (!(dom h1t (kw, s))) {
          y <$ dutoken;
          h1t.[(kw, s)] <- y;
        }

        return oget h1t.[(kw, s)];
      }
    }

    module SimH2: HashFunction2 = {
      proc hash(kw: mapquery, s: stoken): index = {
        var y;

        if (!(dom h2t (kw, s))) {
          y <$ di;
          h2t.[(kw, s)] <- y;
        }

        return oget h2t.[(kw, s)];
      }
    }

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var kw, s, c, sc, idx, ti;

      if (o = ADD) {
        kw <@ RF.f(q);
        if (fmap_collision RF.m) {
          bad_rf_coll <- true;
          ti <- None;
        } else {
          if (!dom ws q) {
            sc <- [];
            s <$ dstoken;
            c <- 0;
          } else {
            sc <- oget ws.[q];
            c <- size sc;
            s <@ CTP.backward(sk, last witness sc);
          }
          ws.[q] <- sc ++ [s];
          utt.[(q, c)] <$ dutoken;
          idx <$ di;
          et.[(q, c)] <- idx;
          idx <- i +^ idx;
          ti <- Some(oget utt.[(q, c)], idx);
        }
      } else {
        ti <- None;
      }
     
      return ti;
    }

    proc query(q: query): (mapquery * stoken * int) option = {
      var kw, sc, c, i, s;
      var r: (mapquery * stoken * int) option;

      if (!dom ws q) {
        r <- None;
      } else {
        kw <@ RF.f(q);
        if (fmap_collision RF.m) {
          bad_rf_coll <- true;
        }

        sc <- oget ws.[q];
        c <- size sc - 1;
        r <- Some (kw, nth witness sc c, c);

        (* Lazily programming the hash tables *)
        i <- 0;
        while (i < size sc) {
          s <- nth witness sc i;
          h1t.[(kw, s)] <- oget utt.[(q, i)];
          h2t.[(kw, s)] <- oget et.[(q, i)];
          i <- i + 1;
        }
      }

      return r;
    }

    proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
      var h1, h2, h;

      h <- None;
      if     (i = HASH1) {
        h1 <@ SimH1.hash(argv);
        h <- Some(Some(h1), None);
      } elif (i = HASH2) {
        h2 <@ SimH2.hash(argv);
        h <- Some(None, Some(h2));
      }

      return h;
    }
  }.
  module G10 = SSEProtocol(G10_Client, G4_Server(G10_Client.SimH1, G10_Client.SimH2)).

  lemma G10_setup_ll:
    is_lossless dcoins =>
    islossless G10.setup.
  proof.
    move : dkey_ll => _ dcoins_ll.
    proc; inline *.
    wp; rnd; skip; progress.
  qed.

  lemma G10_update_ll:
    islossless G10.update.
  proof.
    move : dmapquery_ll di_ll dut_ll dstoken_ll cdistr_ful => dmq_ll di_ll _ _ [cd_ll cd_fun].
    proc; inline*.
    wp => /=; kill 4.
      if => //; last by wp; skip; progress.
      wp; kill 4.
        case (fmap_collision RF.m).
        + rcondt 1; progress.
          wp; skip; progress.
        + rcondf 1; progress.
          if => //.
          * wp; rnd; wp; rnd; wp; rnd; wp; skip; progress.
          * wp; rnd; wp; rnd; wp; skip; progress.
      wp => /=; sp; if => //; first by rnd; skip; progress.
    wp; skip; progress.
  qed.

  lemma G10_query_ll:
    islossless G10.query.
  proof.
    move : dmapquery_ll dstoken_ll di_ll dut_ll => _ _ _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //; first by wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress => //.
    + sp; if => //.
      * kill 10.
          if => //; first by wp; skip; progress.
          case (0 <= (oget qo).`3).
          - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
            wp => /=; kill 7.
              sp; if => //; first by wp; rnd; skip; progress.
            wp => /=; kill 3.
              sp; if => //; first by wp; rnd; skip; progress.
            wp; skip; progress; smt.
          wp; skip; progress; smt.
          - rcondf 4; progress; first by wp; skip; progress.
            wp; skip; progress.
        wp => /=; while (0 <= i <= size sc) (size sc - i) => //=; progress.
          wp; skip; progress; smt.
        wp => /=; rnd predT; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
      * kill 9.
          if => //; first by wp; skip; progress.
          case (0 <= (oget qo).`3).
          - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
            wp => /=; kill 7.
              sp; if => //; first by wp; rnd; skip; progress.
            wp => /=; kill 3.
              sp; if => //; first by wp; rnd; skip; progress.
            wp; skip; progress; smt.
          wp; skip; progress; smt.
          - rcondf 4; progress; first by wp; skip; progress.
            wp; skip; progress.
        wp => /=; while (0 <= i <= size sc) (size sc - i) => //=; progress.
          wp; skip; progress; smt.
        wp => /=; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
  qed.

  lemma G10_o_ll:
    islossless G10.o.
  proof.
    move : di_ll dut_ll => _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      - wp; rnd; skip; progress.
      - wp; skip; progress.
    + sp; if => //.
      - sp; if => //.
        + wp; rnd; skip; progress.
        + wp; skip; progress.
  qed.

  local lemma G9_G10_indistinguishable_resnotbad
    (D <: SSEDistROM{G9,G10,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
    Pr[SSEExpROM(G9, G10, OracleCallsCounter(D)).game(true) @ &m : res /\ !G9_Client.bad_update_h1t] <= Pr[SSEExpROM(G9, G10, OracleCallsCounter(D)).game(false) @ &m : res].
  proof.
    move : dut_ll di_ll dmapquery_ll dstoken_ll dkey_ll; rewrite /is_lossless => _ _ _ _ _.
    move => oracle.
    byequiv => //.
    symmetry.
    proc*.
    inline SSEExpROM(G9, G10, OracleCallsCounter(D)).game.
    rcondf{1} 2; first by progress; first by wp; skip; progress.
    rcondt{2} 2; first by progress; first by wp; skip; progress.
    inline*; wp.
    call (_: G9_Client.bad_update_h1t, ={glob OracleCallsCounter, glob RF, glob G4_Server}
         /\   (G9_Client.et, G9_Client.utt, G9_Client.ws, G9_Client.h1t, G9_Client.h2t, G9_Client.sk, G9_Client.bad_rf_coll, G9_Client.bad_h1, G9_Client.bad_h2){2}
            = (G10_Client.et, G10_Client.utt, G10_Client.ws, G10_Client.h1t, G10_Client.h2t, G10_Client.sk, G10_Client.bad_rf_coll, G10_Client.bad_h1, G10_Client.bad_h2){1}
    ) => //.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: update
 *)
proc.
sp; if => //.
inline*.
sp; if => //; last by wp; skip; progress.
seq 3 3: (={kw, q1, i1, o0, x, glob OracleCallsCounter, glob RF, glob G4_Server}
         /\   (G9_Client.et, G9_Client.utt, G9_Client.ws, G9_Client.h1t, G9_Client.h2t, G9_Client.sk, G9_Client.bad_rf_coll, G9_Client.bad_h1, G9_Client.bad_h2){2}
            = (G10_Client.et, G10_Client.utt, G10_Client.ws, G10_Client.h1t, G10_Client.h2t, G10_Client.sk, G10_Client.bad_rf_coll, G10_Client.bad_h1, G10_Client.bad_h2){1}
         /\ (o0 = ADD){2}
  ).
sp; wp; if => //.
wp; rnd; skip; progress.

if => //; first by wp; skip; progress; smt.
seq 1 1: (={kw, q1, i1, o0, x, sc, s, c, glob OracleCallsCounter, glob RF, glob G4_Server}
         /\   (G9_Client.et, G9_Client.utt, G9_Client.ws, G9_Client.h1t, G9_Client.h2t, G9_Client.sk, G9_Client.bad_rf_coll, G9_Client.bad_h1, G9_Client.bad_h2){2}
            = (G10_Client.et, G10_Client.utt, G10_Client.ws, G10_Client.h1t, G10_Client.h2t, G10_Client.sk, G10_Client.bad_rf_coll, G10_Client.bad_h1, G10_Client.bad_h2){1}
         /\ (o0 = ADD){2}
  ).
if => //.
wp; rnd; wp; skip; progress.
wp; skip; progress.
sp; if{2} => //=.
wp; rnd{1}; rnd{1}; wp; skip; progress => //.
wp; rnd; rnd; skip; progress; smt.
(*
 * The update call in the real world is required to terminate
 *)
progress.
proc.
inline*.
sp; if => //.
wp; sp; if => //; last by wp; skip; progress.
simplify; kill 4.
case (fmap_collision RF.m).
rcondt 1 => //; first by wp; skip; progress
rcondf 1 => //.
if => //; first by wp; skip; progress.
if => //; last by wp; rnd; rnd; wp; skip; progress.
wp; rnd; rnd; wp; rnd; wp; skip; progress; smt.
wp; sp; if => //.
rnd; skip; progress; smt.
(*
 * update called in the bad-event state does not affect the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G9_Client.bad_update_h1t) => //.
kill 2; first by if => //; inline*; wp; skip; progress.
inline*.
sp; if => //; last by wp; skip; progress.
sp; if => //.
  * seq 2: (G9_Client.bad_update_h1t) => //; last by hoare; wp; rnd; skip; progress.
      wp; rnd; skip; progress.
    sp; if => //; first by wp; skip; progress.
    if => //.
    - seq 2: (G9_Client.bad_update_h1t) => //; last by hoare; rnd; wp; skip; progress.
        rnd; wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress.
    - sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress.
  * sp; if => //; first by wp; skip; progress.
    if => //.
    - seq 2: (G9_Client.bad_update_h1t) => //; last by hoare; rnd; wp; skip; progress.
        rnd; wp; skip; progress.
      sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress.
    - sp; if => //; first by wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress => //.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: query
 *)
sim.
(*
 * The query call in the real world is required to terminate
 *)
progress; proc; sp; if => //; wp.
inline*.
wp; kill 5.
    if => //; first by wp; skip; progress.
    wp => /=; sp; while (true) (c0 + 1 - i0); progress.
      wp; kill 7; first by if => //; wp; rnd; skip; progress.
      wp; kill 3; first by if => //; wp; rnd; skip; progress.
      wp => /=; skip; progress; smt.
    skip; progress; smt.
wp; kill 3.
  if => //; first by wp; skip; progress.
    wp => /=; sp; while (true) (size sc - i); progress.
      wp => /=; skip; progress; smt.
    wp; if => //; first by rnd (predT); skip; progress; smt.
    skip; progress; smt.
  wp; skip; progress; smt.
(*
 * query called in the bad-event state must keep the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G9_Client.bad_update_h1t) => //.
inline*.
sp; if => //.
* rcondt 3; progress; first by wp; skip; progress.
  wp; skip; progress.
* rcondf 11; progress.
    wp; kill 9.
      while (true) (size sc - i); progress; first by wp; skip; progress; smt.
      wp; skip; progress; smt.
    wp => /=; sp; if => //.
  wp; while (G9_Client.bad_update_h1t) (c0 + 1 - i0); progress.
    wp => /=; kill 7.
      if => //; first by wp; rnd; skip; progress; smt.
    wp; sp; if => //; last by skip; progress; smt.
    wp; rnd; skip; progress; smt.
  wp; kill 9.
    wp; while (true) (size sc - i); progress.
      wp; skip; progress; smt.
    wp; skip; progress; smt.
  rewrite /=.
  wp => /=; sp; if => //.
  + rnd (predT); skip; progress; smt.
  + skip; progress; smt.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: o
 *)
sim.
(*
 * The o call in the real world is required to terminate
 *)
progress.
proc.
sp; if => //.
wp; inline*.
sp; if => //.
sp; if => //; last by wp; skip; progress.
wp; rnd; wp; skip; progress.
sp; if => //; last by wp; skip; progress.
sp; if => //; last by wp; skip; progress.
wp; rnd; wp; skip; progress.
(*
 * o called in the bad-event state keeps the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G9_Client.bad_update_h1t).
sp; if => //.
wp; inline*.
sp; if => //.
wp; rnd; skip; progress.
wp; skip; progress.
if => //.
inline *.
sp; if => //.
wp; rnd; wp; skip; progress.
wp; skip; progress.
skip; progress.
(*
 * No further procedures are left. Lastly, we need to prove that, in the meanwhile that the distinguisher does whatever she wants, the consistency, hence the indistinguishability, is kept in the case no bad events occur.
 *)
wp; rnd; wp; skip; progress.
move : (H1 H3).
move => [rwme] _.
rewrite rwme //.
  qed.

  local lemma G9_G10_indistinguishable_uptoresbad
    (D <: SSEDistROM{G9,G10,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
      Pr[SSEExpROM(G9, G10, OracleCallsCounter(D)).game(true) @ &m : res]
    <= Pr[SSEExpROM(G9, G10, OracleCallsCounter(D)).game(false) @ &m : res]
    + Pr[SSEExpROM(G9, G10, OracleCallsCounter(D)).game(true) @ &m : res /\ G9_Client.bad_update_h1t].
  proof.
    move => oracle.
    rewrite RField.addrC Pr[mu_split (G9_Client.bad_update_h1t)] ler_add2l.
    apply (G9_G10_indistinguishable_resnotbad D &m oracle).
  qed.

  lemma G9_G10_indistinguishable_uptobad
    (D <: SSEDistROM{G9,G10,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
      Pr[SSEExpROM(G9, G10, OracleCallsCounter(D)).game(true) @ &m : res]
    <= Pr[SSEExpROM(G9, G10, OracleCallsCounter(D)).game(false) @ &m : res]
    + Pr[SSEExpROM(G9, G10, OracleCallsCounter(D)).game(true) @ &m : G9_Client.bad_update_h1t].
  proof.
    move => oracle.
    pose p5 := Pr[SSEExpROM(G9, G10, OracleCallsCounter(D)).game(true) @ &m : res].
    pose p6 := Pr[SSEExpROM(G9, G10, OracleCallsCounter(D)).game(false) @ &m : res].
    rewrite RField.addrC RField.addrC Pr[mu_split res] andbC.
    pose prb := Pr[SSEExpROM(G9, G10, OracleCallsCounter(D)).game(true) @ &m : res /\ G9_Client.bad_update_h1t].
    rewrite andbC RField.addrA.
    pose prCb := Pr[SSEExpROM(G9, G10, OracleCallsCounter(D)).game(true) @ &m : !res /\ G9_Client.bad_update_h1t].
    rewrite (ler_trans (p6 + prb)).
    rewrite /p5 /p6 /prb.
    apply (G9_G10_indistinguishable_uptoresbad D &m oracle).
    rewrite -RField.addrA ler_add2l -RField.addr0 ler_add2l.
    smt.
  qed.

  (*
   * === Part11 ===
   * We start no to handle the bad events, reducing to other experiments
   * -- bad_rf_coll
   *)
  module G11_Client: SSEClient = {
    var sk: tau
    var ws: (query, stoken list) fmap

    var utt: (query * int, utoken) fmap
    var et: (query * int, index) fmap
    var h1t: (mapquery * stoken, utoken) fmap
    var h2t: (mapquery * stoken, index) fmap

    var bad_rf_coll: bool (* collision in the random function *)
    var bad_update_bt: bool (* prediction in backup tables *)
    var bad_update_h1t: bool (* guess in h1t *)
    var bad_update_h2t: bool (* guess in h2t *)
    var bad_h1: bool (* bad event raised by h1 *)
    var bad_h2: bool (* bad event raised by h2 *)

    proc setup(): setupserver = {
      var pk;

      (pk, sk) <@ CTP.index();
      RF.init();
      ws <- empty;
      utt <- empty;
      et <- empty;
      h1t <- empty;
      h2t <- empty;

      bad_rf_coll <- false;
      bad_update_bt <- false;
      bad_update_h1t <- false;
      bad_update_h2t <- false;
      bad_h1 <- false;
      bad_h2 <- false;

      return pk;
    }

    (* Simulating the hash functions *)
    module SimH1: HashFunction1 = {
      proc hash(kw: mapquery, s: stoken): utoken = {
        var y;

        if (!(dom h1t (kw, s))) {
          y <$ dutoken;
          h1t.[(kw, s)] <- y;
        }

        return oget h1t.[(kw, s)];
      }
    }

    module SimH2: HashFunction2 = {
      proc hash(kw: mapquery, s: stoken): index = {
        var y;

        if (!(dom h2t (kw, s))) {
          y <$ di;
          h2t.[(kw, s)] <- y;
        }

        return oget h2t.[(kw, s)];
      }
    }

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var kw, s, c, sc, idx, ti;

      if (o = ADD) {
        kw <@ RF.f(q);
        if (!dom ws q) {
          sc <- [];
          s <$ dstoken;
          c <- 0;
        } else {
          sc <- oget ws.[q];
          c <- size sc;
          s <@ CTP.backward(sk, last witness sc);
        }
        ws.[q] <- sc ++ [s];
        utt.[(q, c)] <$ dutoken;
        idx <$ di;
        et.[(q, c)] <- idx;
        idx <- i +^ idx;
        ti <- Some(oget utt.[(q, c)], idx);
      } else {
        ti <- None;
      }
     
      return ti;
    }

    proc query(q: query): (mapquery * stoken * int) option = {
      var kw, sc, c, i, s;
      var r: (mapquery * stoken * int) option;

      if (!dom ws q) {
        r <- None;
      } else {
        kw <@ RF.f(q);
        sc <- oget ws.[q];
        c <- size sc - 1;
        r <- Some (kw, nth witness sc c, c);

        (* Lazily programming the hash tables *)
        i <- 0;
        while (i < size sc) {
          s <- nth witness sc i;
          h1t.[(kw, s)] <- oget utt.[(q, i)];
          h2t.[(kw, s)] <- oget et.[(q, i)];
          i <- i + 1;
        }
      }

      return r;
    }

    proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
      var h1, h2, h;

      h <- None;
      if     (i = HASH1) {
        h1 <@ SimH1.hash(argv);
        h <- Some(Some(h1), None);
      } elif (i = HASH2) {
        h2 <@ SimH2.hash(argv);
        h <- Some(None, Some(h2));
      }

      return h;
    }
  }.
  module G11 = SSEProtocol(G11_Client, G4_Server(G11_Client.SimH1, G11_Client.SimH2)).

  lemma G11_setup_ll:
    is_lossless dcoins =>
    islossless G11.setup.
  proof.
    move : dkey_ll => _ dcoins_ll.
    proc; inline *.
    wp; rnd; skip; progress.
  qed.

  lemma G11_update_ll:
    islossless G11.update.
  proof.
    move : dmapquery_ll di_ll dut_ll dstoken_ll cdistr_ful => dmq_ll di_ll _ _ [cd_ll cd_fun].
    proc; inline*.
    wp => /=; kill 4.
      if => //; last by wp; skip; progress.
      sp; if => //.
      + swap 3 -2; if => //.
        - wp; rnd; rnd; wp; rnd; wp; rnd; wp; skip; progress.
        - wp; rnd; rnd; wp; rnd; wp; skip; progress.
      + sp; if => //.
        - wp; rnd; rnd; wp; rnd; wp; skip; progress.
        - wp; rnd; rnd; wp; skip; progress.
    wp; skip; progress.
  qed.

  lemma G11_query_ll:
    islossless G11.query.
  proof.
    move : dmapquery_ll dstoken_ll di_ll dut_ll => _ _ _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //; first by wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress => //.
    + kill 10.
        if => //; first by wp; skip; progress.
        case (0 <= (oget qo).`3).
        - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //; first by wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress; smt.
        - rcondf 4; progress; first by wp; skip; progress.
          wp; skip; progress.
      wp => /=; while (0 <= i <= size sc) (size sc - i) => //=; progress.
        wp; skip; progress; smt.
      wp => /=; sp; if => //.
      * rnd; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
      * skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
  qed.

  lemma G11_o_ll:
    islossless G11.o.
  proof.
    move : di_ll dut_ll => _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      - wp; rnd; skip; progress.
      - wp; skip; progress.
    + sp; if => //.
      - sp; if => //.
        + wp; rnd; skip; progress.
        + wp; skip; progress.
  qed.

  local lemma G10_G11_indistinguishable_resnotbad
    (D <: SSEDistROM{G10,G11,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
    Pr[SSEExpROM(G10, G11, OracleCallsCounter(D)).game(true) @ &m : res /\ !G10_Client.bad_rf_coll] <= Pr[SSEExpROM(G10, G11, OracleCallsCounter(D)).game(false) @ &m : res].
  proof.
    move : dut_ll di_ll dmapquery_ll dstoken_ll dkey_ll; rewrite /is_lossless => _ _ _ _ _.
    move => oracle.
    byequiv => //.
    symmetry.
    proc*.
    inline SSEExpROM(G10, G11, OracleCallsCounter(D)).game.
    rcondf{1} 2; first by progress; first by wp; skip; progress.
    rcondt{2} 2; first by progress; first by wp; skip; progress.
    inline*; wp.
    call (_: G10_Client.bad_rf_coll, ={glob OracleCallsCounter, glob RF, glob G4_Server}
         /\   (G10_Client.et, G10_Client.utt, G10_Client.ws, G10_Client.h1t, G10_Client.h2t, G10_Client.sk, G10_Client.bad_rf_coll, G10_Client.bad_h1, G10_Client.bad_h2){2}
            = (G11_Client.et, G11_Client.utt, G11_Client.ws, G11_Client.h1t, G11_Client.h2t, G11_Client.sk, G11_Client.bad_rf_coll, G11_Client.bad_h1, G11_Client.bad_h2){1}
    ) => //.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: update
 *)
proc.
sp; if => //.
inline*.
sp; if => //; last by wp; skip; progress.
seq 3 3: (={kw, q1, i1, o0, x, glob OracleCallsCounter, glob RF, glob G4_Server}
         /\   (G10_Client.et, G10_Client.utt, G10_Client.ws, G10_Client.h1t, G10_Client.h2t, G10_Client.sk, G10_Client.bad_rf_coll, G10_Client.bad_h1, G10_Client.bad_h2){2}
            = (G11_Client.et, G11_Client.utt, G11_Client.ws, G11_Client.h1t, G11_Client.h2t, G11_Client.sk, G11_Client.bad_rf_coll, G11_Client.bad_h1, G11_Client.bad_h2){1}
         /\ (o0 = ADD){2}
  ).
sp; wp; if => //.
wp; rnd; skip; progress.

if{2} => //.
wp; rnd{1}; rnd{1}; wp.
if{1} => //.
wp; rnd{1}; wp; skip; progress.
wp; skip; progress.
sim.
(*
 * The update call in the real world is required to terminate
 *)
progress.
proc.
inline*.
sp; if => //.
wp; sp; if => //; last by wp; skip; progress.
wp => /=.
kill 7; first by rnd; skip; progress.
kill 6; first by rnd; skip; progress.
wp; simplify.
kill 4.
  if => //; first by wp; rnd; wp; skip; progress.
  wp; skip; progress.
wp; sp; if => //.
rnd; skip; progress; smt.
(*
 * update called in the bad-event state does not affect the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G10_Client.bad_rf_coll) => //.
kill 2; first by if => //; inline*; wp; skip; progress.
inline*.
sp; if => //; last by wp; skip; progress.
sp; if => //.
  * seq 2: (G10_Client.bad_rf_coll) => //; last by hoare; wp; rnd; skip; progress.
      wp; rnd; skip; progress.
    sp; if => //; first by wp; skip; progress.
    if => //.
    - seq 2: (G10_Client.bad_rf_coll) => //; last by hoare; rnd; wp; skip; progress.
        rnd; wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress.
    - wp; rnd; wp; rnd; wp; skip; progress.
  * sp; if => //; first by wp; skip; progress.
    if => //.
    - seq 2: (G10_Client.bad_rf_coll) => //; last by hoare; rnd; wp; skip; progress.
        rnd; wp; skip; progress.
      wp; rnd; wp; rnd; wp; skip; progress.
    - wp; rnd; wp; rnd; wp; skip; progress => //.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: query
 *)
proc.
sp; if => //.
wp; inline*.
sp; wp; if => //.
+ rcondt{1} 3; progress; first by wp; skip; progress.
  rcondt{2} 3; progress; first by wp; skip; progress.
  wp; skip; progress.
+ rcondf{2} 11; progress.
    kill 9.
      while (true) (size sc - i) => //; progress.
        wp; skip; progress; smt.
      skip; progress; smt.
    wp; sp; if => //; first by rnd; skip; progress.
  rcondf{1} 10; progress.
    kill 8.
      while (true) (size sc - i) => //; progress.
        wp; skip; progress; smt.
      skip; progress; smt.
    wp; sp; if => //.
  seq 3 3: (={kw, q1, x, glob OracleCallsCounter, glob RF, glob G4_Server}
         /\   (G10_Client.et, G10_Client.utt, G10_Client.ws, G10_Client.h1t, G10_Client.h2t, G10_Client.sk, G10_Client.bad_rf_coll, G10_Client.bad_h1, G10_Client.bad_h2){2}
            = (G11_Client.et, G11_Client.utt, G11_Client.ws, G11_Client.h1t, G11_Client.h2t, G11_Client.sk, G11_Client.bad_rf_coll, G11_Client.bad_h1, G11_Client.bad_h2){1}
  ).
    sp; if => //; first by wp; rnd; skip; progress.
    wp; skip; progress.
    if{2} => //.
      wp; while (0 <= i0{2} <= c0{2} + 1 /\ ={i0, c0}).
        wp.
        kill{1} 7; first by if => //; wp; rnd; progress.
        kill{2} 7; first by if => //; wp; rnd; progress.
        wp.
        kill{1} 3; first by if => //; wp; rnd; progress.
        kill{2} 3; first by if => //; wp; rnd; progress.
        wp; skip; progress; smt.
      wp; while (0 <= i{2} <= size sc{2} /\ ={i, sc}).
        wp; skip; progress; smt.
      wp; skip; progress; smt.
    sim.
(*
 * The query call in the real world is required to terminate
 *)
progress.
proc.
inline*.
sp; if => //.
wp => /=.
sp; if => //.
* rcondt 3; progress; first by wp; skip; progress.
  wp; skip; progress.
* rcondf 10; progress.
    wp; kill 8.
      while (true) (size sc - i); progress; first by wp; skip; progress; smt.
      wp; skip; progress; smt.
    wp => /=; sp; if => //.
  wp; while (true) (c0 + 1 - i0); progress.
    wp; sp; if => //.
    - swap 4 -3; swap 5 -3; swap 6 -3; sp; if => //.
      + wp; rnd; wp; rnd; skip; progress; smt.
      + wp; rnd; skip; progress; smt.
    - sp; if => //.
      + wp; rnd; skip; progress; smt.
      + wp; skip; progress; smt.
  wp; while (true) (size sc - i); progress.
    wp; skip; progress; smt.
  wp => /=; sp; if => //.
  + rnd (predT); skip; progress; smt.
  + skip; progress; smt.
(*
 * query called in the bad-event state must keep the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G10_Client.bad_rf_coll) => //.
inline*.
sp; if => //.
* rcondt 3; progress; first by wp; skip; progress.
  wp; skip; progress.
* rcondf 11; progress.
    wp; kill 9.
      while (true) (size sc - i); progress; first by wp; skip; progress; smt.
      wp; skip; progress; smt.
    wp => /=; sp; if => //.
  wp; while (G10_Client.bad_rf_coll) (c0 + 1 - i0); progress.
    wp => /=; kill 7.
      if => //; first by wp; rnd; skip; progress; smt.
    wp; sp; if => //; last by skip; progress; smt.
    wp; rnd; skip; progress; smt.
  wp; kill 9.
    wp; while (true) (size sc - i); progress.
      wp; skip; progress; smt.
    wp; skip; progress; smt.
  rewrite /=.
  wp => /=; sp; if => //.
  + rnd (predT); skip; progress; smt.
  + skip; progress; smt.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: o
 *)
sim.
(*
 * The o call in the real world is required to terminate
 *)
progress.
proc.
sp; if => //.
wp; inline*.
sp; if => //.
sp; if => //; last by wp; skip; progress.
wp; rnd; wp; skip; progress.
sp; if => //; last by wp; skip; progress.
sp; if => //; last by wp; skip; progress.
wp; rnd; wp; skip; progress.
(*
 * o called in the bad-event state keeps the bad-event state
 *)
progress.
proc.
sp; if => //.
wp; call (_: G10_Client.bad_rf_coll).
sp; if => //.
wp; inline*.
sp; if => //.
wp; rnd; skip; progress.
wp; skip; progress.
if => //.
inline *.
sp; if => //.
wp; rnd; wp; skip; progress.
wp; skip; progress.
skip; progress.
(*
 * No further procedures are left. Lastly, we need to prove that, in the meanwhile that the distinguisher does whatever she wants, the consistency, hence the indistinguishability, is kept in the case no bad events occur.
 *)
wp; rnd; wp; skip; progress.
move : (H1 H3).
move => [rwme] _.
rewrite rwme //.
  qed.

  local lemma G10_G11_indistinguishable_uptoresbad
    (D <: SSEDistROM{G10,G11,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
      Pr[SSEExpROM(G10, G11, OracleCallsCounter(D)).game(true) @ &m : res]
    <= Pr[SSEExpROM(G10, G11, OracleCallsCounter(D)).game(false) @ &m : res]
    + Pr[SSEExpROM(G10, G11, OracleCallsCounter(D)).game(true) @ &m : res /\ G10_Client.bad_rf_coll].
  proof.
    move => oracle.
    rewrite RField.addrC Pr[mu_split (G10_Client.bad_rf_coll)] ler_add2l.
    apply (G10_G11_indistinguishable_resnotbad D &m oracle).
  qed.

  lemma G10_G11_indistinguishable_uptobad
    (D <: SSEDistROM{G10,G11,OracleCallsCounter}) &m:
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
      Pr[SSEExpROM(G10, G11, OracleCallsCounter(D)).game(true) @ &m : res]
    <= Pr[SSEExpROM(G10, G11, OracleCallsCounter(D)).game(false) @ &m : res]
    + Pr[SSEExpROM(G10, G11, OracleCallsCounter(D)).game(true) @ &m : G10_Client.bad_rf_coll].
  proof.
    move => oracle.
    pose p5 := Pr[SSEExpROM(G10, G11, OracleCallsCounter(D)).game(true) @ &m : res].
    pose p6 := Pr[SSEExpROM(G10, G11, OracleCallsCounter(D)).game(false) @ &m : res].
    rewrite RField.addrC RField.addrC Pr[mu_split res] andbC.
    pose prb := Pr[SSEExpROM(G10, G11, OracleCallsCounter(D)).game(true) @ &m : res /\ G10_Client.bad_rf_coll].
    rewrite andbC RField.addrA.
    pose prCb := Pr[SSEExpROM(G10, G11, OracleCallsCounter(D)).game(true) @ &m : !res /\ G10_Client.bad_rf_coll].
    rewrite (ler_trans (p6 + prb)).
    rewrite /p5 /p6 /prb.
    apply (G10_G11_indistinguishable_uptoresbad D &m oracle).
    rewrite -RField.addrA ler_add2l -RField.addr0 ler_add2l.
    smt.
  qed.

  (*
   * === Part12 ===
   * We start no to handle the bad events, reducing to other experiments
   * -- remove useless bad events
   *)
  module G12_Client: SSEClient = {
    var sk: tau
    var ws: (query, stoken list) fmap

    var utt: (query * int, utoken) fmap
    var et: (query * int, index) fmap
    var h1t: (mapquery * stoken, utoken) fmap
    var h2t: (mapquery * stoken, index) fmap

    proc setup(): setupserver = {
      var pk;

      (pk, sk) <@ CTP.index();
      RF.init();
      ws <- empty;
      utt <- empty;
      et <- empty;
      h1t <- empty;
      h2t <- empty;

      return pk;
    }

    (* Simulating the hash functions *)
    module SimH1: HashFunction1 = {
      proc hash(kw: mapquery, s: stoken): utoken = {
        var y;

        if (!(dom h1t (kw, s))) {
          y <$ dutoken;
          h1t.[(kw, s)] <- y;
        }

        return oget h1t.[(kw, s)];
      }
    }

    module SimH2: HashFunction2 = {
      proc hash(kw: mapquery, s: stoken): index = {
        var y;

        if (!(dom h2t (kw, s))) {
          y <$ di;
          h2t.[(kw, s)] <- y;
        }

        return oget h2t.[(kw, s)];
      }
    }

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var kw, s, c, sc, idx, ti;

      if (o = ADD) {
        kw <@ RF.f(q);
        if (!dom ws q) {
          sc <- [];
          s <$ dstoken;
          c <- 0;
        } else {
          sc <- oget ws.[q];
          c <- size sc;
          s <@ CTP.backward(sk, last witness sc);
        }
        ws.[q] <- sc ++ [s];
        utt.[(q, c)] <$ dutoken;
        idx <$ di;
        et.[(q, c)] <- idx;
        idx <- i +^ idx;
        ti <- Some(oget utt.[(q, c)], idx);
      } else {
        ti <- None;
      }
     
      return ti;
    }

    proc query(q: query): (mapquery * stoken * int) option = {
      var kw, sc, c, i, s;
      var r: (mapquery * stoken * int) option;

      if (!dom ws q) {
        r <- None;
      } else {
        kw <@ RF.f(q);

        sc <- oget ws.[q];
        c <- size sc - 1;
        r <- Some (kw, nth witness sc c, c);

        (* Lazily programming the hash tables *)
        i <- 0;
        while (i < size sc) {
          s <- nth witness sc i;
          h1t.[(kw, s)] <- oget utt.[(q, i)];
          h2t.[(kw, s)] <- oget et.[(q, i)];
          i <- i + 1;
        }
      }

      return r;
    }

    proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
      var h1, h2, h;

      h <- None;
      if     (i = HASH1) {
        h1 <@ SimH1.hash(argv);
        h <- Some(Some(h1), None);
      } elif (i = HASH2) {
        h2 <@ SimH2.hash(argv);
        h <- Some(None, Some(h2));
      }

      return h;
    }
  }.
  module G12 = SSEProtocol(G12_Client, G4_Server(G12_Client.SimH1, G12_Client.SimH2)).

  lemma G12_setup_ll:
    is_lossless dcoins =>
    islossless G12.setup.
  proof.
    move : dkey_ll => _ dcoins_ll.
    proc; inline *.
    wp; rnd; skip; progress.
  qed.

  lemma G12_update_ll:
    islossless G12.update.
  proof.
    move : dmapquery_ll di_ll dut_ll dstoken_ll cdistr_ful => dmq_ll di_ll _ _ [cd_ll cd_fun].
    proc; inline*.
    wp => /=; kill 4.
      if => //; last by wp; skip; progress.
      sp; if => //.
      + swap 3 -2; if => //.
        - wp; rnd; rnd; wp; rnd; wp; rnd; wp; skip; progress.
        - wp; rnd; rnd; wp; rnd; wp; skip; progress.
      + sp; if => //.
        - wp; rnd; rnd; wp; rnd; wp; skip; progress.
        - wp; rnd; rnd; wp; skip; progress.
    wp; skip; progress.
  qed.

  lemma G12_query_ll:
    islossless G12.query.
  proof.
    move : dmapquery_ll dstoken_ll di_ll dut_ll => _ _ _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //; first by wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress => //.
    + kill 10.
        if => //; first by wp; skip; progress.
        case (0 <= (oget qo).`3).
        - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //; first by wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress; smt.
        - rcondf 4; progress; first by wp; skip; progress.
          wp; skip; progress.
      wp => /=; while (0 <= i <= size sc) (size sc - i) => //=; progress.
        wp; skip; progress; smt.
      wp => /=; sp; if => //.
      * rnd; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
      * skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
  qed.

  lemma G12_o_ll:
    islossless G12.o.
  proof.
    move : di_ll dut_ll => _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      - wp; rnd; skip; progress.
      - wp; skip; progress.
    + sp; if => //.
      - sp; if => //.
        + wp; rnd; skip; progress.
        + wp; skip; progress.
  qed.

  lemma G11_G12_indistinguishable
    (D <: SSEDistROM{G11,G12,OracleCallsCounter}) &m:
    Pr[SSEExpROM(G11, G12, OracleCallsCounter(D)).game(true) @ &m : res] = Pr[SSEExpROM(G11, G12, OracleCallsCounter(D)).game(false) @ &m : res].
  proof.
    byequiv => //.
    proc*.
    inline SSEExpROM(G11, G12, OracleCallsCounter(D)).game.
    rcondt{1} 2; first by progress; first by wp; skip; progress.
    rcondf{2} 2; first by progress; first by wp; skip; progress.
    inline*; wp; sim.
  qed.

  (*
   * === Part13 ===
   * We map the (q, i) to internal timing for utt and et
   *)
  module G13_Client: SSEClient = {
    var sk: tau
    var ws: (query, stoken list) fmap

    var t: int (* auto-incrementing timestamp *)
    var uh: (query, (int * index) list) fmap (* mapping queries to timestamps and indexes - this resembles the update history *)
    var utt: (int, utoken) fmap
    var et: (int, index) fmap
    var h1t: (mapquery * stoken, utoken) fmap
    var h2t: (mapquery * stoken, index) fmap

    proc setup(): setupserver = {
      var pk;

      (pk, sk) <@ CTP.index();
      RF.init();
      ws <- empty;
      utt <- empty;
      et <- empty;
      h1t <- empty;
      h2t <- empty;
      uh <- empty;
      t <- 0;

      return pk;
    }

    (* Simulating the hash functions *)
    module SimH1: HashFunction1 = {
      proc hash(kw: mapquery, s: stoken): utoken = {
        var y;

        if (!(dom h1t (kw, s))) {
          y <$ dutoken;
          h1t.[(kw, s)] <- y;
        }

        return oget h1t.[(kw, s)];
      }
    }

    module SimH2: HashFunction2 = {
      proc hash(kw: mapquery, s: stoken): index = {
        var y;

        if (!(dom h2t (kw, s))) {
          y <$ di;
          h2t.[(kw, s)] <- y;
        }

        return oget h2t.[(kw, s)];
      }
    }

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var kw, s, c, sc, idx, ti, ul;

      if (o = ADD) {
        kw <@ RF.f(q);
        if (!dom ws q) {
          ul <- [];
          sc <- [];
          s <$ dstoken;
          c <- 0;
        } else {
          ul <- oget uh.[q];
          sc <- oget ws.[q];
          c <- size sc;
          s <@ CTP.backward(sk, last witness sc);
        }
        ws.[q] <- sc ++ [s];
        uh.[q] <- ul ++ [(t, i)];
        utt.[t] <$ dutoken;
        idx <$ di;
        et.[t] <- idx;
        idx <- i +^ idx;
        ti <- Some(oget utt.[t], idx);
        t <- t + 1;
      } else {
        ti <- None;
      }
     
      return ti;
    }

    proc query(q: query): (mapquery * stoken * int) option = {
      var kw, sc, c, i, s, u, ul;
      var r: (mapquery * stoken * int) option;

      if (!dom ws q) {
        r <- None;
      } else {
        kw <@ RF.f(q);

        sc <- oget ws.[q];
        c <- size sc - 1;
        r <- Some (kw, nth witness sc c, c);
        ul <- oget uh.[q];

        (* Lazily programming the hash tables *)
        i <- 0;
        while (i < size ul) {
          s <- nth witness sc i;
          u <- fst (nth witness ul i);
          h1t.[(kw, s)] <- oget utt.[u];
          h2t.[(kw, s)] <- oget et.[u];
          i <- i + 1;
        }

        (* Timestamp increments here too *)
        t <- t + 1;
      }

      return r;
    }

    proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
      var h1, h2, h;

      h <- None;
      if     (i = HASH1) {
        h1 <@ SimH1.hash(argv);
        h <- Some(Some(h1), None);
      } elif (i = HASH2) {
        h2 <@ SimH2.hash(argv);
        h <- Some(None, Some(h2));
      }

      return h;
    }
  }.
  module G13 = SSEProtocol(G13_Client, G4_Server(G13_Client.SimH1, G13_Client.SimH2)).

  lemma G13_setup_ll:
    is_lossless dcoins =>
    islossless G13.setup.
  proof.
    move : dkey_ll => _ dcoins_ll.
    proc; inline *.
    wp; rnd; skip; progress.
  qed.

  lemma G13_update_ll:
    islossless G13.update.
  proof.
    move : dmapquery_ll di_ll dut_ll dstoken_ll cdistr_ful => dmq_ll di_ll _ _ [cd_ll cd_fun].
    proc; inline*.
    wp => /=; kill 4.
      if => //; last by wp; skip; progress.
      sp; if => //.
      + swap 3 -2; if => //.
        - wp; rnd; rnd; wp; rnd; wp; rnd; wp; skip; progress.
        - wp; rnd; rnd; wp; rnd; wp; skip; progress.
      + sp; if => //.
        - wp; rnd; rnd; wp; rnd; wp; skip; progress.
        - wp; rnd; rnd; wp; skip; progress.
    wp; skip; progress.
  qed.

  lemma G13_query_ll:
    islossless G13.query.
  proof.
    move : dmapquery_ll dstoken_ll di_ll dut_ll => _ _ _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //; first by wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress => //.
    + kill 12.
        if => //; first by wp; skip; progress.
        case (0 <= (oget qo).`3).
        - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //; first by wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress; smt.
        - rcondf 4; progress; first by wp; skip; progress.
          wp; skip; progress.
      wp => /=; while (0 <= i <= size ul) (size ul - i) => //=; progress.
        wp; skip; progress; smt.
      wp => /=; sp; if => //.
      * rnd; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
      * skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
  qed.

  lemma G13_o_ll:
    islossless G13.o.
  proof.
    move : di_ll dut_ll => _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      - wp; rnd; skip; progress.
      - wp; skip; progress.
    + sp; if => //.
      - sp; if => //.
        + wp; rnd; skip; progress.
        + wp; skip; progress.
  qed.

  lemma G12_G13_indistinguishable
    (D <: SSEDistROM{G12,G13,OracleCallsCounter}) &m:
    Pr[SSEExpROM(G12, G13, OracleCallsCounter(D)).game(true) @ &m : res] = Pr[SSEExpROM(G12, G13, OracleCallsCounter(D)).game(false) @ &m : res].
  proof.
    byequiv => //.
    proc*.
    inline SSEExpROM(G12, G13, OracleCallsCounter(D)).game.
    rcondt{1} 2; first by progress; first by wp; skip; progress.
    rcondf{2} 2; first by progress; first by wp; skip; progress.
    inline*; wp.
    call (_: ={glob OracleCallsCounter, glob RF, glob G4_Server}
            /\   (glob RF, glob G4_Server, G12_Client.sk, G12_Client.ws, G12_Client.h1t, G12_Client.h2t){1}
               = (glob RF, glob G4_Server, G13_Client.sk, G13_Client.ws, G13_Client.h1t, G13_Client.h2t){2}
               (* UPDATE ASSUMPTIONS - empty, the output is simply compatible random sampling *)
               (* SEARCH ASSUMPTIONS - indexes in utt and et correspond *)
            /\ (forall w, dom G13_Client.ws w <=> dom G13_Client.uh w){2}
            /\ (forall w,
                  let ul = map fst (oget G13_Client.uh.[w]) in
                dom G13_Client.ws w => uniq ul
               ){2}
            /\ (forall w,
                  let ul = map fst (oget G13_Client.uh.[w]) in
                forall i, 0 <= i < size ul => dom G13_Client.ws w => nth witness ul i < G13_Client.t
               ){2}
            /\ (forall w,
                dom G13_Client.ws w =>
                  let sc = (oget G13_Client.ws.[w]) in
                  let ul = (oget G13_Client.uh.[w]) in
                size sc = size ul
               ){2}
            /\ (forall w i,
                dom G13_Client.ws w =>
                  let sc = (oget G13_Client.ws.[w]) in
                  let ul = (oget G13_Client.uh.[w]) in
                0 <= i < size ul =>
                  let s = nth witness sc i in
                  let u = fst (nth witness ul i) in
                G12_Client.utt{1}.[(w, i)] = G13_Client.utt.[u] /\ G12_Client.et{1}.[(w, i)] = G13_Client.et.[u]
               ){2}
               (* O(RACLES) ASSUMPTIONS *)
  ) => //.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: update

 * -- enough without SEARCH ASSUMPTIONS
  proc; inline*.
  sp; if => //.
  sp; if => //; last first.
  * rcondf{1} 3; progress; first by wp; skip; progress.
    rcondf{2} 3; progress; first by wp; skip; progress.
    wp; skip; progress.
  * wp => /=.
    rnd; rnd; wp.
    sp; if => //.
    + swap{1} 2 1; swap{2} 2 1; swap{1} 1 1; swap{2} 1 1.
      if => //.
      - wp; rnd; wp; rnd; wp; skip; progress; smt.
      - wp; rnd; wp; skip; progress; smt.
    + swap{1} 1 1; swap{2} 1 1.
      if => //.
      - wp; rnd; wp; skip; progress; smt.
      - wp; skip; progress; smt.
 *)
  proc; inline*.
  sp; if => //.
  sp; if => //; last first.
  * rcondf{1} 3; progress; first by wp; skip; progress.
    rcondf{2} 3; progress; first by wp; skip; progress.
    wp; skip; progress.
  * wp => /=.
    rnd; rnd; wp.
    sp; if => //.
    + swap{1} 2 1; swap{2} 2 1; swap{1} 1 1; swap{2} 1 1.
      if => //.
      - wp; rnd; wp; rnd; wp; skip; progress.
smt.
smt.
smt.
move : H15; rewrite 2!mem_set H //.
move : H15; rewrite 2!mem_set H //.
case (w = q{2}) => wq.
+ rewrite wq get_set_sameE oget_some //.
+ rewrite get_set_neqE // H0.
  move : H15; rewrite mem_set wq //=.
case (w = q{2}) => wq.
+ move : H16 (H1 w i3); rewrite wq get_set_sameE oget_some //= => pre.
  have ->: i3 = 0 by smt.
  rewrite /= ltz_addl //.
+ move : H16 (H1 w i3); rewrite get_set_neqE // H15 /= => pre.
  rewrite pre /=; smt.
case (w = q{2}) => wq.
+ rewrite wq 2!get_set_sameE 2!oget_some //.
+ rewrite get_set_neqE // get_set_neqE //.
  move : H15; rewrite mem_set wq /= => pre.
  apply (H2 w pre).
case (w = q{2}) => wq.
+ move : H17; rewrite wq get_set_sameE oget_some /= => pre.
  have ->: i3 = 0 by smt.
  rewrite /= 2!get_set_sameE //.
+ move : H15; rewrite mem_set wq /= => pre1.
  move : H17; rewrite get_set_neqE // => pre2.
  rewrite get_set_neqE //=; first by rewrite andaE negb_and wq //.
  move : (H1 w i3); rewrite H16 size_map pre2 ltz_def /= (nth_map witness witness) // /= eq_sym pre1; move => [pre _].
  rewrite get_set_neqE //.
  move : (H3 w i3 pre1).
  rewrite H16 pre2 //=.
case (w = q{2}) => wq.
+ move : H17; rewrite wq get_set_sameE oget_some /= => pre.
  have ->: i3 = 0 by smt.
  rewrite /= 2!get_set_sameE //.
+ move : H15; rewrite mem_set wq /= => pre1.
  move : H17; rewrite get_set_neqE // => pre2.
  rewrite get_set_neqE //=; first by rewrite andaE negb_and wq //.
  move : (H1 w i3); rewrite H16 size_map pre2 ltz_def /= (nth_map witness witness) // /= eq_sym pre1; move => [pre _].
  rewrite get_set_neqE //.
  move : (H3 w i3 pre1).
  rewrite H16 pre2 //=.
      - wp; rnd; wp; skip; progress.
smt.
smt.
smt.
move : H13; rewrite 2!mem_set H //.
move : H13; rewrite 2!mem_set H //.
case (w = q{2}) => wq.
+ rewrite wq get_set_sameE oget_some map_cat cat_uniq H0 //.
  rewrite /= mem_map_fst negb_exists /= => idx.
  move : (H1 q{2}).
  rewrite size_map.
  apply absurd => /=.
  rewrite -has_pred1 hasP /pred1 /=.
  move => [x] [x_mem x_def].
  rewrite negb_forall /= => *.
  have : mem (map fst (oget G13_Client.uh{2}.[q{2}])) G13_Client.t{2} by rewrite mem_map_fst; exists idx; rewrite -x_def x_mem.
  rewrite mem_size_nth size_map.
  move => [_] [i] [irng pre].
  exists i.
  rewrite H6 /= irng /= -lezNgt -pre //=.
+ rewrite get_set_neqE // H0.
  move : H13; rewrite mem_set wq //=.
rewrite size_map /= in H14.
rewrite (nth_map witness witness) //=.
case (w = q{2}) => wq.
+ move : H14; rewrite wq get_set_sameE oget_some size_cat //= => pre.
  case (i3 = size (oget G13_Client.uh{2}.[q{2}] ++ [(G13_Client.t{2}, i{2})]) - 1) => //= ilast.
  - rewrite ilast nth_last last_cat /= -lez_add1r addzC //.
  - have ilt: i3 < size (oget G13_Client.uh{2}.[q{2}]).
      move : ilast.
      rewrite ltz_def size_cat /= eq_sym => ilast.
      rewrite ilast /= -(lez_add2l 1) lez_add1r addzC //.
    rewrite nth_cat ilt /=.
    move : (H1 w i3); rewrite wq size_map (nth_map witness witness) //= H13 ilt /= H6 => h.
    rewrite -lez_add1r addzC lez_add2r ltzW //.
+ move : H14 H15 (H1 w i3); rewrite get_set_neqE // H13 /= => pre.
  rewrite size_map pre (nth_map witness witness) //= mem_set wq /= => w_dom.
  rewrite w_dom /= => h.
  rewrite -lez_add1r addzC lez_add2r ltzW //.
case (w = q{2}) => wq.
+ rewrite wq 2!get_set_sameE 2!oget_some 2!size_cat /= eqz_add2r H2 // H6.
+ move : H13; rewrite mem_set wq /= => pre; rewrite get_set_neqE // get_set_neqE // H2 // pre.
case (w = q{2}) => wq.
+ move : H15; rewrite wq get_set_sameE oget_some size_cat //= => pre.
  case (i3 = size (oget G13_Client.uh{2}.[q{2}] ++ [(G13_Client.t{2}, i{2})]) - 1) => //= ilast.
  - rewrite ilast nth_last last_cat /= size_cat /= get_set_sameE H2 // get_set_sameE //.
  - have ilt: i3 < size (oget G13_Client.uh{2}.[q{2}]).
      move : ilast.
      rewrite ltz_def size_cat /= eq_sym => ilast.
      rewrite ilast /= -(lez_add2l 1) lez_add1r addzC //.
    rewrite nth_cat ilt /=.
    move : (H1 w i3); rewrite wq size_map (nth_map witness witness) //= H14 ilt /= => h.
    move : (H3 q{2} i3 H6).
    rewrite H14 ilt /= get_set_neqE; first by rewrite /= neq_ltz (H2 q{2} H6) ilt //.
    rewrite get_set_neqE; first by rewrite neq_ltz h //.
    trivial.
+ move : H13 H15 (H1 w i3); rewrite get_set_neqE // get_set_neqE //=; first by rewrite /= andaE negb_and wq //.
  rewrite mem_set wq size_map H14 /= => w_dom ilt.
  rewrite (nth_map witness witness) //= ilt /= w_dom.
  rewrite ltz_def eq_sym; move => [_ _].
  rewrite get_set_neqE //.
  move : (H3 w i3 w_dom).
  rewrite H14 ilt //=.
case (w = q{2}) => wq.
+ move : H15; rewrite wq get_set_sameE oget_some size_cat //= => pre.
  case (i3 = size (oget G13_Client.uh{2}.[q{2}] ++ [(G13_Client.t{2}, i{2})]) - 1) => //= ilast.
  - rewrite ilast nth_last last_cat /= size_cat /= get_set_sameE H2 // get_set_sameE //.
  - have ilt: i3 < size (oget G13_Client.uh{2}.[q{2}]).
      move : ilast.
      rewrite ltz_def size_cat /= eq_sym => ilast.
      rewrite ilast /= -(lez_add2l 1) lez_add1r addzC //.
    rewrite nth_cat ilt /=.
    move : (H1 w i3); rewrite wq size_map (nth_map witness witness) //= H14 ilt /= => h.
    move : (H3 q{2} i3 H6).
    rewrite H14 ilt /= get_set_neqE; first by rewrite /= neq_ltz (H2 q{2} H6) ilt //.
    rewrite get_set_neqE; first by rewrite neq_ltz h //.
    trivial.
+ move : H13 H15 (H1 w i3);rewrite get_set_neqE // get_set_neqE //=; first by rewrite /= andaE negb_and wq //.
  rewrite mem_set wq size_map H14 /= => w_dom ilt.
  rewrite (nth_map witness witness) //= ilt /= w_dom.
  rewrite ltz_def eq_sym; move => [_ _].
  rewrite get_set_neqE //.
  move : (H3 w i3 w_dom).
  rewrite H14 ilt //=.
    + swap{1} 1 1; swap{2} 1 1.
      if => //.
      - wp; rnd; wp; skip; progress.
smt.
smt.
smt.
smt.
smt.
case (w = q{2}) => wq.
+ rewrite wq get_set_sameE oget_some //.
+ rewrite get_set_neqE // H0.
  move : H13; rewrite mem_set wq //=.
case (w = q{2}) => wq.
+ move : H14 (H1 w i3); rewrite wq get_set_sameE oget_some //= => pre.
  have ->: i3 = 0 by smt.
  rewrite /= ltz_addl //.
+ move : H14 (H1 w i3); rewrite get_set_neqE // /= => pre.
  rewrite pre /=; smt.
case (w = q{2}) => wq.
+ rewrite wq 2!get_set_sameE 2!oget_some //.
+ rewrite get_set_neqE // get_set_neqE //.
  move : H13; rewrite mem_set wq /= => pre.
  apply (H2 w pre).
case (w = q{2}) => wq.
+ move : H15; rewrite wq get_set_sameE oget_some /= => pre.
  have ->: i3 = 0 by smt.
  rewrite /= 2!get_set_sameE //.
+ move : H13; rewrite mem_set wq /= => pre1.
  move : H15; rewrite get_set_neqE // => pre2.
  rewrite get_set_neqE //=; first by rewrite andaE negb_and wq //.
  move : (H1 w i3); rewrite H14 size_map pre2 ltz_def /= (nth_map witness witness) // /= eq_sym pre1; move => [pre _].
  rewrite get_set_neqE //.
  move : (H3 w i3 pre1).
  rewrite H14 pre2 //=.
case (w = q{2}) => wq.
+ move : H15; rewrite wq get_set_sameE oget_some /= => pre.
  have ->: i3 = 0 by smt.
  rewrite /= 2!get_set_sameE //.
+ move : H13; rewrite mem_set wq /= => pre1.
  move : H15; rewrite get_set_neqE // => pre2.
  rewrite get_set_neqE //=; first by rewrite andaE negb_and wq //.
  move : (H1 w i3); rewrite H14 size_map pre2 ltz_def /= (nth_map witness witness) // /= eq_sym pre1; move => [pre _].
  rewrite get_set_neqE //.
  move : (H3 w i3 pre1).
  rewrite H14 pre2 //=.
      - wp; skip; progress.
smt.
smt.
smt.
smt.
rewrite mem_set; smt.
case (w = q{2}) => wq.
+ rewrite wq get_set_sameE oget_some // map_cat cat_uniq H0 //=.
  rewrite mem_map_fst negb_exists /= => idx.
  move : (H1 q{2}).
  rewrite size_map.
  apply absurd => /=.
  rewrite -has_pred1 hasP /pred1 /=.
  move => [x] [x_mem x_def].
  rewrite negb_forall /= => *.
  have : mem (map fst (oget G13_Client.uh{2}.[q{2}])) G13_Client.t{2} by rewrite mem_map_fst; exists idx; rewrite -x_def x_mem.
  rewrite mem_size_nth size_map.
  move => [_] [i] [irng pre].
  exists i.
  rewrite H6 /= irng /= -lezNgt -pre //=.
+ rewrite get_set_neqE // H0.
  move : H11; rewrite mem_set wq //=.
rewrite size_map /= in H12.
rewrite (nth_map witness witness) //=.
case (w = q{2}) => wq.
+ move : H12; rewrite wq get_set_sameE oget_some size_cat //= => pre.
  case (i3 = size (oget G13_Client.uh{2}.[q{2}] ++ [(G13_Client.t{2}, i{2})]) - 1) => //= ilast.
  - rewrite ilast nth_last last_cat /= -lez_add1r addzC //.
  - have ilt: i3 < size (oget G13_Client.uh{2}.[q{2}]).
      move : ilast.
      rewrite ltz_def size_cat /= eq_sym => ilast.
      rewrite ilast /= -(lez_add2l 1) lez_add1r addzC //.
    rewrite nth_cat ilt /=.
    move : (H1 w i3); rewrite wq size_map (nth_map witness witness) //= H11 ilt /= H6 /= => h.
    rewrite -lez_add1r addzC lez_add2r ltzW //.
+ move : H12 H13 (H1 w i3); rewrite get_set_neqE // H11 /= mem_set /= wq /= => pre w_dom.
  rewrite size_map pre (nth_map witness witness) //= w_dom /= => h.
  rewrite -lez_add1r addzC lez_add2r ltzW //.
case (w = q{2}) => wq.
+ rewrite wq 2!get_set_sameE 2!oget_some 2!size_cat /= eqz_add2r H2 // H6.
+ move : H11; rewrite mem_set wq /= => pre; rewrite get_set_neqE // get_set_neqE // H2 // pre.
case (w = q{2}) => wq.
+ move : H13; rewrite wq get_set_sameE oget_some size_cat //= => pre.
  case (i3 = size (oget G13_Client.uh{2}.[q{2}] ++ [(G13_Client.t{2}, i{2})]) - 1) => //= ilast.
  - rewrite ilast nth_last last_cat /= size_cat /= get_set_sameE H2 // get_set_sameE //.
  - have ilt: i3 < size (oget G13_Client.uh{2}.[q{2}]).
      move : ilast.
      rewrite ltz_def size_cat /= eq_sym => ilast.
      rewrite ilast /= -(lez_add2l 1) lez_add1r addzC //.
    rewrite nth_cat ilt /=.
    move : (H1 w i3); rewrite wq size_map (nth_map witness witness) //= H12 ilt /= => h.
    move : (H3 q{2} i3 H6).
    rewrite H12 ilt /= get_set_neqE; first by rewrite /= neq_ltz (H2 q{2} H6) ilt //.
    rewrite get_set_neqE; first by rewrite neq_ltz h //.
    trivial.
+ move : H11 H13 (H1 w i3); rewrite get_set_neqE // get_set_neqE //=; first by rewrite /= andaE negb_and wq //.
  rewrite mem_set wq size_map H12 /= => w_dom ilt.
  rewrite (nth_map witness witness) //= ilt /=.
  rewrite ltz_def eq_sym w_dom /=; move => [_ _].
  rewrite get_set_neqE //.
  move : (H3 w i3 w_dom).
  rewrite H12 ilt //=.
case (w = q{2}) => wq.
+ move : H13; rewrite wq get_set_sameE oget_some size_cat //= => pre.
  case (i3 = size (oget G13_Client.uh{2}.[q{2}] ++ [(G13_Client.t{2}, i{2})]) - 1) => //= ilast.
  - rewrite ilast nth_last last_cat /= size_cat /= get_set_sameE H2 // get_set_sameE //.
  - have ilt: i3 < size (oget G13_Client.uh{2}.[q{2}]).
      move : ilast.
      rewrite ltz_def size_cat /= eq_sym => ilast.
      rewrite ilast /= -(lez_add2l 1) lez_add1r addzC //.
    rewrite nth_cat ilt /=.
    move : (H1 w i3); rewrite wq size_map (nth_map witness witness) //= H12 ilt /= => h.
    move : (H3 q{2} i3 H6).
    rewrite H12 ilt /= get_set_neqE; first by rewrite /= neq_ltz (H2 q{2} H6) ilt //.
    rewrite get_set_neqE; first by rewrite neq_ltz h //.
    trivial.
+ move : H11 H13 (H1 w i3); rewrite get_set_neqE // get_set_neqE //=; first by rewrite /= andaE negb_and wq //.
  rewrite mem_set wq size_map H12 /= => w_dom ilt.
  rewrite (nth_map witness witness) //= ilt /=.
  rewrite ltz_def eq_sym w_dom; move => [_ _].
  rewrite get_set_neqE //.
  move : (H3 w i3 w_dom).
  rewrite H12 ilt //=.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: query
 *)
  proc; inline*.
  sp; if => //.
  sp; if => //.
  * rcondt{1} 3; progress; first by wp; skip; progress.
    rcondt{2} 3; progress; first by wp; skip; progress.
    wp; skip; progress.
  * rcondf{2} 12; progress.
      swap 10 -1; kill 10.
        while (true) (size ul - i) => //; progress.
        * wp; skip; progress; smt.
        * skip; progress; smt.
      wp; sp; if => //.
    rcondf{1} 10; progress.
      swap 9 -1; kill 9.
        while (true) (size sc - i) => //; progress.
        * wp; skip; progress; smt.
        * skip; progress; smt.
      wp; sp; if => //.
    wp => /=.
    while (={i0, c0, kw0, t, r1}
            /\ ={glob OracleCallsCounter, glob RF, glob G4_Server}
            /\   (glob RF, glob G4_Server, G12_Client.sk, G12_Client.ws, G12_Client.h1t, G12_Client.h2t){1}
               = (glob RF, glob G4_Server, G13_Client.sk, G13_Client.ws, G13_Client.h1t, G13_Client.h2t){2}
               (* UPDATE ASSUMPTIONS - empty, the output is simply compatible random sampling *)
               (* SEARCH ASSUMPTIONS - indexes in utt and et correspond *)
            /\ (forall w, dom G13_Client.ws w <=> dom G13_Client.uh w){2}
            /\ (forall w,
                  let ul = map fst (oget G13_Client.uh.[w]) in
                dom G13_Client.ws w => uniq ul
               ){2}
            /\ (forall w,
                  let ul = map fst (oget G13_Client.uh.[w]) in
                forall i, 0 <= i < size ul => dom G13_Client.ws w => nth witness ul i < G13_Client.t
               ){2}
            /\ (forall w,
                dom G13_Client.ws w =>
                  let sc = (oget G13_Client.ws.[w]) in
                  let ul = (oget G13_Client.uh.[w]) in
                size sc = size ul
               ){2}
            /\ (forall w i,
                dom G13_Client.ws w =>
                  let sc = (oget G13_Client.ws.[w]) in
                  let ul = (oget G13_Client.uh.[w]) in
                0 <= i < size ul =>
                  let s = nth witness sc i in
                  let u = fst (nth witness ul i) in
                G12_Client.utt{1}.[(w, i)] = G13_Client.utt.[u] /\ G12_Client.et{1}.[(w, i)] = G13_Client.et.[u]
               ){2}
               (* O(RACLES) ASSUMPTIONS *)
  ) => //.
    sp; if => //.
    + case ((dom G13_Client.h2t (kw0, t)){2}) => //=.
      * rcondf{2} 6; progress; first by wp; rnd; skip; progress.
        rcondf{1} 6; progress; first by wp; rnd; skip; progress.
        wp; rnd; progress.
      * rcondt{2} 6; progress; first by wp; rnd; skip; progress.
        rcondt{1} 6; progress; first by wp; rnd; skip; progress.
        wp; rnd; wp; rnd; progress.
    + sp; if => //.
      * wp; rnd; progress.
      * wp; progress.
  swap{1} 9 -1; swap{2} 10 -1.
  wp => /=.
  while (={i, kw, sc, q1}
            /\ (ul = oget G13_Client.uh.[q1]){2}
            /\ (sc = oget G13_Client.ws.[q1]){2}
            /\ (0 <= i <= size sc){2}
            /\ (dom G12_Client.ws q1){1}
            /\ ={glob OracleCallsCounter, glob RF, glob G4_Server}
            /\   (glob RF, glob G4_Server, G12_Client.sk, G12_Client.ws, G12_Client.h1t, G12_Client.h2t){1}
               = (glob RF, glob G4_Server, G13_Client.sk, G13_Client.ws, G13_Client.h1t, G13_Client.h2t){2}
               (* UPDATE ASSUMPTIONS - empty, the output is simply compatible random sampling *)
               (* SEARCH ASSUMPTIONS - indexes in utt and et correspond *)
            /\ (forall w, dom G13_Client.ws w <=> dom G13_Client.uh w){2}
            /\ (forall w,
                  let ul = map fst (oget G13_Client.uh.[w]) in
                dom G13_Client.ws w => uniq ul
               ){2}
            /\ (forall w,
                  let ul = map fst (oget G13_Client.uh.[w]) in
                forall i, 0 <= i < size ul => dom G13_Client.ws w => nth witness ul i < G13_Client.t
               ){2}
            /\ (forall w,
                dom G13_Client.ws w =>
                  let sc = (oget G13_Client.ws.[w]) in
                  let ul = (oget G13_Client.uh.[w]) in
                size sc = size ul
               ){2}
            /\ (forall w i,
                dom G13_Client.ws w =>
                  let sc = (oget G13_Client.ws.[w]) in
                  let ul = (oget G13_Client.uh.[w]) in
                0 <= i < size ul =>
                  let s = nth witness sc i in
                  let u = fst (nth witness ul i) in
                G12_Client.utt{1}.[(w, i)] = G13_Client.utt.[u] /\ G12_Client.et{1}.[(w, i)] = G13_Client.et.[u]
               ){2}
               (* O(RACLES) ASSUMPTIONS *)
  ) => //.
    wp; skip; progress; smt.
  wp; sp; if => //.
  + rnd; skip; progress; smt.
  + wp; skip; progress; smt.
(*
 * Indistinguishability of output and side effects (consistency)
 * Calling: o
 *)
  proc; inline*.
  sp; if => //.
  sp; if => //.
  * sp; if => //.
    - wp; rnd; progress.
    - wp; progress.
  * sp; if => //.
    + sp; if => //.
      - wp; rnd; skip; progress.
      - wp; skip; progress.
    + wp; skip; progress.
    wp; rnd; wp; skip; progress.
move : H1; rewrite mem_empty //.
move : H1; rewrite mem_empty //.
move : H1; rewrite mem_empty //.
move : H3; rewrite mem_empty //.
move : H1; rewrite mem_empty //.
move : H1; rewrite mem_empty //.
move : H1; rewrite mem_empty //.
  qed.

  (*
   * === Part14 ===
   * Slight modification to G13 - moving RF filling to query
   *)
  module G14_Client: SSEClient = {
    var sk: tau
    var ws: (query, stoken list) fmap

    var t: int (* auto-incrementing timestamp *)
    var uh: (query, (int * index) list) fmap (* mapping queries to timestamps and indexes - this resembles the update history *)
    var utt: (int, utoken) fmap
    var et: (int, index) fmap
    var h1t: (mapquery * stoken, utoken) fmap
    var h2t: (mapquery * stoken, index) fmap

    proc setup(): setupserver = {
      var pk;

      (pk, sk) <@ CTP.index();
      RF.init();
      ws <- empty;
      utt <- empty;
      et <- empty;
      h1t <- empty;
      h2t <- empty;
      uh <- empty;
      t <- 0;

      return pk;
    }

    (* Simulating the hash functions *)
    module SimH1: HashFunction1 = {
      proc hash(kw: mapquery, s: stoken): utoken = {
        var y;

        if (!(dom h1t (kw, s))) {
          y <$ dutoken;
          h1t.[(kw, s)] <- y;
        }

        return oget h1t.[(kw, s)];
      }
    }

    module SimH2: HashFunction2 = {
      proc hash(kw: mapquery, s: stoken): index = {
        var y;

        if (!(dom h2t (kw, s))) {
          y <$ di;
          h2t.[(kw, s)] <- y;
        }

        return oget h2t.[(kw, s)];
      }
    }

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var s, c, sc, idx, ti, ul;

      if (o = ADD) {
        if (!dom ws q) {
          ul <- [];
          sc <- [];
          s <$ dstoken;
          c <- 0;
        } else {
          ul <- oget uh.[q];
          sc <- oget ws.[q];
          c <- size sc;
          s <@ CTP.backward(sk, last witness sc);
        }
        ws.[q] <- sc ++ [s];
        uh.[q] <- ul ++ [(t, i)];
        utt.[t] <$ dutoken;
        idx <$ di;
        et.[t] <- idx;
        idx <- i +^ idx;
        ti <- Some(oget utt.[t], idx);
        t <- t + 1;
      } else {
        ti <- None;
      }
     
      return ti;
    }

    proc query(q: query): (mapquery * stoken * int) option = {
      var kw, sc, c, i, s, u, ul;
      var r: (mapquery * stoken * int) option;

      if (!dom ws q) {
        r <- None;
      } else {
        kw <@ RF.f(q);

        sc <- oget ws.[q];
        c <- size sc - 1;
        r <- Some (kw, nth witness sc c, c);
        ul <- oget uh.[q];

        (* Lazily programming the hash tables *)
        s <- witness; (* avoid complaining about being uninitialised *)
        i <- 0;
        while (i < size ul) {
          s <- nth witness sc i;
          u <- fst (nth witness ul i);
          h1t.[(kw, s)] <- oget utt.[u];
          h2t.[(kw, s)] <- oget et.[u];
          i <- i + 1;
        }
      }

      (* Timestamp increments here too *)
      t <- t + 1;

      return r;
    }

    proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
      var h1, h2, h;

      h <- None;
      if     (i = HASH1) {
        h1 <@ SimH1.hash(argv);
        h <- Some(Some(h1), None);
      } elif (i = HASH2) {
        h2 <@ SimH2.hash(argv);
        h <- Some(None, Some(h2));
      }

      return h;
    }
  }.
  module G14 = SSEProtocol(G14_Client, G4_Server(G14_Client.SimH1, G14_Client.SimH2)).

  lemma G14_setup_ll:
    is_lossless dcoins =>
    islossless G14.setup.
  proof.
    move : dkey_ll => _ dcoins_ll.
    proc; inline *.
    wp; rnd; skip; progress.
  qed.

  lemma G14_update_ll:
    islossless G14.update.
  proof.
    move : dmapquery_ll di_ll dut_ll dstoken_ll cdistr_ful => dmq_ll di_ll _ _ [cd_ll cd_fun].
    proc; inline*.
    wp => /=; kill 4.
      if => //; last by wp; skip; progress.
      sp; if => //.
      - wp; rnd; rnd; wp; rnd; wp; skip; progress.
      - wp; rnd; rnd; wp; skip; progress.
    wp; skip; progress.
  qed.

  lemma G14_query_ll:
    islossless G14.query.
  proof.
    move : dmapquery_ll dstoken_ll di_ll dut_ll => _ _ _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //; first by wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress => //.
    + kill 13.
        if => //; first by wp; skip; progress.
        case (0 <= (oget qo).`3).
        - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //; first by wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress; smt.
        - rcondf 4; progress; first by wp; skip; progress.
          wp; skip; progress.
      wp => /=; while (0 <= i <= size ul) (size ul - i) => //=; progress.
        wp; skip; progress; smt.
      wp => /=; sp; if => //.
      * rnd; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
      * skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
  qed.

  lemma G14_o_ll:
    islossless G14.o.
  proof.
    move : di_ll dut_ll => _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      - wp; rnd; skip; progress.
      - wp; skip; progress.
    + sp; if => //.
      - sp; if => //.
        + wp; rnd; skip; progress.
        + wp; skip; progress.
  qed.

  lemma G13_G14_indistinguishable
    (D <: SSEDistROM{G13,G14,OracleCallsCounter}) &m:
    Pr[SSEExpROM(G13, G14, OracleCallsCounter(D)).game(true) @ &m : res] = Pr[SSEExpROM(G13, G14, OracleCallsCounter(D)).game(false) @ &m : res].
  proof.
    byequiv => //.
    proc*.
    inline SSEExpROM(G13, G14, OracleCallsCounter(D)).game.
    rcondt{1} 2; first by progress; first by wp; skip; progress.
    rcondf{2} 2; first by progress; first by wp; skip; progress.
    inline*; wp.
    admit.
  qed.

  (*
   * === Part15 ===
   * Slight modification to G14 - Replacin ws table with ws mapping only the first
   *)
  module G15_Client: SSEClient = {
    var sk: tau
    var ws: (query, stoken) fmap (* now we map only the first *)

    var t: int (* auto-incrementing timestamp *)
    var uh: (query, (int * index) list) fmap (* mapping queries to timestamps and indexes - this resembles the update history *)
    var utt: (int, utoken) fmap
    var et: (int, index) fmap
    var h1t: (mapquery * stoken, utoken) fmap
    var h2t: (mapquery * stoken, index) fmap

    proc setup(): setupserver = {
      var pk;

      (pk, sk) <@ CTP.index();
      RF.init();
      ws <- empty;
      utt <- empty;
      et <- empty;
      h1t <- empty;
      h2t <- empty;
      uh <- empty;
      t <- 0;

      return pk;
    }

    (* Simulating the hash functions *)
    module SimH1: HashFunction1 = {
      proc hash(kw: mapquery, s: stoken): utoken = {
        var y;

        if (!(dom h1t (kw, s))) {
          y <$ dutoken;
          h1t.[(kw, s)] <- y;
        }

        return oget h1t.[(kw, s)];
      }
    }

    module SimH2: HashFunction2 = {
      proc hash(kw: mapquery, s: stoken): index = {
        var y;

        if (!(dom h2t (kw, s))) {
          y <$ di;
          h2t.[(kw, s)] <- y;
        }

        return oget h2t.[(kw, s)];
      }
    }

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var s, c, idx, ti, ul;

      if (o = ADD) {
        if (!dom ws q) {
          ul <- [];
          ws.[q] <$ dstoken;
          s <- oget ws.[q];
          c <- 0;
        } else {
          ul <- oget uh.[q];
          c <- size ul;
          s <@ CTP.backward(sk, oget ws.[q]);
        }
        uh.[q] <- ul ++ [(t, i)];
        utt.[t] <$ dutoken;
        idx <$ di;
        et.[t] <- idx;
        idx <- i +^ idx;
        ti <- Some(oget utt.[t], idx);
        t <- t + 1;
      } else {
        ti <- None;
      }
     
      return ti;
    }

    proc query(q: query): (mapquery * stoken * int) option = {
      var kw, c, i, s, u, ul;
      var r: (mapquery * stoken * int) option;

      if (!dom ws q) {
        r <- None;
      } else {
        kw <@ RF.f(q);

        ul <- oget uh.[q];
        c <- size ul - 1;

        (* Lazily programming the hash tables *)
        s <- witness; (* avoid complaining about being uninitialised *)
        i <- 0;
        while (i < size ul) {
          if (0 = i) {
            s <- oget ws.[q];
          } else {
            s <@ CTP.backward(sk, s);
          }
          u <- fst (nth witness ul i);
          h1t.[(kw, s)] <- oget utt.[u];
          h2t.[(kw, s)] <- oget et.[u];
          i <- i + 1;
        }
        r <- Some (kw, s, c);
      }

      (* Timestamp increments here too *)
      t <- t + 1;

      return r;
    }

    proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
      var h1, h2, h;

      h <- None;
      if     (i = HASH1) {
        h1 <@ SimH1.hash(argv);
        h <- Some(Some(h1), None);
      } elif (i = HASH2) {
        h2 <@ SimH2.hash(argv);
        h <- Some(None, Some(h2));
      }

      return h;
    }
  }.
  module G15 = SSEProtocol(G15_Client, G4_Server(G15_Client.SimH1, G15_Client.SimH2)).

  lemma G15_setup_ll:
    is_lossless dcoins =>
    islossless G15.setup.
  proof.
    move : dkey_ll => _ dcoins_ll.
    proc; inline *.
    wp; rnd; skip; progress.
  qed.

  lemma G15_update_ll:
    islossless G15.update.
  proof.
    move : dmapquery_ll di_ll dut_ll dstoken_ll cdistr_ful => dmq_ll di_ll _ _ [cd_ll cd_fun].
    proc; inline*.
    wp => /=; kill 4.
      if => //; last by wp; skip; progress.
      sp; if => //.
      - wp; rnd; rnd; wp; rnd; wp; skip; progress.
      - wp; rnd; rnd; wp; skip; progress.
    wp; skip; progress.
  qed.

  lemma G15_query_ll:
    islossless G15.query.
  proof.
    move : dmapquery_ll dstoken_ll di_ll dut_ll => _ _ _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //; first by wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress => //.
    + kill 12.
        if => //; first by wp; skip; progress.
        case (0 <= (oget qo).`3).
        - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //; first by wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress; smt.
        - rcondf 4; progress; first by wp; skip; progress.
          wp; skip; progress.
      wp => /=; while (0 <= i <= size ul) (size ul - i) => //=; progress.
        wp; skip; progress; smt.
      wp => /=; sp; if => //.
      * rnd; skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
      * skip; progress => //.
        + rewrite size_ge0 //.
        + smt.
  qed.

  lemma G15_o_ll:
    islossless G15.o.
  proof.
    move : di_ll dut_ll => _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      - wp; rnd; skip; progress.
      - wp; skip; progress.
    + sp; if => //.
      - sp; if => //.
        + wp; rnd; skip; progress.
        + wp; skip; progress.
  qed.

  lemma G14_G15_indistinguishable
    (D <: SSEDistROM{G14,G15,OracleCallsCounter}) &m:
    ct TP.index sample forward backward => (* collection of trapdoor permutation *)
    Pr[SSEExpROM(G14, G15, OracleCallsCounter(D)).game(true) @ &m : res] = Pr[SSEExpROM(G14, G15, OracleCallsCounter(D)).game(false) @ &m : res].
  proof.
    move : dut_ll di_ll dmapquery_ll dstoken_ll dkey_ll => _ _ _ _ _.
    rewrite /ct /validkeypair /(-<) /cancel forall_and /=.
    move => [_ valk_can_fb].
    byequiv (_: (glob D){1} = (glob D){2} /\ (glob D){1} = (glob D){m} /\ real{1} /\ !real{2} ==> _) => //.
    proc*.
    inline SSEExpROM(G14, G15, OracleCallsCounter(D)).game.
    rcondt{1} 2; first by progress; first by wp; skip; progress.
    rcondf{2} 2; first by progress; first by wp; skip; progress.
    inline*; wp.
    call (_: ={glob OracleCallsCounter}
            /\   (G14_Client.utt, G14_Client.et, G14_Client.uh, G14_Client.h1t, G14_Client.h2t, RF.m, G4_Server.pk, G14_Client.sk, G4_Server.edb, G14_Client.t){1}
               = (G15_Client.utt, G15_Client.et, G15_Client.uh, G15_Client.h1t, G15_Client.h2t, RF.m, G4_Server.pk, G15_Client.sk, G4_Server.edb, G15_Client.t){2}
            /\ (validkeypair (G4_Server.pk, G14_Client.sk)){1}
            /\ (forall w,
                     (dom G14_Client.ws{1} w <=> dom G15_Client.ws{2} w)
                  /\ (dom G14_Client.ws{1} w => head witness (oget G14_Client.ws{1}.[w]) = oget G15_Client.ws{2}.[w])
                  /\ (dom G14_Client.ws{1} w => (oget G14_Client.ws{1}.[w]) <> [])
               )
            /\ (forall w, dom G14_Client.ws w =>
                     (size (oget G14_Client.ws.[w]) = size (oget G14_Client.uh.[w]))
               ){1}
            /\ (forall w, dom G14_Client.ws w =>
                 let sc = oget G14_Client.ws.[w] in
                 forall i, 0 < i < size sc => nth witness sc (i - 1) = forward G4_Server.pk (nth witness sc i)
               ){1}
    ) => //.
  + (* Update *)
    proc.
    sp; if => //.
    inline*; wp => /=.
    case (o{2} = ADD); last first.
    * (* else *)
      rcondf{1} 7; progress; first by wp; skip; progress.
      rcondf{2} 7; progress; first by wp; skip; progress.
      wp; skip; progress.
    * (* then *)
      rcondt{1} 7; progress; first by wp; skip; progress.
      rcondt{2} 7; progress; first by wp; skip; progress.
      wp; rnd; rnd; wp => /=.
      sp; if.
      - (* condition *)
        move => &1 &2 [_] [_] [_] [_] [_] [_] [_] [_] [_] [_] [_] [_] [[[_] [_] [[_ [_ _]]]]] [_] [[_] [_] [_ [_] [_] [_] [_] [_] [_ _]]]; subst.
        move => [valid_keypair] [ws_sync] ws_tp_relation  _ _; subst.
        move : (ws_sync q{2}) => [concl] _.
        rewrite iff_negb; exact concl.
      - (* then *)
        wp; rnd; wp; skip.
        move => &1 &2 [[_] [_] [_] [_] [_] [_] [_] [_] [_] [_] [_] [_]] [[[_] [_] [[_ [_ _]]]]] [_] [[_] [_] [_ [_] [_] [_] [_] [_] [_ _]]]; subst.
        move => [valid_keypair] [ws_sync] [sizes] ws_tp_relation _ _ q_dom; subst.
        progress; expect 6.
        + move : H5; rewrite 2!mem_set.
          case (w = q{2}) => //= wq.
          move : (ws_sync w) => [rwme] _.
          rewrite -rwme //.
        + move : H5; rewrite 2!mem_set.
          case (w = q{2}) => //= wq.
          move : (ws_sync w) => [rwme] _.
          rewrite -rwme //.
        + case (w = q{2}) => wq.
          * rewrite wq 2!get_set_sameE 2!oget_some //.
          * move : H5; rewrite mem_set wq /= => w_dom.
            move : (ws_sync w) => [_] [rwme] _.
            rewrite get_set_neqE // get_set_neqE // rwme //.
        + case (w = q{2}) => wq.
          * rewrite wq get_set_sameE oget_some //.
          * move : H5; rewrite mem_set wq /= => w_dom.
            move : (ws_sync w) => [_] [_].
            rewrite w_dom get_set_neqE // rwme //.
        + case (w = q{2}) => wq.
          * rewrite wq 2!get_set_sameE 2!oget_some //.
          * move : H5; rewrite mem_set wq /= => w_dom.
            move : (sizes w w_dom) => _.
            rewrite get_set_neqE // get_set_neqE //.
        + case (w = q{2}) => wq.
          * move : H6 H7; rewrite wq get_set_sameE oget_some andWI -andaE /=. (* this shows that the precondition is an absurd *)
            rewrite -lez_add1r /= lez_lt_asym //.
          * move : H5; rewrite mem_set wq /= => w_dom.
            move : H7; rewrite get_set_neqE // => ilt.
            move : (ws_tp_relation w w_dom i3); rewrite H6 ilt //.
      - (* else *)
        wp; skip.
        move => &1 &2 [[_] [_] [_] [_] [_] [_] [_] [_] [_] [_] [_] [_]] [[[_] [_] [[_ [_ _]]]]] [_] [[_] [_] [_ [_] [_] [_] [_] [_] [_ _]]]; subst => /=.
        move => [valid_keypair] [ws_sync] [sizes] ws_tp_relation _ _ q_dom; subst.
        progress; expect 6.
        + move : H3; rewrite mem_set.
          case (w = q{2}) => //= wq.
          * move : (ws_sync q{2}) => [rwme] _.
            rewrite wq -rwme //.
          * move : (ws_sync w) => [rwme] _.
            rewrite -rwme //.
        + move : H3; rewrite mem_set.
          case (w = q{2}) => //= wq.
          move : (ws_sync w) => [rwme] _.
          rewrite -rwme //.
        + case (w = q{2}) => wq.
          * move : (ws_sync w) => [_].
            rewrite wq q_dom /=; move => [concl subconcl].
            rewrite get_set_sameE oget_some // head_cat //.
          * move : H3; rewrite mem_set wq /= => w_dom.
            move : (ws_sync w) => [_] [rwme] _.
            rewrite get_set_neqE // rwme //.
        + case (w = q{2}) => wq.
          * rewrite wq get_set_sameE oget_some -size_eq0 size_cat /= eq_sym neq_ltz; left.
            rewrite -lez_add1r addzC lez_add2r size_ge0.
          * move : H3; rewrite mem_set wq /= => w_dom.
          * move : (ws_sync w) => [_].
            rewrite w_dom /=; move => [concl subconcl].
            rewrite (get_set_neqE _ q{2}) //.
        + case (w = q{2}) => wq.
          * rewrite wq 2!get_set_sameE 2!oget_some // 2!size_cat /= eqz_add2r.
            move : (sizes q{2} q_dom) => //.
          * move : H3; rewrite mem_set wq /= => w_dom.
            move : (sizes w w_dom) => _.
            rewrite get_set_neqE // get_set_neqE //.
        + case (w = q{2}) => wq.
          * move : H4 H5; rewrite wq get_set_sameE oget_some andWI -andaE /=.
            rewrite size_cat /=.
            case (i3 = size (oget G14_Client.ws{1}.[q{2}])) => i3max.
            - have ->/=: 0 < i3 < size (oget G14_Client.ws{1}.[q{2}]) + 1 by smt.
              rewrite 2!nth_cat i3max /=.
              have ->/=: size (oget G14_Client.ws{1}.[q{2}]) - 1 < size (oget G14_Client.ws{1}.[q{2}]) by smt.
              rewrite nth_last.                
              pose s := oget G15_Client.ws{2}.[q{2}];
                pose f := forward G4_Server.pk{2};
                pose b := backward G15_Client.sk{2}.
              have inj_f: injective f by move : (valk_can_fb (G4_Server.pk, G15_Client.sk){2} valid_keypair); apply (can_inj f b).
              move : (inj_f); rewrite TP.TrapdoorDomain.PermutationDomain.enumD_inj_uniq_isomap -TP.TrapdoorDomain.PermutationDomain.enumD_bij_uniq_isomap => bij_f.
              move : (valk_can_fb (G4_Server.pk, G15_Client.sk){2} valid_keypair); rewrite -/f -/b -/cancel => can_fb.
              have can_bf: cancel b f by apply (bij_can_sym f b) => //.
              rewrite /= can_bf //. 
            - have ->pre: i3 < size (oget G14_Client.ws{1}.[q{2}]) + 1 <=> i3 < size (oget G14_Client.ws{1}.[q{2}]) by smt.
              move : (ws_tp_relation q{2} q_dom i3 pre) => concl.
              rewrite 2!nth_cat /=.
              have ->/=: i3 - 1 < size (oget G14_Client.ws{1}.[q{2}]) by smt.
              have ->/=: i3 < size (oget G14_Client.ws{1}.[q{2}]) by smt.
              exact concl.
          * move : H3; rewrite mem_set wq /= => w_dom.
            move : H5; rewrite get_set_neqE // => ilt.
            move : (ws_tp_relation w w_dom i3); rewrite H4 ilt //.
  + (* Search *)
    proc.
    sp; if => //.
    inline*; wp => /=.
    sp; if => /=.
      - (* condition *)
        move => &1 &2 [_] [_] [_] [_] [[_] [_] [_ [_ [[_ [_] [_] [_] [_] [_] [_] [_] [_ _]]]]]]; subst.
        move => [valid_keypair] [ws_sync] ws_tp_relation _ ; subst.
        move : (ws_sync q{2}) => [concl] _.
        rewrite iff_negb; exact concl.
      - (* then *)
        rcondt{1} 4; progress; first by wp; skip; progress.
        rcondt{2} 4; progress; first by wp; skip; progress.
        wp; skip; progress.
      - (* else *)
        rcondf{1} 13; progress.
          kill 10.
            while (true) (size ul - i) => //; progress; first by wp; skip; progress; smt.
            skip; progress; smt.
          wp; sp; if => //.
        rcondf{2} 12; progress; first by wp; sp; while (true) => //; progress.
        seq 3 3: (={glob OracleCallsCounter}
            /\   (G14_Client.utt, G14_Client.et, G14_Client.uh, G14_Client.h1t, G14_Client.h2t, RF.m, G4_Server.pk, G14_Client.sk, G4_Server.edb, G14_Client.t){1}
               = (G15_Client.utt, G15_Client.et, G15_Client.uh, G15_Client.h1t, G15_Client.h2t, RF.m, G4_Server.pk, G15_Client.sk, G4_Server.edb, G15_Client.t){2}
            /\ ={q, q1, kw}
            /\ (validkeypair (G4_Server.pk, G14_Client.sk)){1}
            /\ (dom G14_Client.ws q1){1}
            /\ (forall w,
                     (dom G14_Client.ws{1} w <=> dom G15_Client.ws{2} w)
                  /\ (dom G14_Client.ws{1} w => head witness (oget G14_Client.ws{1}.[w]) = oget G15_Client.ws{2}.[w])
                  /\ (dom G14_Client.ws{1} w => (oget G14_Client.ws{1}.[w]) <> [])
               )
            /\ (forall w, dom G14_Client.ws w =>
                     (size (oget G14_Client.ws.[w]) = size (oget G14_Client.uh.[w]))
               ){1}
            /\ (forall w, dom G14_Client.ws w =>
                 let sc = oget G14_Client.ws.[w] in
                 forall i, 0 < i < size sc => nth witness sc (i - 1) = forward G4_Server.pk (nth witness sc i)
               ){1}
          ) => //.
          wp; sp; if => //.
          rnd; skip; progress.
        seq 9 8: (={glob OracleCallsCounter}
            /\   (G14_Client.utt, G14_Client.et, G14_Client.uh, G14_Client.h1t, G14_Client.h2t, RF.m, G4_Server.pk, G14_Client.sk, G4_Server.edb, G14_Client.t){1}
               = (G15_Client.utt, G15_Client.et, G15_Client.uh, G15_Client.h1t, G15_Client.h2t, RF.m, G4_Server.pk, G15_Client.sk, G4_Server.edb, G15_Client.t){2}
            /\ ={q, q1, kw, qo}
            /\ (let c = size (oget G14_Client.ws.[q1]) - 1 in qo = Some (kw, s{2}, c)){1}
            /\ (validkeypair (G4_Server.pk, G14_Client.sk)){1}
            /\ (dom G14_Client.ws q1){1}
            /\ (forall w,
                     (dom G14_Client.ws{1} w <=> dom G15_Client.ws{2} w)
                  /\ (dom G14_Client.ws{1} w => head witness (oget G14_Client.ws{1}.[w]) = oget G15_Client.ws{2}.[w])
                  /\ (dom G14_Client.ws{1} w => (oget G14_Client.ws{1}.[w]) <> [])
               )
            /\ (forall w, dom G14_Client.ws w =>
                     (size (oget G14_Client.ws.[w]) = size (oget G14_Client.uh.[w]))
               ){1}
            /\ (forall w, dom G14_Client.ws w =>
                 let sc = oget G14_Client.ws.[w] in
                 forall i, 0 < i < size sc => nth witness sc (i - 1) = forward G4_Server.pk (nth witness sc i) 
               ){1}
          ) => //.
          swap{1} 3 3.
          wp; while ((0 <= i <= size ul){1}
            /\ ={i, ul, c}
            /\ ={glob OracleCallsCounter}
            /\   (G14_Client.utt, G14_Client.et, G14_Client.uh, G14_Client.h1t, G14_Client.h2t, RF.m, G4_Server.pk, G14_Client.sk, G4_Server.edb, G14_Client.t){1}
               = (G15_Client.utt, G15_Client.et, G15_Client.uh, G15_Client.h1t, G15_Client.h2t, RF.m, G4_Server.pk, G15_Client.sk, G4_Server.edb, G15_Client.t){2}
            /\ ={q, q1, kw}
            /\ (validkeypair (G4_Server.pk, G14_Client.sk)){1}
            /\ (dom G14_Client.ws q1){1}
            /\ (forall w,
                     (dom G14_Client.ws w <=> dom G15_Client.ws{2} w)
                  /\ (dom G14_Client.ws w => head witness (oget G14_Client.ws.[w]) = oget G15_Client.ws{2}.[w])
                  /\ (dom G14_Client.ws w => (oget G14_Client.ws.[w]) <> [])
               ){1}
            /\ (forall w, dom G14_Client.ws w =>
                     (size (oget G14_Client.ws.[w]) = size (oget G14_Client.uh.[w]))
               ){1}
            /\ (forall w, dom G14_Client.ws w =>
                 let sc = oget G14_Client.ws.[w] in
                 forall i, 0 < i < size sc => nth witness sc (i - 1) = forward G4_Server.pk (nth witness sc i) 
               ){1}
            /\ (sc = oget G14_Client.ws.[q1]){1}
            /\ (ul = oget G14_Client.uh.[q1]){1}
            /\ (0 < i < size ul => nth witness sc i = backward G14_Client.sk s{2}){1}
            /\ (i = size ul => last witness sc = s{2}){1}
            ).
            wp => /=; skip; move => &1 &2 [[_ [[_] [_ _]]]] [_] [[_] [_] [_] [_] [_] [_] [_] [_] [_ _]] [[_] [_] _]; subst.
            move => [valid_keypair] [q_dom] [ws_sync] [sizes] [ws_tp_relation] [sc_def] [ul_def] [s_sync qo_s_sync] [isup]; move : s_sync; rewrite isup /= => s_sync; subst.
            progress.
            + smt.
            + move : (ws_sync q1{2}) => [_] [concl _]; move : concl; rewrite q_dom /= nth_head //.
            + move : (ws_sync q1{2}) => /= [_] [rwme _]; move : rwme; rewrite q_dom /= => rwme.
              rewrite nth_head rwme //.
            + move : (ws_sync q1{2}) => /= [_] [rwme _]; move : rwme; rewrite q_dom /= => rwme.
              rewrite nth_head rwme //.
            + move : (ws_sync q1{2}) (ws_tp_relation q1{2} q_dom 1) => /= [_] [rwme1 _]; move : rwme1; rewrite q_dom /= => rwme1.
              rewrite (sizes q1{2} q_dom) H /= => rwme2.
              rewrite -rwme1 -nth_head rwme2.
              pose s := oget G15_Client.ws{2}.[q{2}];
                pose f := forward G4_Server.pk{2};
                pose b := backward G15_Client.sk{2}.
              have inj_f: injective f by move : (valk_can_fb (G4_Server.pk, G15_Client.sk){2} valid_keypair); apply (can_inj f b).
              move : (inj_f); rewrite TP.TrapdoorDomain.PermutationDomain.enumD_inj_uniq_isomap -TP.TrapdoorDomain.PermutationDomain.enumD_bij_uniq_isomap => bij_f.
              move : (valk_can_fb (G4_Server.pk, G15_Client.sk){2} valid_keypair); rewrite -/f -/b -/cancel => can_fb.
              rewrite /= can_fb //.
            + move : (ws_sync q1{2}) => [_] [concl _]; move : concl; rewrite q_dom /= //.
              rewrite -nth_last (sizes q1{2} q_dom) H /= nth_head //.
            + smt.
            + smt.
            + smt.
            + smt.
            + move : (ws_tp_relation q1{2} q_dom (i{2} + 1)).
              rewrite (sizes q1{2} q_dom) H0 H1 /=.
              move : s_sync.
              pose s := oget G14_Client.ws{1}.[q1{2}];
                pose f := forward G4_Server.pk{2};
                pose b := backward G15_Client.sk{2}.
              have ->/=s_sync: 0 < i{2} by smt.
              have inj_f: injective f by move : (valk_can_fb (G4_Server.pk, G15_Client.sk){2} valid_keypair); apply (can_inj f b).
              move : (inj_f); rewrite TP.TrapdoorDomain.PermutationDomain.enumD_inj_uniq_isomap -TP.TrapdoorDomain.PermutationDomain.enumD_bij_uniq_isomap => bij_f.
              move : (valk_can_fb (G4_Server.pk, G15_Client.sk){2} valid_keypair); rewrite -/f -/b -/cancel => can_fb.
              have can_bf: cancel b f by apply (bij_can_sym f b) => //.
              rewrite -(can_eq b f can_bf).
              rewrite can_fb eq_sym => rwme.
              rewrite rwme -s_sync //.
            + rewrite -nth_last (sizes q1{2} q_dom) -H0 /=.
              move : s_sync.
              have ->//: 0 < i{2} by smt.
              (* end of while *)
          wp; skip; move => /= &1 &2 [_] [[_] [_] [_] [_] [_] [_] [_] [_] [_ _]] [[_] [_ _]]; subst.
          move => [valid_keypair] [q_dom] [ws_sync] [sizes] ws_tp_relation; subst.
          progress.
          + smt.
          + smt.
          + smt.
          + smt.
          + smt.
        (* end of seq *)
        wp; while ((0 <= i0 <= c0 + 1){1}
            /\ ={kw0, t, i0, c0, r1}
            /\ ={glob OracleCallsCounter}
            /\   (G14_Client.utt, G14_Client.et, G14_Client.uh, G14_Client.h1t, G14_Client.h2t, RF.m, G4_Server.pk, G14_Client.sk, G4_Server.edb, G14_Client.t){1}
               = (G15_Client.utt, G15_Client.et, G15_Client.uh, G15_Client.h1t, G15_Client.h2t, RF.m, G4_Server.pk, G15_Client.sk, G4_Server.edb, G15_Client.t){2}
            /\ ={q, q1, kw, qo, c0}
            /\ (qo = Some (kw, s{2}, size (oget G14_Client.ws.[q1]) - 1)){1}
            /\ (validkeypair (G4_Server.pk, G14_Client.sk)){1}
            /\ (dom G14_Client.ws q1){1}
            /\ (forall w,
                     (dom G14_Client.ws{1} w <=> dom G15_Client.ws{2} w)
                  /\ (dom G14_Client.ws{1} w => head witness (oget G14_Client.ws{1}.[w]) = oget G15_Client.ws{2}.[w])
                  /\ (dom G14_Client.ws{1} w => (oget G14_Client.ws{1}.[w]) <> [])
               )
            /\ (forall w, dom G14_Client.ws w =>
                     (size (oget G14_Client.ws.[w]) = size (oget G14_Client.uh.[w]))
               ){1}
            /\ (forall w, dom G14_Client.ws w =>
                 let sc = oget G14_Client.ws.[w] in
                 forall i, 0 < i < size sc => nth witness sc (i - 1) = forward G4_Server.pk (nth witness sc i) 
               ){1}
          ).
          wp; sp; if => //.
          - (* then *)
            swap{1} 3 3; swap{1} 2 3; swap{1} 1 3.
            swap{2} 3 3; swap{2} 2 3; swap{2} 1 3.
            sp; if => //.
            * wp; rnd; wp; rnd; skip; progress; smt.
            * wp; rnd; skip; progress; smt.
          - (* else *)
            sp; if => //.
            * wp; rnd; skip; progress; smt.
            * wp; skip; progress; smt.
          (* end of while *)
        wp; skip; move => /= &1 &2 [_] [[_] [_] [_] [_] [_] [_] [_] [_] [_ _]] [[_] [_ [_ _]]]; subst.
        move => [qo_def] [valid_keypair] [q_dom] [ws_sync] [sizes] ws_tp_relation; subst.
        progress; smt.
  + (* o *)
    proc.
    sp; if => //.
    inline*; wp => /=.
    sp; if => //.
    * (* HASH1 *)
      sp; if => //.
      - wp; rnd; progress.
      - wp; progress.
    * (* NOT HASH1 *)
      if => //.
      (* HASH2 *)
      sp; if => //.
      - wp; rnd; progress.
      - wp; progress.
  + (* Invariant before the distinguisher call *)
    wp; rnd; wp; skip; move => &1 &2 /= [_] [_ _] r r_supp; rewrite r_supp /=; subst; progress; expect 7; last 6 by move : H; rewrite mem_empty //.
    smt.
  qed.

  (*
   * === Part16 ===
   * Slight modification to G16 - moving ws filling to query
   *)
  module G16_Client: SSEClient = {
    var sk: tau
    var ws: (query, stoken) fmap (* now we map only the first *)

    var t: int (* auto-incrementing timestamp *)
    var uh: (query, (int * index) list) fmap (* mapping queries to timestamps and indexes - this resembles the update history *)
    var utt: (int, utoken) fmap
    var et: (int, index) fmap
    var h1t: (mapquery * stoken, utoken) fmap
    var h2t: (mapquery * stoken, index) fmap

    proc setup(): setupserver = {
      var pk;

      (pk, sk) <@ CTP.index();
      RF.init();
      ws <- empty;
      utt <- empty;
      et <- empty;
      h1t <- empty;
      h2t <- empty;
      uh <- empty;
      t <- 0;

      return pk;
    }

    (* Simulating the hash functions *)
    module SimH1: HashFunction1 = {
      proc hash(kw: mapquery, s: stoken): utoken = {
        var y;

        if (!(dom h1t (kw, s))) {
          y <$ dutoken;
          h1t.[(kw, s)] <- y;
        }

        return oget h1t.[(kw, s)];
      }
    }

    module SimH2: HashFunction2 = {
      proc hash(kw: mapquery, s: stoken): index = {
        var y;

        if (!(dom h2t (kw, s))) {
          y <$ di;
          h2t.[(kw, s)] <- y;
        }

        return oget h2t.[(kw, s)];
      }
    }

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var idx, ti, ul;

      if (o = ADD) {
        if (!dom uh q) {
          ul <- [];
        } else {
          ul <- oget uh.[q];
        }
        uh.[q] <- ul ++ [(t, i)];
        utt.[t] <$ dutoken;
        idx <$ di;
        et.[t] <- idx;
        idx <- i +^ idx;
        ti <- Some(oget utt.[t], idx);
        t <- t + 1;
      } else {
        ti <- None;
      }
     
      return ti;
    }

    proc query(q: query): (mapquery * stoken * int) option = {
      var kw, c, i, s, u, ul;
      var r: (mapquery * stoken * int) option;

      if (!dom uh q) {
        r <- None;
      } else {
        kw <@ RF.f(q);

        ul <- oget uh.[q];
        c <- size ul - 1;
        if (!dom ws q) {
          ws.[q] <$ dstoken;
        }

        (* Lazily programming the hash tables *)
        s <- witness; (* avoid complaining about being uninitialised *)
        i <- 0;
        while (i < size ul) {
          if (i = 0) {
            s <- oget ws.[q];
          } else {
            s <@ CTP.backward(sk, s);
          }
          u <- fst (nth witness ul i);
          h1t.[(kw, s)] <- oget utt.[u];
          h2t.[(kw, s)] <- oget et.[u];
          i <- i + 1;
        }
        r <- Some (kw, s, c);
      }

      (* Timestamp increments here too *)
      t <- t + 1;

      return r;
    }

    proc o(i: int, argv: sseo_args_t): sseo_res_t option = {
      var h1, h2, h;

      h <- None;
      if     (i = HASH1) {
        h1 <@ SimH1.hash(argv);
        h <- Some(Some(h1), None);
      } elif (i = HASH2) {
        h2 <@ SimH2.hash(argv);
        h <- Some(None, Some(h2));
      }

      return h;
    }
  }.
  module G16 = SSEProtocol(G16_Client, G4_Server(G16_Client.SimH1, G16_Client.SimH2)).

  lemma G16_setup_ll:
    is_lossless dcoins =>
    islossless G16.setup.
  proof.
    move : dkey_ll => _ dcoins_ll.
    proc; inline *.
    wp; rnd; skip; progress.
  qed.

  lemma G16_update_ll:
    islossless G16.update.
  proof.
    move : dmapquery_ll di_ll dut_ll dstoken_ll cdistr_ful => dmq_ll di_ll _ _ [cd_ll cd_fun].
    proc; inline*.
    wp => /=; kill 4.
      if => //; last by wp; skip; progress.
      wp; rnd; rnd; wp; skip; progress.
    wp; skip; progress.
  qed.

  lemma G16_query_ll:
    islossless G16.query.
  proof.
    move : dmapquery_ll dstoken_ll di_ll dut_ll => _ _ _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      * wp; skip; progress.
      * wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //; first by wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress => //.
    + kill 13.
        if => //; first by wp; skip; progress.
        case (0 <= (oget qo).`3).
        - wp => /=; while (0 <= i0 <= c0 + 1) (c0 + 1 - i0) => //=; progress.
          wp => /=; kill 7.
            sp; if => //; first by wp; rnd; skip; progress.
          wp => /=; kill 3.
            sp; if => //; first by wp; rnd; skip; progress.
          wp; skip; progress; smt.
        wp; skip; progress; smt.
        - rcondf 4; progress; first by wp; skip; progress.
          wp; skip; progress.
      wp => /=; while (0 <= i <= size ul) (size ul - i) => //=; progress.
        wp; skip; progress; smt.
      wp => /=; sp; if => //.
      * swap 5 -4; if => //.
        - wp; rnd; rnd; skip; progress => //.
          + rewrite size_ge0 //.
          + smt.
        - wp; rnd; skip; progress => //.
          + rewrite size_ge0 //.
          + smt.
      * sp; if => //.
        - rnd; skip; progress => //.
          + rewrite size_ge0 //.
          + smt.
        - skip; progress => //.
          + rewrite size_ge0 //.
          + smt.
  qed.

  lemma G16_o_ll:
    islossless G16.o.
  proof.
    move : di_ll dut_ll => _ _.
    proc; inline*.
    sp; if => //.
    + sp; if => //.
      - wp; rnd; skip; progress.
      - wp; skip; progress.
    + sp; if => //.
      - sp; if => //.
        + wp; rnd; skip; progress.
        + wp; skip; progress.
  qed.

  lemma G15_G16_indistinguishable
    (D <: SSEDistROM{G15,G16,OracleCallsCounter}) &m:
    Pr[SSEExpROM(G15, G16, OracleCallsCounter(D)).game(true) @ &m : res] = Pr[SSEExpROM(G15, G16, OracleCallsCounter(D)).game(false) @ &m : res].
  proof.
    byequiv (_: (glob D){1} = (glob D){2} /\ (glob D){1} = (glob D){m} /\ real{1} /\ !real{2} ==> _) => //.
    proc*.
    inline SSEExpROM(G15, G16, OracleCallsCounter(D)).game.
    rcondt{1} 2; first by progress; first by wp; skip; progress.
    rcondf{2} 2; first by progress; first by wp; skip; progress.
    inline*; wp.
    admit.
  qed.

  (*
   * === Part19 ===
   * Reduce to simulator!
   *)
  module SSIM = SophosSimulator(CTP).
  
  lemma G16_Sim_indistinguishable
    (D <: SSEDistROM{G16,SSIM,OracleCallsCounter,SophosLeakage}) &m:
    ct TP.index sample forward backward => (* collection of trapdoor permutation *)
    Pr[SSELAdaptiveSecurityROM(G16, SSIM, SophosLeakage, OracleCallsCounter(D)).game(false) @ &m : res] = Pr[SSELAdaptiveSecurityROM(G16, SSIM, SophosLeakage, OracleCallsCounter(D)).game(true) @ &m : res].
  proof.
    move : dut_ll di_ll dmapquery_ll dstoken_ll dkey_ll => _ _ _ _ _.
    rewrite /ct /validkeypair /(-<) /cancel forall_and /=.
    move => [_ valk_can_fb].
    byequiv (_: ={glob D, glob OracleCallsCounter} /\ real{2} /\ !real{1} ==> _) => //.
    proc*.
    inline SSELAdaptiveSecurityROM(G16, SSIM, SophosLeakage, OracleCallsCounter(D)).game.
    rcondf{1} 2; first by progress; first by wp; skip; progress.
    rcondt{2} 2; first by progress; first by wp; skip; progress.
    inline*; wp.
    call (_: ={glob OracleCallsCounter}
            /\   (     SSIM.pk,       SSIM.sk,      SSIM.edb,       SSIM.t, size (SophosLeakage.h)){1}
               = (G4_Server.pk, G16_Client.sk, G4_Server.edb, G16_Client.t,           G16_Client.t){2}
            /\ (validkeypair (SSIM.pk, SSIM.sk)){1}
           (*
            * UPDATE does not require additional relationship but changes database and tables ~ leak information.
            * SEARCH and HASH1/2 do require relations on how to show that the results are indistinguishable.
            *)
            /\ (indexed SophosLeakage.h){1}
            /\ (forall x, mem SophosLeakage.h x => (oh_update x <> None <=> oh_query x = None)){1}
            /\ (forall w, dom G16_Client.uh{2} w <=>
                 filter (fun (z: int * operation * index), z.`2 = ADD) (ahpU SophosLeakage.h{1} w) <> []
               )
            /\ (forall w, dom G16_Client.uh w =>
                    size (filter (fun (z: int * operation * index), z.`2 = ADD) (ahpU SophosLeakage.h{1} w)) = size (oget G16_Client.uh.[w])
               ){2}
            /\ (forall w, dom RF.m w <=> dom G16_Client.ws w){2}
            /\ (forall k, dom SSIM.wssim k <=> dom SSIM.keys k){1}
            /\ (forall w,
                 let spat = (qp SophosLeakage.h{1} w) in
                 let wsim = head witness spat in
                    (dom RF.m w => 0 < size spat /\ SSIM.keys{1}.[wsim] = RF.m.[w])
                 /\ (!dom RF.m w => (0 < size spat => !dom SSIM.keys{1} wsim) /\ forall j, (size SophosLeakage.h{1}) <= j => !dom SSIM.keys{1} j)
               ){2}
            /\ (forall w,
                 let spat = (qp SophosLeakage.h{1} w) in
                 let wsim = head witness spat in
                    (0 < size spat /\ !dom G16_Client.ws w => !dom SSIM.wssim{1} wsim)
                 /\ (0 < size spat /\ dom G16_Client.ws w => SSIM.wssim{1}.[wsim] = G16_Client.ws.[w])
               ){2}
            /\ (forall w, dom G16_Client.uh w =>
                 let ap = filter (fun (z: int * operation * index), z.`2 = ADD) (ahpU SophosLeakage.h{1} w) in
                 let ul = oget G16_Client.uh.[w] in
                 forall i, 0 <= i < size ul =>
                   let apentry = (nth witness ap i) in
                   let j = apentry.`1 in
                   let ind = apentry.`3 in
                   let u = (nth witness ul i).`1 in
                       dom G16_Client.utt u
                    /\ dom G16_Client.et u
                    /\ u < size SophosLeakage.h{1}
                    /\ j < size SophosLeakage.h{1}
                    /\ G16_Client.utt.[u] = SSIM.utokens{1}.[j]
                    /\ G16_Client.et.[u] = Some (ind +^ (oget SSIM.idxs{1}.[j]))
               ){2}
            /\ (forall x, SSIM.h1t.[x]{1} = G16_Client.h1t.[x]{2})
            /\ (forall x, SSIM.h2t.[x]{1} = G16_Client.h2t.[x]{2})
    ) => //.
  + (* Update *)
    proc.
    sp; if => //.
    inline*; wp => /=.
    case (o{2} = ADD); last first.
    * (* else *)
      rcondf{1} 7; progress; first by wp; skip; progress.
      rcondf{2} 7; progress; first by wp; skip; progress.
      rcondf{1} 9; progress; first by wp; skip; progress.
      wp; skip; progress.
    * (* then *) 
      rcondt{1} 7; progress; first by wp; skip; progress.
      rcondt{2} 7; progress; first by wp; skip; progress.
      rcondt{1} 12; progress; first by wp; skip; progress.
      wp => /=; rnd (fun z, i1{2} +^ z); rnd; wp; skip; move => /= &1 &2 [[[_] [_] [[_ [_ _]]] [_] [[_ [_ [_ [_ _]]]]] ]]; subst.
      move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync] PPTA _; subst => /=; progress; expect 108.
      - (* 1/4 the term q in the document i were never added in the past *)
        smt.
      - rewrite xorwA xorwK xorwC xorw0 //.
      - smt.
      - smt.
      - rewrite xorwA xorwK xorwC xorw0 //.
      - rewrite 2!get_set_sameE //.
      - rewrite get_set_sameE xorwA xorwK xorwC xorw0 //.
      - smt.
      - rewrite size_cat //=.
      - rewrite cats1 indexed_rcons //.
      - move : H9 (atomic_operations x); rewrite mem_cat /=.
        case (mem SophosLeakage.h{1} x) => //= xmem.
        move => rwme; rewrite -rwme //.
      - move : H9 (atomic_operations x); rewrite mem_cat /=.
        case (mem SophosLeakage.h{1} x) => //= xmem.
        move => rwme; rewrite rwme //.
      - case (w = q{2}) => wq.
        + rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= oget_some /= /=.
          rewrite -size_eq0 size_cat /= eq_sym neq_ltz; left.
          rewrite -lez_add1r addzC lez_add2r size_ge0 //.
        + move : H9; rewrite mem_set wq /= => w_dom.
          move : (leakage w); rewrite w_dom /=.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /=.
          rewrite -size_eq0 eq_sym neq_ltz 2!ltzNge -ltzNge size_ge0 /= size_gt0 /=; move => [x s] => pre.
          rewrite -pre //.
      - rewrite mem_set.
        case (w = q{2}) => //= wq.
        rewrite leakage.
        move : H9; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
        rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
        rewrite (eq_sym _ w) wq /= /= /= cats0 //.
      - case (w = q{2}) => wq.
        + move : (leakage q{2}); rewrite H /= -size_eq0.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 2!filter_cat 2!map_cat filter_cat 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
          move => rwme.
          rewrite (eq_sym _ w) wq /= /= oget_some /= /=.
          rewrite get_set_sameE 2!oget_some size_cat rwme //.
        + move : H9; rewrite mem_set wq /= => w_dom.
          move : (leakage_size w w_dom).
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /= cats0 get_set_neqE //.
      - move : (kw_sync w); rewrite 2!H9; move => [concl _]; move : concl.
        rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map filter_cat /= cats0 //.
      - move : (kw_sync w); rewrite 2!H9; rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= size_map filter_cat /= cats0 //.
      - move : H10 (kw_sync w); rewrite H9 /=.
        rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map filter_cat /= cats0 // => pre.
        rewrite pre //.
      - move : H10 (kw_sync w); rewrite H9 /=.
        rewrite /qp /projQueries /hist -filter_predI /predI -map_comp /(\o) /= //= size_map /= size_cat /= addzC lez_add1r; move => pre [aux] concl.
        move : (concl j).
        rewrite lez_eqVlt pre //.
      - move : H9 (wssim_ws_sync w); rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map filter_cat /= cats0 // => pre.
        rewrite pre H10 //.
      - move : H9 H10 (wssim_ws_sync w); rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map filter_cat /= cats0 // => pre1 pre2.
        rewrite pre1 2!pre2 //.
      - case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some /= => pre.
          have ->/=: i3 = 0 by smt.
          rewrite mem_set //.
        + move : H9 H11; rewrite mem_set wq /= get_set_neqE // => w_dom ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [concl] _.
          rewrite mem_set concl //.
      - case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some /= => pre.
          have ->/=: i3 = 0 by smt.
          rewrite mem_set //.
        + move : H9 H11; rewrite mem_set wq /= get_set_neqE // => w_dom ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [concl] _.
          rewrite mem_set concl //.
      - case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some /= => pre.
          have ->/=: i3 = 0 by smt.
          rewrite size_cat /= -lez_add1r addzC lez_add2r //.
        + move : H9 H11; rewrite mem_set wq /= get_set_neqE // => w_dom ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [_] [concl] _.
          rewrite size_cat /= -lez_add1r addzC lez_add2r lez_eqVlt concl //.
      - case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some /= => pre.
          have ->/=: i3 = 0 by smt.
          rewrite size_cat /= -lez_add1r addzC lez_add2r //.
          move : (leakage q{2}); rewrite H /=.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat => rwme.
          rewrite rwme /= oget_some /= /= //=.
        + move : H9 H11; rewrite mem_set wq /= get_set_neqE // => w_dom ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [_] [_] [concl] _.
          move : concl; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat /= oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /= cats0 => concl.
          rewrite size_cat /= -lez_add1r addzC lez_add2r lez_eqVlt /= concl //.
      - case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some /= => pre.
          have ->/=: i3 = 0 by smt.
          move : (leakage q{2}); rewrite H /=.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat => rwme.
          rewrite rwme /= oget_some /= /= /= 2!get_set_sameE //.
        + move : H9 H11; rewrite mem_set wq /= get_set_neqE // => w_dom ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [_] [aux1] [aux2] [concl] _.
          move : aux2 concl; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat /= oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /= cats0 => aux2 concl.
          rewrite get_set_neqE; first by rewrite neq_ltz aux1 //.
          rewrite get_set_neqE; first by rewrite neq_ltz aux2 //.
          exact concl.
      - case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some /= => pre.
          have ->/=: i3 = 0 by smt.
          move : (leakage q{2}); rewrite H /=.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat => rwme.
          rewrite rwme /= oget_some /= /= /= 2!get_set_sameE //.
        + move : H9 H11; rewrite mem_set wq /= get_set_neqE // => w_dom ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [_] [aux1] [aux2] [_ concl].
          move : aux2 concl; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat /= oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /= cats0 => aux2 concl.
          rewrite get_set_neqE; first by rewrite neq_ltz aux1 //.
          rewrite get_set_neqE; first by rewrite neq_ltz aux2 //.
          exact concl.
      - (* 2/4 query was never added in the past, but index was *)
        smt.
      - rewrite xorwA xorwK xorwC xorw0 //.
      - smt.
      - smt.
      - rewrite xorwA xorwK xorwC xorw0 //.
      - rewrite 2!get_set_sameE //.
      - rewrite get_set_sameE xorwA xorwK xorwC xorw0 //.
      - smt.
      - rewrite size_cat //=.
      - rewrite cats1 indexed_rcons //.
      - move : H9 (atomic_operations x); rewrite mem_cat /=.
        case (mem SophosLeakage.h{1} x) => //= xmem.
        move => rwme; rewrite -rwme //.
      - move : H9 (atomic_operations x); rewrite mem_cat /=.
        case (mem SophosLeakage.h{1} x) => //= xmem.
        move => rwme; rewrite rwme //.
      - case (w = q{2}) => wq.
        + rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= oget_some /= /=.
          rewrite -size_eq0 size_cat /= eq_sym neq_ltz; left.
          rewrite -lez_add1r addzC lez_add2r size_ge0 //.
        + move : H9; rewrite mem_set wq /= => w_dom.
          move : (leakage w); rewrite w_dom /=.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /=.
          rewrite -size_eq0 eq_sym neq_ltz 2!ltzNge -ltzNge size_ge0 /= size_gt0 /=; move => [x s] => pre.
          rewrite -pre //.
      - rewrite mem_set.
        case (w = q{2}) => //= wq.
        rewrite leakage.
        move : H9; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
        rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
        rewrite (eq_sym _ w) wq /= /= /= cats0 //.
      - case (w = q{2}) => wq.
        + move : (leakage q{2}); rewrite H /= -size_eq0.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 2!filter_cat 2!map_cat filter_cat 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
          move => rwme.
          rewrite (eq_sym _ w) wq /= /= oget_some /= /=.
          rewrite get_set_sameE 2!oget_some size_cat rwme //.
        + move : H9; rewrite mem_set wq /= => w_dom.
          move : (leakage_size w w_dom).
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /= cats0 get_set_neqE //.
      - move : (kw_sync w); rewrite 2!H9; move => [concl _]; move : concl.
        rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map filter_cat /= cats0 //.
      - move : (kw_sync w); rewrite 2!H9; rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= size_map filter_cat /= cats0 //.
      - move : H10 (kw_sync w); rewrite H9 /=.
        rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map filter_cat /= cats0 // => pre.
        rewrite pre //.
      - move : H10 (kw_sync w); rewrite H9 /=.
        rewrite /qp /projQueries /hist -filter_predI /predI -map_comp /(\o) /= //= size_map /= size_cat /= addzC lez_add1r; move => pre [aux] concl.
        move : (concl j).
        rewrite lez_eqVlt pre //.
      - move : H9 (wssim_ws_sync w); rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map filter_cat /= cats0 // => pre.
        rewrite pre H10 //.
      - move : H9 H10 (wssim_ws_sync w); rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map filter_cat /= cats0 // => pre1 pre2.
        rewrite pre1 2!pre2 //.
      - case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some /= => pre.
          have ->/=: i3 = 0 by smt.
          rewrite mem_set //.
        + move : H9 H11; rewrite mem_set wq /= get_set_neqE // => w_dom ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [concl] _.
          rewrite mem_set concl //.
      - case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some /= => pre.
          have ->/=: i3 = 0 by smt.
          rewrite mem_set //.
        + move : H9 H11; rewrite mem_set wq /= get_set_neqE // => w_dom ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [concl] _.
          rewrite mem_set concl //.
      - case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some /= => pre.
          have ->/=: i3 = 0 by smt.
          rewrite size_cat /= -lez_add1r addzC lez_add2r //.
        + move : H9 H11; rewrite mem_set wq /= get_set_neqE // => w_dom ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [_] [concl] _.
          rewrite size_cat /= -lez_add1r addzC lez_add2r lez_eqVlt concl //.
      - case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some /= => pre.
          have ->/=: i3 = 0 by smt.
          rewrite size_cat /= -lez_add1r addzC lez_add2r //.
          move : (leakage q{2}); rewrite H /=.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat => rwme.
          rewrite rwme /= oget_some /= /= //=.
        + move : H9 H11; rewrite mem_set wq /= get_set_neqE // => w_dom ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [_] [_] [concl] _.
          move : concl; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat /= oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /= cats0 => concl.
          rewrite size_cat /= -lez_add1r addzC lez_add2r lez_eqVlt /= concl //.
      - case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some /= => pre.
          have ->/=: i3 = 0 by smt.
          move : (leakage q{2}); rewrite H /=.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat => rwme.
          rewrite rwme /= oget_some /= /= /= 2!get_set_sameE //.
        + move : H9 H11; rewrite mem_set wq /= get_set_neqE // => w_dom ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [_] [aux1] [aux2] [concl] _.
          move : aux2 concl; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat /= oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /= cats0 => aux2 concl.
          rewrite get_set_neqE; first by rewrite neq_ltz aux1 //.
          rewrite get_set_neqE; first by rewrite neq_ltz aux2 //.
          exact concl.
      - case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some /= => pre.
          have ->/=: i3 = 0 by smt.
          move : (leakage q{2}); rewrite H /=.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat => rwme.
          rewrite rwme /= oget_some /= /= /= 2!get_set_sameE //.
        + move : H9 H11; rewrite mem_set wq /= get_set_neqE // => w_dom ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [_] [aux1] [aux2] [_ concl].
          move : aux2 concl; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat /= oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /= cats0 => aux2 concl.
          rewrite get_set_neqE; first by rewrite neq_ltz aux1 //.
          rewrite get_set_neqE; first by rewrite neq_ltz aux2 //.
          exact concl.
      - (* 3/4 the term q was already added, but for a different index *)
        smt.
      - rewrite xorwA xorwK xorwC xorw0 //.
      - smt.
      - smt.
      - rewrite xorwA xorwK xorwC xorw0 //.
      - rewrite 2!get_set_sameE //.
      - rewrite get_set_sameE xorwA xorwK xorwC xorw0 //.
      - smt.
      - rewrite size_cat //=.
      - rewrite cats1 indexed_rcons //.
      - move : H9 (atomic_operations x); rewrite mem_cat /=.
        case (mem SophosLeakage.h{1} x) => //= xmem.
        move => rwme; rewrite -rwme //.
      - move : H9 (atomic_operations x); rewrite mem_cat /=.
        case (mem SophosLeakage.h{1} x) => //= xmem.
        move => rwme; rewrite rwme //.
      - case (w = q{2}) => wq.
        + rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= oget_some /= /=.
          rewrite -size_eq0 size_cat /= eq_sym neq_ltz; left.
          rewrite -lez_add1r addzC lez_add2r size_ge0 //.
        + move : H9; rewrite mem_set wq /= => w_dom.
          move : (leakage w); rewrite w_dom /=.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /=.
          rewrite -size_eq0 eq_sym neq_ltz 2!ltzNge -ltzNge size_ge0 /= size_gt0 /=; move => [x s] => pre.
          rewrite -pre //.
      - rewrite mem_set.
        case (w = q{2}) => //= wq.
        rewrite leakage.
        move : H9; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
        rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
        rewrite (eq_sym _ w) wq /= /= /= cats0 //.
      - have w_dom: dom G16_Client.uh{2} w by move : H H9; rewrite mem_set //= => q_dom; case (w = q{2}) => //.
        move : (leakage_size w w_dom).
        rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
        rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
        case (w = q{2}) => wq.
        + rewrite (eq_sym _ w) wq /= /= oget_some /= /=.
          rewrite get_set_sameE 2!oget_some 2!size_cat /= eqz_add2r //.
        + rewrite (eq_sym _ w) wq /= /= /= cats0 get_set_neqE //.
      - move : (kw_sync w); rewrite 2!H9; move => [concl _]; move : concl.
        rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map filter_cat /= cats0 //.
      - move : (kw_sync w); rewrite 2!H9; rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= size_map filter_cat /= cats0 //.
      - move : H10 (kw_sync w); rewrite H9 /=.
        rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map filter_cat /= cats0 // => pre.
        rewrite pre //.
      - move : H10 (kw_sync w); rewrite H9 /=.
        rewrite /qp /projQueries /hist -filter_predI /predI -map_comp /(\o) /= //= size_map /= size_cat /= addzC lez_add1r; move => pre [aux] concl.
        move : (concl j).
        rewrite lez_eqVlt pre //.
      - move : H9 (wssim_ws_sync w); rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map filter_cat /= cats0 // => pre.
        rewrite pre H10 //.
      - move : H9 H10 (wssim_ws_sync w); rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map filter_cat /= cats0 // => pre1 pre2.
        rewrite pre1 2!pre2 //.
      - have w_dom: dom G16_Client.uh{2} w by move : H H9; rewrite mem_set //= => q_dom; case (w = q{2}) => //.
        case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some size_cat /= => pre.
          rewrite nth_cat.
          case ((i3 = size (oget G16_Client.uh.[q])){2}) => last_el.
          * rewrite last_el /= mem_set //.
          * have pre': i3 < size (oget G16_Client.uh{2}.[q{2}]) by rewrite ltz_def eq_sym last_el -(lez_add2l 1) lez_add1r addzC pre /=.
            move : (hash_backup w w_dom i3); rewrite wq H10 pre' /=; move => [concl] _.
            rewrite mem_set; left.
            exact concl.
        + move : H11; rewrite /= get_set_neqE // => ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [concl] _.
          rewrite mem_set concl //.
      - have w_dom: dom G16_Client.uh{2} w by move : H H9; rewrite mem_set //= => q_dom; case (w = q{2}) => //.
        case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some size_cat /= => pre.
          rewrite nth_cat.
          case ((i3 = size (oget G16_Client.uh.[q])){2}) => last_el.
          * rewrite last_el /= mem_set //.
          * have pre': i3 < size (oget G16_Client.uh{2}.[q{2}]) by rewrite ltz_def eq_sym last_el -(lez_add2l 1) lez_add1r addzC pre /=.
            move : (hash_backup w w_dom i3); rewrite wq H10 pre' /=; move => [_] [concl] _.
            rewrite mem_set; left.
            exact concl.
        + move : H11; rewrite /= get_set_neqE // => ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [concl] _.
          rewrite mem_set concl //.
      - have w_dom: dom G16_Client.uh{2} w by move : H H9; rewrite mem_set //= => q_dom; case (w = q{2}) => //.
        case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some size_cat /= => pre.
          rewrite nth_cat.
          case ((i3 = size (oget G16_Client.uh.[q])){2}) => last_el.
          * rewrite last_el /= size_cat /= -lez_add1r addzC lez_add2r //.
          * have pre': i3 < size (oget G16_Client.uh{2}.[q{2}]) by rewrite ltz_def eq_sym last_el -(lez_add2l 1) lez_add1r addzC pre /=.
            move : (hash_backup w w_dom i3); rewrite wq H10 pre' /=; move => [_] [_] [concl] _.
            rewrite size_cat /= -lez_add1r addzC lez_add2r lez_eqVlt /= concl //.
        + move : H11; rewrite /= get_set_neqE // => ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [_] [concl] _.
          rewrite size_cat /= -lez_add1r addzC lez_add2r lez_eqVlt concl //.
      - have w_dom: dom G16_Client.uh{2} w by move : H H9; rewrite mem_set //= => q_dom; case (w = q{2}) => //.
        case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some size_cat /= => pre.
          rewrite /= in H; move : (leakage_size q{2}); rewrite H /=.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat => rwme.
          rewrite nth_cat rwme /= oget_some /= /= oget_some /= /= /=.
          case ((i3 = size (oget G16_Client.uh.[q])){2}) => last_el.
          * rewrite last_el /= size_cat /= -lez_add1r addzC lez_add2r //.
          * have pre': i3 < size (oget G16_Client.uh{2}.[q{2}]) by rewrite ltz_def eq_sym last_el -(lez_add2l 1) lez_add1r addzC pre /=.
            move : (hash_backup w w_dom i3); rewrite wq H10 pre' /=; move => [_] [_] [_] [concl] _.
          move : concl; rewrite /ahpU /projUpdates /hist /= /= /= 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= => concl.
          rewrite size_cat /= -lez_add1r addzC lez_add2r lez_eqVlt /= concl //.
        + move : H11; rewrite get_set_neqE // => ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [_] [_] [concl] _.
          move : concl; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat /= oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /= cats0 => concl.
          rewrite size_cat /= -lez_add1r addzC lez_add2r lez_eqVlt /= concl //.
      - have w_dom: dom G16_Client.uh{2} w by move : H H9; rewrite mem_set //= => q_dom; case (w = q{2}) => //.
        case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some size_cat /= => pre.
          rewrite /= in H; move : (leakage_size q{2}); rewrite H /=.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat => rwme.
          rewrite 2!nth_cat /= oget_some /= /= oget_some /= /= /= rwme.
          case ((i3 = size (oget G16_Client.uh.[q])){2}) => last_el.
          * rewrite last_el /= 2!get_set_sameE //.
          * have pre': i3 < size (oget G16_Client.uh{2}.[q{2}]) by rewrite ltz_def eq_sym last_el -(lez_add2l 1) lez_add1r addzC pre /=.
            move : (hash_backup w w_dom i3); rewrite wq H10 pre' /=; move => [_] [_] [aux1] [aux2] [concl] _.
          move : aux2 concl; rewrite /ahpU /projUpdates /hist /= /= /= 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= => aux2 concl.
          rewrite get_set_neqE; first by rewrite neq_ltz aux1 //.
          rewrite get_set_neqE; first by rewrite neq_ltz aux2 //.
          exact concl.
        + move : H11; rewrite get_set_neqE // => ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [_] [aux1] [aux2] [concl] _.
          move : aux2 concl; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat /= oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /= cats0 => aux2 concl.
          rewrite get_set_neqE; first by rewrite neq_ltz aux1 //.
          rewrite get_set_neqE; first by rewrite neq_ltz aux2 //.
          exact concl.
      - have w_dom: dom G16_Client.uh{2} w by move : H H9; rewrite mem_set //= => q_dom; case (w = q{2}) => //.
        case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some size_cat /= => pre.
          rewrite /= in H; move : (leakage_size q{2}); rewrite H /=.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat => rwme.
          rewrite 2!nth_cat /= oget_some /= /= oget_some /= /= /= rwme.
          case ((i3 = size (oget G16_Client.uh.[q])){2}) => last_el.
          * rewrite last_el /= 2!get_set_sameE //.
          * have pre': i3 < size (oget G16_Client.uh{2}.[q{2}]) by rewrite ltz_def eq_sym last_el -(lez_add2l 1) lez_add1r addzC pre /=.
            move : (hash_backup w w_dom i3); rewrite wq H10 pre' /=; move => [_] [_] [aux1] [aux2] [_ concl].
          move : aux2 concl; rewrite /ahpU /projUpdates /hist /= /= /= 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= => aux2 concl.
          rewrite get_set_neqE; first by rewrite neq_ltz aux1 //.
          rewrite get_set_neqE; first by rewrite neq_ltz aux2 //.
          exact concl.
        + move : H11; rewrite get_set_neqE // => ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [_] [aux1] [aux2] [_ concl].
          move : aux2 concl; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat /= oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /= cats0 => aux2 concl.
          rewrite get_set_neqE; first by rewrite neq_ltz aux1 //.
          rewrite get_set_neqE; first by rewrite neq_ltz aux2 //.
          exact concl.
      - (* 4/4 the term q was already added for the same index *)
        smt.
      - rewrite xorwA xorwK xorwC xorw0 //.
      - smt.
      - smt.
      - rewrite xorwA xorwK xorwC xorw0 //.
      - rewrite 2!get_set_sameE //.
      - rewrite get_set_sameE xorwA xorwK xorwC xorw0 //.
      - smt.
      - rewrite size_cat //=.
      - rewrite cats1 indexed_rcons //.
      - move : H9 (atomic_operations x); rewrite mem_cat /=.
        case (mem SophosLeakage.h{1} x) => //= xmem.
        move => rwme; rewrite -rwme //.
      - move : H9 (atomic_operations x); rewrite mem_cat /=.
        case (mem SophosLeakage.h{1} x) => //= xmem.
        move => rwme; rewrite rwme //.
      - case (w = q{2}) => wq.
        + rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= oget_some /= /=.
          rewrite -size_eq0 size_cat /= eq_sym neq_ltz; left.
          rewrite -lez_add1r addzC lez_add2r size_ge0 //.
        + move : H9; rewrite mem_set wq /= => w_dom.
          move : (leakage w); rewrite w_dom /=.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /=.
          rewrite -size_eq0 eq_sym neq_ltz 2!ltzNge -ltzNge size_ge0 /= size_gt0 /=; move => [x s] => pre.
          rewrite -pre //.
      - rewrite mem_set.
        case (w = q{2}) => //= wq.
        rewrite leakage.
        move : H9; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
        rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
        rewrite (eq_sym _ w) wq /= /= /= cats0 //.
      - have w_dom: dom G16_Client.uh{2} w by move : H H9; rewrite mem_set //= => q_dom; case (w = q{2}) => //.
        move : (leakage_size w w_dom).
        rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
        rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) oget_some /= /= /=.
        case (w = q{2}) => wq.
        + rewrite (eq_sym _ w) wq /= /= oget_some /= /=.
          rewrite get_set_sameE 2!oget_some 2!size_cat /= eqz_add2r //.
        + rewrite (eq_sym _ w) wq /= /= /= cats0 get_set_neqE //.
      - move : (kw_sync w); rewrite 2!H9; move => [concl _]; move : concl.
        rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map filter_cat /= cats0 //.
      - move : (kw_sync w); rewrite 2!H9; rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= size_map filter_cat /= cats0 //.
      - move : H10 (kw_sync w); rewrite H9 /=.
        rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map filter_cat /= cats0 // => pre.
        rewrite pre //.
      - move : H10 (kw_sync w); rewrite H9 /=.
        rewrite /qp /projQueries /hist -filter_predI /predI -map_comp /(\o) /= //= size_map /= size_cat /= addzC lez_add1r; move => pre [aux] concl.
        move : (concl j).
        rewrite lez_eqVlt pre //.
      - move : H9 (wssim_ws_sync w); rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map filter_cat /= cats0 // => pre.
        rewrite pre H10 //.
      - move : H9 H10 (wssim_ws_sync w); rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map filter_cat /= cats0 // => pre1 pre2.
        rewrite pre1 2!pre2 //.
      - have w_dom: dom G16_Client.uh{2} w by move : H H9; rewrite mem_set //= => q_dom; case (w = q{2}) => //.
        case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some size_cat /= => pre.
          rewrite nth_cat.
          case ((i3 = size (oget G16_Client.uh.[q])){2}) => last_el.
          * rewrite last_el /= mem_set //.
          * have pre': i3 < size (oget G16_Client.uh{2}.[q{2}]) by rewrite ltz_def eq_sym last_el -(lez_add2l 1) lez_add1r addzC pre /=.
            move : (hash_backup w w_dom i3); rewrite wq H10 pre' /=; move => [concl] _.
            rewrite mem_set; left.
            exact concl.
        + move : H11; rewrite /= get_set_neqE // => ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [concl] _.
          rewrite mem_set concl //.
      - have w_dom: dom G16_Client.uh{2} w by move : H H9; rewrite mem_set //= => q_dom; case (w = q{2}) => //.
        case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some size_cat /= => pre.
          rewrite nth_cat.
          case ((i3 = size (oget G16_Client.uh.[q])){2}) => last_el.
          * rewrite last_el /= mem_set //.
          * have pre': i3 < size (oget G16_Client.uh{2}.[q{2}]) by rewrite ltz_def eq_sym last_el -(lez_add2l 1) lez_add1r addzC pre /=.
            move : (hash_backup w w_dom i3); rewrite wq H10 pre' /=; move => [_] [concl] _.
            rewrite mem_set; left.
            exact concl.
        + move : H11; rewrite /= get_set_neqE // => ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [concl] _.
          rewrite mem_set concl //.
      - have w_dom: dom G16_Client.uh{2} w by move : H H9; rewrite mem_set //= => q_dom; case (w = q{2}) => //.
        case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some size_cat /= => pre.
          rewrite nth_cat.
          case ((i3 = size (oget G16_Client.uh.[q])){2}) => last_el.
          * rewrite last_el /= size_cat /= -lez_add1r addzC lez_add2r //.
          * have pre': i3 < size (oget G16_Client.uh{2}.[q{2}]) by rewrite ltz_def eq_sym last_el -(lez_add2l 1) lez_add1r addzC pre /=.
            move : (hash_backup w w_dom i3); rewrite wq H10 pre' /=; move => [_] [_] [concl] _.
            rewrite size_cat /= -lez_add1r addzC lez_add2r lez_eqVlt /= concl //.
        + move : H11; rewrite /= get_set_neqE // => ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [_] [concl] _.
          rewrite size_cat /= -lez_add1r addzC lez_add2r lez_eqVlt concl //.
      - have w_dom: dom G16_Client.uh{2} w by move : H H9; rewrite mem_set //= => q_dom; case (w = q{2}) => //.
        case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some size_cat /= => pre.
          rewrite /= in H; move : (leakage_size q{2}); rewrite H /=.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat => rwme.
          rewrite nth_cat rwme /= oget_some /= /= oget_some /= /= /=.
          case ((i3 = size (oget G16_Client.uh.[q])){2}) => last_el.
          * rewrite last_el /= size_cat /= -lez_add1r addzC lez_add2r //.
          * have pre': i3 < size (oget G16_Client.uh{2}.[q{2}]) by rewrite ltz_def eq_sym last_el -(lez_add2l 1) lez_add1r addzC pre /=.
            move : (hash_backup w w_dom i3); rewrite wq H10 pre' /=; move => [_] [_] [_] [concl] _.
          move : concl; rewrite /ahpU /projUpdates /hist /= /= /= 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= => concl.
          rewrite size_cat /= -lez_add1r addzC lez_add2r lez_eqVlt /= concl //.
        + move : H11; rewrite get_set_neqE // => ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [_] [_] [concl] _.
          move : concl; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat /= oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /= cats0 => concl.
          rewrite size_cat /= -lez_add1r addzC lez_add2r lez_eqVlt /= concl //.
      - have w_dom: dom G16_Client.uh{2} w by move : H H9; rewrite mem_set //= => q_dom; case (w = q{2}) => //.
        case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some size_cat /= => pre.
          rewrite /= in H; move : (leakage_size q{2}); rewrite H /=.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat => rwme.
          rewrite 2!nth_cat /= oget_some /= /= oget_some /= /= /= rwme.
          case ((i3 = size (oget G16_Client.uh.[q])){2}) => last_el.
          * rewrite last_el /= 2!get_set_sameE //.
          * have pre': i3 < size (oget G16_Client.uh{2}.[q{2}]) by rewrite ltz_def eq_sym last_el -(lez_add2l 1) lez_add1r addzC pre /=.
            move : (hash_backup w w_dom i3); rewrite wq H10 pre' /=; move => [_] [_] [aux1] [aux2] [concl] _.
          move : aux2 concl; rewrite /ahpU /projUpdates /hist /= /= /= 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= => aux2 concl.
          rewrite get_set_neqE; first by rewrite neq_ltz aux1 //.
          rewrite get_set_neqE; first by rewrite neq_ltz aux2 //.
          exact concl.
        + move : H11; rewrite get_set_neqE // => ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [_] [aux1] [aux2] [concl] _.
          move : aux2 concl; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat /= oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /= cats0 => aux2 concl.
          rewrite get_set_neqE; first by rewrite neq_ltz aux1 //.
          rewrite get_set_neqE; first by rewrite neq_ltz aux2 //.
          exact concl.
      - have w_dom: dom G16_Client.uh{2} w by move : H H9; rewrite mem_set //= => q_dom; case (w = q{2}) => //.
        case (w = q{2}) => wq.
        + move : H11; rewrite wq get_set_sameE oget_some size_cat /= => pre.
          rewrite /= in H; move : (leakage_size q{2}); rewrite H /=.
          rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat => rwme.
          rewrite 2!nth_cat /= oget_some /= /= oget_some /= /= /= rwme.
          case ((i3 = size (oget G16_Client.uh.[q])){2}) => last_el.
          * rewrite last_el /= 2!get_set_sameE //.
          * have pre': i3 < size (oget G16_Client.uh{2}.[q{2}]) by rewrite ltz_def eq_sym last_el -(lez_add2l 1) lez_add1r addzC pre /=.
            move : (hash_backup w w_dom i3); rewrite wq H10 pre' /=; move => [_] [_] [aux1] [aux2] [_ concl].
          move : aux2 concl; rewrite /ahpU /projUpdates /hist /= /= /= 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= => aux2 concl.
          rewrite get_set_neqE; first by rewrite neq_ltz aux1 //.
          rewrite get_set_neqE; first by rewrite neq_ltz aux2 //.
          exact concl.
        + move : H11; rewrite get_set_neqE // => ilt.
          move : (hash_backup w w_dom i3); rewrite H10 ilt; move => [_] [_] [aux1] [aux2] [_ concl].
          move : aux2 concl; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
          rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /= /= filter_cat map_cat /= oget_some /= /= /=.
          rewrite (eq_sym _ w) wq /= /= /= cats0 => aux2 concl.
          rewrite get_set_neqE; first by rewrite neq_ltz aux1 //.
          rewrite get_set_neqE; first by rewrite neq_ltz aux2 //.
          exact concl.
  + (* Search *)
    proc.
    sp; if => //.
    inline*.
    case ((dom G16_Client.uh q){2}).
    + rcondf{2} 3; progress; first by wp; skip; progress.
      rcondt{1} 8; progress.
        wp; skip; move => /= &hr [[[_] [_] [_] [_] [[_ _]]]]; subst.
        move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync] PPTA q_dom; subst; progress.
        move : (leakage q{m0}); rewrite q_dom /=.
        rewrite /ahpU /projUpdates /hist 2!filter_cat 2!map_cat filter_cat.
        rewrite -size_eq0 eq_sym neq_ltz 2!ltzNge -ltzNge size_ge0 /= size_gt0 /=; move => [x s] => pre.
        rewrite -pre //.
      rcondf{2} 15; progress.
        wp; while (true); progress.
      swap{1} 21 -2; swap{1} 12 7; swap{1} 22 -21.
      swap{2} 7 4; swap{2} 6 2; swap{2} 13 -12.
      seq 15 8: (={glob OracleCallsCounter}
            /\   (     SSIM.pk,       SSIM.sk,      SSIM.edb,       SSIM.t, size (SophosLeakage.h)){1}
               = (G4_Server.pk, G16_Client.sk, G4_Server.edb, G16_Client.t,           G16_Client.t){2}
            /\   (SSIM.keys.[w],    SSIM.wssim.[w]){1}
               = (     RF.m.[q], G16_Client.ws.[q]){2}
            /\ ={q, kw, s}
            /\ (q1 = q){2}
            /\ (addpat = filter (fun (x: int * operation * index) => x.`2 = ADD) (ahpU SophosLeakage.h q)){1}
            /\ (w = head witness (qp SophosLeakage.h q)){1}
            /\ (0 < size (qp SophosLeakage.h{1} q)){2}
            /\ (dom G16_Client.uh q){2}
            /\ (dom G16_Client.ws q){2}

            /\ (validkeypair (SSIM.pk, SSIM.sk)){1}
            /\ (indexed SophosLeakage.h){1}
            /\ (forall x, mem SophosLeakage.h x => (oh_update x <> None <=> oh_query x = None)){1}
            /\ (forall w, dom G16_Client.uh{2} w <=>
                 filter (fun (z: int * operation * index), z.`2 = ADD) (ahpU SophosLeakage.h{1} w) <> []
               )
            /\ (forall w, dom G16_Client.uh w =>
                    size (filter (fun (z: int * operation * index), z.`2 = ADD) (ahpU SophosLeakage.h{1} w)) = size (oget G16_Client.uh.[w])
               ){2}
            /\ (forall w, dom RF.m w <=> dom G16_Client.ws w){2}
            /\ (forall k, dom SSIM.wssim k <=> dom SSIM.keys k){1}
            /\ (forall w,
                 let spat = (qp SophosLeakage.h{1} w) in
                 let wsim = head witness spat in
                    (dom RF.m w => 0 < size spat /\ SSIM.keys{1}.[wsim] = RF.m.[w])
                 /\ (!dom RF.m w => (0 < size spat => !dom SSIM.keys{1} wsim) /\ forall j, (size SophosLeakage.h{1}) <= j => !dom SSIM.keys{1} j)
               ){2}
            /\ (forall w,
                 let spat = (qp SophosLeakage.h{1} w) in
                 let wsim = head witness spat in
                    (0 < size spat /\ !dom G16_Client.ws w => !dom SSIM.wssim{1} wsim)
                 /\ (0 < size spat /\ dom G16_Client.ws w => SSIM.wssim{1}.[wsim] = G16_Client.ws.[w])
               ){2}
            /\ (forall w, dom G16_Client.uh w =>
                 let ap = filter (fun (z: int * operation * index), z.`2 = ADD) (ahpU SophosLeakage.h{1} w) in
                 let ul = oget G16_Client.uh.[w] in
                 forall i, 0 <= i < size ul =>
                   let apentry = (nth witness ap i) in
                   let j = apentry.`1 in
                   let ind = apentry.`3 in
                   let u = (nth witness ul i).`1 in
                       dom G16_Client.utt u
                    /\ dom G16_Client.et u
                    /\ u < size SophosLeakage.h{1}
                    /\ j < size SophosLeakage.h{1}
                    /\ G16_Client.utt.[u] = SSIM.utokens{1}.[j]
                    /\ G16_Client.et.[u] = Some (ind +^ (oget SSIM.idxs{1}.[j]))
               ){2}
            /\ (forall x, SSIM.h1t.[x]{1} = G16_Client.h1t.[x]{2})
            /\ (forall x, SSIM.h2t.[x]{1} = G16_Client.h2t.[x]{2})
        ).
        case ((dom RF.m q){2}).
        * (* Query already searched in the past *)
          rcondf{2} 5; progress.
            wp; skip; progress.
          rcondf{2} 6; progress.
            wp; skip; move => &hr [[[[_] [_] [_] [_] [[_] [_] [_] [_] _]]]]; subst.
            move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress.
            rewrite -kw_ws_sync //.
          rcondf{1} 11; progress.
            wp; skip; move => &hr [[[[_] [_] [_] [_] [[_] [_] [_] [_] _]]]]; subst.
            move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress.
            move : (kw_sync q{m0}); rewrite 2!H1 /=.
            rewrite /qp /projQueries /hist -2!filter_predI /predI -2!map_comp /(\o) /= //= filter_cat /= map_cat size_map //; move => [aux rwme].
            rewrite head_cat; first by rewrite -size_eq0 size_map eq_sym neq_ltz aux //.
            move : H1; rewrite 2!domE -rwme //.
          rcondf{1} 13; progress.
            wp; skip; move => &hr [[[[_] [_] [_] [_] [[_] [_] [_] [_] _]]]]; subst.
            move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress.
            move : (kw_sync q{m0}); rewrite 2!H1 /=; move => [aux rwme].
            rewrite kw_wssim_sync qp_cat head_cat; first by rewrite -size_eq0 eq_sym neq_ltz aux //.
            rewrite domE rwme -domE //.
          wp => /=; skip.
          move => &1 &2 [[[[_] [_] [_] [_] [[_] [_] [_] [_] _]]]]; subst.
          move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress; expect 24.
          + smt.
          + move : (kw_sync q{2}); rewrite 2!H1 /=; move => [aux concl].
            rewrite qp_cat head_cat; first by rewrite -size_eq0 eq_sym neq_ltz aux //.
            exact concl.
          + move : (kw_sync q{2}); rewrite 2!H1 /=; move => [aux] _.
            move : H1; rewrite kw_ws_sync => q_dom_ws.
            move : (wssim_ws_sync q{2}); rewrite aux 2!q_dom_ws /= => concl.
            rewrite qp_cat head_cat; first by rewrite -size_eq0 eq_sym neq_ltz aux //.
            exact concl.
          + move : (kw_sync q{2}); rewrite 2!H1 /=; move => [aux rwme].
            rewrite qp_cat head_cat; first by rewrite -size_eq0 eq_sym neq_ltz aux //.
            rewrite rwme //.
          + rewrite qp_cat size_cat /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
            rewrite -2!filter_predI /predI -2!map_comp /(\o) /=.
            rewrite -lez_add1r addzC lez_add2r size_ge0 //.
          + rewrite -kw_ws_sync //.
          + rewrite cats1 indexed_rcons //.
          + move : H2 (atomic_operations x2); rewrite mem_cat /=.
            case (mem SophosLeakage.h{1} x2) => //= xmem.
            move => rwme; rewrite -rwme //.
          + move : H2 (atomic_operations x2); rewrite mem_cat /=.
            case (mem SophosLeakage.h{1} x2) => //= xmem.
            move => rwme; rewrite rwme //.
          + move : (leakage w2); rewrite H2 /= -size_eq0.
            rewrite -size_eq0 ahpU_cat filter_cat size_cat.
            rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
            rewrite -2!filter_predI /predI -2!map_comp /(\o) //.
          + move : H2 (leakage w2); rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
            rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) /=.
            case (w2 = q{2}) => // wq.
            rewrite -(eq_sym _ q{2}) wq /= cats0 // => pre.
            rewrite (leakage w2) pre /= //.
          + rewrite ahpU_cat filter_cat size_cat (leakage_size w2 H2).
            rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
            rewrite 2!filter_map /preim -2!filter_predI /predI //.
          + move : (kw_sync w2); rewrite 2!H2 /=.
            rewrite qp_cat size_cat /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
            rewrite -2!filter_predI /predI -2!map_comp /(\o) /=; move => [aux _].
            case (w2 = q{2}) => // wq.
            * rewrite -(eq_sym _ q{2}) wq /= -lez_add1r addzC lez_add2r size_ge0 //.
            * rewrite -(eq_sym _ q{2}) wq /= //.
          + move : (kw_sync w2); rewrite 2!H2 /=; move => [aux] concl.
            rewrite qp_cat head_cat; first by rewrite -size_eq0 eq_sym neq_ltz aux //.
            exact concl.
          + have wq: w2 <> q{2} by move : H2; apply absurd => /= wq; rewrite wq H1 //.
            move : (kw_sync w2); rewrite H2 /=; move => [concl _].
            move : H3 concl; rewrite qp_cat size_cat /=.
            rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
            rewrite -2!filter_predI /predI -2!map_comp /(\o) /= //= 2!size_map /=.
            rewrite (eq_sym _ w2) wq /= => pre.
            rewrite cats0 pre //.
          + have wq: w2 <> q{2} by move : H2; apply absurd => /= wq; rewrite wq H1 //.
            move : (kw_sync w2); rewrite H2 /=; move => [_ concl].
            move : H3 (concl j0); rewrite size_cat /=.
            rewrite addzC lez_add1r => jlt.
            rewrite lez_eqVlt jlt //=.
          + move : (H3); rewrite -kw_ws_sync => w_dom.
            have wq: w2 <> q{2} by move : w_dom; apply absurd => /= wq; rewrite wq H1 //.
            move : H2; rewrite qp_cat size_cat -nth_head nth_cat.
            move : (wssim_ws_sync w2); rewrite H3 /=.
            rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
            rewrite -2!filter_predI /predI -2!map_comp /(\o) /= => concl.
            rewrite (eq_sym _ w2) wq /= => pre.
            move : concl; rewrite nth_head pre //.
          + move : (H3); rewrite -kw_ws_sync => w_dom.
            move : (kw_sync w2); rewrite 2!w_dom /=; move => [aux _].
            rewrite qp_cat head_cat //; first by rewrite -size_eq0 eq_sym neq_ltz aux //.
            move : (wssim_ws_sync w2); rewrite 2!H3 aux //.
          + smt.
          + smt.
          + smt.
          + move : (hash_backup w2 H2 i1); rewrite H3 H4 /=; move => [_] [_] [_] [concl] _.
            rewrite ahpU_cat filter_cat size_cat nth_cat (leakage_size w2 H2) H4 /=.
            rewrite (ltz_trans (size SophosLeakage.h{1})) //.
            rewrite -lez_add1r addzC lez_add2r //.
          + move : (hash_backup w2 H2 i1); rewrite H3 H4 /=; move => [_] [_] [_] [_] [rwme] _.
            rewrite rwme ahpU_cat filter_cat nth_cat (leakage_size w2 H2) H4 //.
          + move : (hash_backup w2 H2 i1); rewrite H3 H4 /=; move => [_] [_] [_] [_] [_ rwme].
            rewrite rwme ahpU_cat filter_cat nth_cat (leakage_size w2 H2) H4 //.
        * (* Query has never been searched *)
          rcondt{2} 5; progress.
            wp; skip; progress.
          rcondt{2} 7; progress.
            wp; rnd; wp; skip; move => &hr [[[[_] [_] [_] [_] [[_] [_] [_] [_] _]]]]; subst.
            move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress.
            rewrite -kw_ws_sync //.
          rcondt{1} 11; progress.
            wp; skip; move => &hr [[[[_] [_] [_] [_] [[_] [_] [_] [_] _]]]]; subst.
            move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress.
            move : (kw_sync q{m0}); rewrite H1 /=.
            case (size (qp SophosLeakage.h{hr} q{m0}) = 0) => //= s0.
            * rewrite s0 /= qp_cat -nth_head nth_cat s0 /=.
              rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
              rewrite -filter_predI /predI -map_comp /(\o) /= /= => concl.
              move : (concl (size SophosLeakage.h{hr})) => //.
            * have ss: 0 < size (qp SophosLeakage.h{hr} q{m0}) by smt.
              rewrite ss qp_cat -2!nth_head nth_cat ss //.
          rcondt{1} 14; progress.
            wp; rnd; wp; skip; move => &hr [[[[_] [_] [_] [_] [[_] [_] [_] [_] _]]]]; subst.
            move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress.
            move : (kw_sync q{m0}); rewrite H1 /=.
            case (size (qp SophosLeakage.h{hr} q{m0}) = 0) => //= s0.
            * rewrite s0 /= kw_wssim_sync qp_cat -nth_head nth_cat s0 /=.
              rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
              rewrite -filter_predI /predI -map_comp /(\o) /= /= => concl.
              move : (concl (size SophosLeakage.h{hr})) => //.
            * have ss: 0 < size (qp SophosLeakage.h{hr} q{m0}) by smt.
              rewrite ss kw_wssim_sync qp_cat -2!nth_head nth_cat ss //.
          wp; rnd; wp; rnd; wp => /=; skip.
          move => &1 &2 [[[[_] [_] [_] [_] [[_] [_] [_] [_] _]]]]; subst.
          move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress; expect 28.
          + rewrite size_cat //.
          + rewrite 2!get_set_sameE //.
          + rewrite 2!get_set_sameE //.
          + rewrite 2!get_set_sameE //.
          + rewrite qp_cat size_cat /=.
            rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
            rewrite -2!filter_predI /predI -2!map_comp /(\o) /= /=.
            rewrite -lez_add1r addzC lez_add2r size_ge0 //.
          + rewrite mem_set //.
          + rewrite cats1 indexed_rcons //.
          + move : H6 (atomic_operations x2); rewrite mem_cat /=.
            case (mem SophosLeakage.h{1} x2) => //= xmem.
            move => rwme; rewrite -rwme //.
          + move : H6 (atomic_operations x2); rewrite mem_cat /=.
            case (mem SophosLeakage.h{1} x2) => //= xmem.
            move => rwme; rewrite rwme //.
          + move : (leakage w2); rewrite H6 /= -size_eq0.
            rewrite -size_eq0 ahpU_cat filter_cat size_cat.
            rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
            rewrite -2!filter_predI /predI -2!map_comp /(\o) //.
          + move : H6 (leakage w2); rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
            rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) /=.
            case (w2 = q{2}) => // wq.
            rewrite -(eq_sym _ q{2}) wq /= cats0 // => pre.
            rewrite (leakage w2) pre /= //.
          + rewrite ahpU_cat filter_cat size_cat (leakage_size w2 H6).
            rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
            rewrite 2!filter_map /preim -2!filter_predI /predI //.
          + move : H6; rewrite 2!mem_set /=.
            case (w2 = q{2}) => //= wq.
            rewrite kw_ws_sync //.
          + move : H6; rewrite 2!mem_set /=.
            case (w2 = q{2}) => //= wq.
            rewrite kw_ws_sync //.
          + move : H6; rewrite 2!mem_set /=.
            rewrite kw_wssim_sync //.
          + move : H6; rewrite 2!mem_set /=.
            rewrite kw_wssim_sync //.
          + move : H6; rewrite mem_set.
            case (w2 = q{2}) => //= wq.
            * rewrite qp_cat size_cat /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
              rewrite -2!filter_predI /predI -2!map_comp /(\o) /=.
              rewrite -(eq_sym w2) wq /=.
              rewrite -lez_add1r addzC lez_add2r size_ge0 //.
            * move => pre; move : (kw_sync w2); rewrite 2!pre /=.
              rewrite qp_cat size_cat /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
              rewrite -2!filter_predI /predI -2!map_comp /(\o) /=.
              rewrite -(eq_sym w2) wq //.
          + move : H6; rewrite mem_set.
            case (w2 = q{2}) => //= wq.
            * rewrite wq 2!get_set_sameE //.
            * move => pre; move : (kw_sync w2) (kw_sync q{2}); rewrite 2!pre H1 /=; move => [aux1] c1 [aux2] c2.
              rewrite qp_cat -nth_head nth_cat /= nth_head.
              rewrite qp_cat head_cat; first by rewrite -size_eq0 eq_sym neq_ltz aux1 //.
              rewrite get_set_neqE.
                have someidx: forall x, mem (qp SophosLeakage.h{1} w2) x => mem (map fst SophosLeakage.h{1}) x.
                  rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
                  rewrite -filter_predI /predI -map_comp /(\o) /= => x.
                  rewrite mem_map_fst; move => [y].
                  rewrite mem_filter /=; move => [_ inside].
                  rewrite mem_map_fst; exists y => //.
                have maxnotthere: forall x, mem (map fst SophosLeakage.h{1}) x => x <> size SophosLeakage.h{1}.
                  move => x; rewrite mem_size_nth size_map; move => [ss] [j] [jrng rwme]; rewrite -rwme.
                  move : (timestamps j jrng); rewrite rwme => xj.
                  move : (timestamps x); rewrite xj jrng /= => _.
                  move : jrng => [_ jlt].
                  rewrite neq_ltz jlt //.
                case (size (qp SophosLeakage.h{1} q{2}) = 0) => // s0.
                * rewrite s0 /=.
                  pose x := head witness (qp SophosLeakage.h{1} w2).
                  rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
                  rewrite -filter_predI /predI -map_comp /(\o) /=.
                  rewrite maxnotthere //.
                    rewrite someidx -nth_head mem_nth // /=.
                * smt.
                rewrite get_set_neqE //.
          + have wq: w2 <> q{2} by move : H6; apply absurd => /= wq; rewrite mem_set wq //.
            move : H6; rewrite mem_set wq /= => w_dom.
            move : H7 (kw_sync w2) (kw_sync q{2}); rewrite 2!qp_cat size_cat /= w_dom H1 /=.
            rewrite -4!nth_head 2!nth_cat 2!nth_head.
            pose w := qp SophosLeakage.h{1} w2;
              pose q := qp SophosLeakage.h{1} q{2};
              pose sw := size w;
              pose sq := size q;
              pose hw := head witness w;
              pose hq := head witness q.
            rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
            rewrite -2!filter_predI /predI -2!map_comp /(\o) /=.
            rewrite (eq_sym _ w2) wq size_map /= => [sw_pos].
            rewrite sw_pos /=; move => [cw anyways] [cq] _.
            have someidx: forall w x, mem (qp SophosLeakage.h{1} w) x => mem (map fst SophosLeakage.h{1}) x.
              move => w'; rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
              rewrite -filter_predI /predI -map_comp /(\o) /= => x.
              rewrite mem_map_fst; move => [y].
              rewrite mem_filter /=; move => [_ inside].
              rewrite mem_map_fst; exists y => //.
            have maxnotthere: forall x, mem (map fst SophosLeakage.h{1}) x => x <> size SophosLeakage.h{1}.
              move => x; rewrite mem_size_nth size_map; move => [ss] [j] [jrng rwme]; rewrite -rwme.
              move : (timestamps j jrng); rewrite rwme => xj.
              move : (timestamps x); rewrite xj jrng /= => _.
              move : jrng => [_ jlt].
              rewrite neq_ltz jlt //.
            case (sq = 0) => //sq0.
            * rewrite sq0 /= mem_set cw /= maxnotthere //.
                rewrite (someidx w2) -nth_head mem_nth // /=.
            * have sq_pos: 0 < sq by rewrite ltz_def sq0 size_ge0 //.
              rewrite sq_pos mem_set cw /=. 
              have : mem q hq by rewrite -nth_head mem_nth sq_pos //.
              have : mem w hw by rewrite -nth_head mem_nth sw_pos //.
              rewrite /w => hwqp.
              move : (mem_qp_ap _ _ _ hwqp) => hwap.
              rewrite /q => hqqp.
              move : (mem_qp_ap _ _ _ hqqp) hwap.
              rewrite 2!mem_map_fst /hist.
              move => [eq]; rewrite mem_filter /=; move => [eq_def] hqmem.
              move => [ew]; rewrite mem_filter /=; move => [ew_def] hwmem.
              move : (indexed_all _ timestamps); rewrite allP => idx.
              move : (idx (hw, ew) hwmem) (idx (hq, eq) hqmem) => /= idxw idxq.
              have pwpq: (hw, ew) <> (hq, eq).
                move : eq_def ew_def.
                case (eq.`2 = None) => /= eq_u0.
                * move => eq_def.
                  case (ew.`2 = None) => /= ew_u0.
                  - (* both are history traces of previous search queries *)
                    move => ew_def.
                    rewrite /= andaE negb_and; right; smt.
                  - (* ew contains history traces of previous update query (while eq doesn't) *)
                    move => *; rewrite /= andaE negb_and; right; smt.
                * move => eq_def.
                  case (ew.`2 = None) => /= ew_u0.
                  - (* eq contains history traces of previous update query (while ew doesn't) *)
                    move => *; rewrite /= andaE negb_and; right; smt.
                  - (* both contain certainly update queries, therefore no search queries *)
                    move => ew_def.
                    move : (atomic_operations (hq, eq) hqmem) (atomic_operations (hw, ew) hwmem).
                    rewrite /oh_update /oh_query /oev_update /oev_query /h_event eq_u0 ew_u0 /= => eq_query_none ew_query_none.
                    rewrite andaE negb_and; right; smt.
              rewrite idxw idxq uniq_index; first by rewrite indexed_uniq //.
            smt.
          + move : H6; rewrite mem_set negb_or /=; move => [w_dom wq].
            move : (kw_sync q{2}); rewrite H1 /=; move => [s0 concl]; move : H7 (concl j0); rewrite size_cat /= addzC lez_add1r => pre; rewrite lez_eqVlt pre //= => notin.
            rewrite mem_set notin /=.
            have someidx: forall w x, mem (qp SophosLeakage.h{1} w) x => mem (map fst SophosLeakage.h{1}) x.
              move => w'; rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
              rewrite -filter_predI /predI -map_comp /(\o) /= => x.
              rewrite mem_map_fst; move => [y].
              rewrite mem_filter /=; move => [_ inside].
              rewrite mem_map_fst; exists y => //.
            have uptotimes: forall x, mem (map fst SophosLeakage.h{1}) x => x < size SophosLeakage.h{1}.
              move => x; rewrite mem_size_nth size_map; move => [ss] [j] [jrng rwme]; rewrite -rwme.
              move : (timestamps j jrng); rewrite rwme => xj.
              move : (timestamps x); rewrite xj jrng /= => _.
              move : jrng => [_ jlt].
              rewrite jlt //.
            rewrite qp_cat.
            pose w := qp SophosLeakage.h{1} q{2};
              pose sq := size w;
              pose hq := head witness w.
            case (0 < size w) => ss.
            * have hqmem: mem w hq by rewrite -nth_head mem_nth ss //.
              rewrite -nth_head nth_cat ss /= nth_head.
              rewrite neq_ltz; right.
              move : (uptotimes hq (someidx q{2} hq hqmem)).
              smt.
            * have sw0: size w = 0 by smt.
              rewrite -nth_head nth_cat ss sw0 /=.
              rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
              rewrite -filter_predI /predI -map_comp /(\o) /= /=.
              smt.
          + move : H7; rewrite mem_set -kw_ws_sync negb_or /=; move => [w_dom wq].
            move : H6 (kw_sync w2) (kw_sync q{2}); rewrite 2!qp_cat size_cat /= w_dom H1 /=.
            rewrite -4!nth_head 2!nth_cat 2!nth_head.
            pose w := qp SophosLeakage.h{1} w2;
              pose q := qp SophosLeakage.h{1} q{2};
              pose sw := size w;
              pose sq := size q;
              pose hw := head witness w;
              pose hq := head witness q.
            rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
            rewrite -2!filter_predI /predI -2!map_comp /(\o) /=.
            rewrite (eq_sym _ w2) wq size_map /= => [sw_pos].
            rewrite sw_pos /=; move => [cw anyways] [cq] _.
            have someidx: forall w x, mem (qp SophosLeakage.h{1} w) x => mem (map fst SophosLeakage.h{1}) x.
              move => w'; rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
              rewrite -filter_predI /predI -map_comp /(\o) /= => x.
              rewrite mem_map_fst; move => [y].
              rewrite mem_filter /=; move => [_ inside].
              rewrite mem_map_fst; exists y => //.
            have maxnotthere: forall x, mem (map fst SophosLeakage.h{1}) x => x <> size SophosLeakage.h{1}.
              move => x; rewrite mem_size_nth size_map; move => [ss] [j] [jrng rwme]; rewrite -rwme.
              move : (timestamps j jrng); rewrite rwme => xj.
              move : (timestamps x); rewrite xj jrng /= => _.
              move : jrng => [_ jlt].
              rewrite neq_ltz jlt //.
            case (sq = 0) => //sq0.
            * rewrite sq0 /= mem_set kw_wssim_sync cw /= maxnotthere //.
                rewrite (someidx w2) -nth_head mem_nth // /=.
            * have sq_pos: 0 < sq by rewrite ltz_def sq0 size_ge0 //.
              rewrite sq_pos mem_set kw_wssim_sync cw /=. 
              have : mem q hq by rewrite -nth_head mem_nth sq_pos //.
              have : mem w hw by rewrite -nth_head mem_nth sw_pos //.
              rewrite /w => hwqp.
              move : (mem_qp_ap _ _ _ hwqp) => hwap.
              rewrite /q => hqqp.
              move : (mem_qp_ap _ _ _ hqqp) hwap.
              rewrite 2!mem_map_fst /hist.
              move => [eq]; rewrite mem_filter /=; move => [eq_def] hqmem.
              move => [ew]; rewrite mem_filter /=; move => [ew_def] hwmem.
              move : (indexed_all _ timestamps); rewrite allP => idx.
              move : (idx (hw, ew) hwmem) (idx (hq, eq) hqmem) => /= idxw idxq.
              have pwpq: (hw, ew) <> (hq, eq).
                move : eq_def ew_def.
                case (eq.`2 = None) => /= eq_u0.
                * move => eq_def.
                  case (ew.`2 = None) => /= ew_u0.
                  - (* both are history traces of previous search queries *)
                    move => ew_def.
                    rewrite /= andaE negb_and; right; smt.
                  - (* ew contains history traces of previous update query (while eq doesn't) *)
                    move => *; rewrite /= andaE negb_and; right; smt.
                * move => eq_def.
                  case (ew.`2 = None) => /= ew_u0.
                  - (* eq contains history traces of previous update query (while ew doesn't) *)
                    move => *; rewrite /= andaE negb_and; right; smt.
                  - (* both contain certainly update queries, therefore no search queries *)
                    move => ew_def.
                    move : (atomic_operations (hq, eq) hqmem) (atomic_operations (hw, ew) hwmem).
                    rewrite /oh_update /oh_query /oev_update /oev_query /h_event eq_u0 ew_u0 /= => eq_query_none ew_query_none.
                    rewrite andaE negb_and; right; smt.
              rewrite idxw idxq uniq_index; first by rewrite indexed_uniq //.
              rewrite pwpq negb_or negb_and hwmem //.
          + move : H7; rewrite mem_set.
            case (w2 = q{2}) => //= wq.
            * rewrite wq 2!get_set_sameE //.
            * move : (H1); rewrite kw_ws_sync => q_dom_ws w_dom_ws; move : (wssim_ws_sync w2) (wssim_ws_sync q{2}); rewrite 2!w_dom_ws q_dom_ws /=.
              move : (w_dom_ws); rewrite -kw_ws_sync => w_dom.
              move : H6 (kw_sync w2) (kw_sync q{2}); rewrite 2!qp_cat size_cat /= 2!w_dom H1 /=.
              move => ss [aux1]; move : ss; rewrite aux1 /=.
            move : aux1; rewrite -4!nth_head 2!nth_cat 2!nth_head.
            pose w := qp SophosLeakage.h{1} w2;
              pose q := qp SophosLeakage.h{1} q{2};
              pose sw := size w;
              pose sq := size q;
              pose hw := head witness w;
              pose hq := head witness q.
            rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
            rewrite -filter_predI /predI -map_comp /(\o) /=.
            rewrite (eq_sym _ w2) wq size_map /= => [sw_pos].
            rewrite sw_pos /=; move => cw [_] anyways cq _.
            have someidx: forall w x, mem (qp SophosLeakage.h{1} w) x => mem (map fst SophosLeakage.h{1}) x.
              move => w'; rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
              rewrite -filter_predI /predI -map_comp /(\o) /= => x.
              rewrite mem_map_fst; move => [y].
              rewrite mem_filter /=; move => [_ inside].
              rewrite mem_map_fst; exists y => //.
            have maxnotthere: forall x, mem (map fst SophosLeakage.h{1}) x => x <> size SophosLeakage.h{1}.
              move => x; rewrite mem_size_nth size_map; move => [ss] [j] [jrng rwme]; rewrite -rwme.
              move : (timestamps j jrng); rewrite rwme => xj.
              move : (timestamps x); rewrite xj jrng /= => _.
              move : jrng => [_ jlt].
              rewrite neq_ltz jlt //.
            case (sq = 0) => //sq0.
            * rewrite sq0 /=. rewrite get_set_neqE. rewrite /= maxnotthere //.
                rewrite (someidx w2) -nth_head mem_nth // /=.
              rewrite get_set_neqE //.
            * smt.
          + smt.
          + smt.
          + smt.
          + move : (hash_backup w2 H6 i1); rewrite H7 H8 /=; move => [_] [_] [_] [concl] _.
            rewrite ahpU_cat filter_cat size_cat nth_cat (leakage_size w2 H6) H8 /=.
            rewrite (ltz_trans (size SophosLeakage.h{1})) //.
            rewrite -lez_add1r addzC lez_add2r //.
          + move : (hash_backup w2 H6 i1); rewrite H7 H8 /=; move => [_] [_] [_] [_] [rwme] _.
            rewrite rwme ahpU_cat filter_cat nth_cat (leakage_size w2 H6) H8 //.
          + move : (hash_backup w2 H6 i1); rewrite H7 H8 /=; move => [_] [_] [_] [_] [_ rwme].
            rewrite rwme ahpU_cat filter_cat nth_cat (leakage_size w2 H6) H8 //.
      seq 2 3: (={glob OracleCallsCounter}
            /\   (     SSIM.pk,       SSIM.sk,      SSIM.edb,       SSIM.t, size (SophosLeakage.h)){1}
               = (G4_Server.pk, G16_Client.sk, G4_Server.edb, G16_Client.t,           G16_Client.t){2}
            /\   (SSIM.keys.[w],    SSIM.wssim.[w]){1}
               = (     RF.m.[q], G16_Client.ws.[q]){2}
            /\ ={q, kw, s}
            /\ (q1 = q){2}
            /\ (addpat = filter (fun (x: int * operation * index) => x.`2 = ADD) (ahpU SophosLeakage.h q)){1}
            /\ (ul = oget G16_Client.uh.[q]){2}
            /\ (w = head witness (qp SophosLeakage.h q)){1}
            /\ (s = ((backward G16_Client.sk)^(size addpat{1} - 1)) (oget G16_Client.ws.[q])){2}
            /\ (0 < size (qp SophosLeakage.h{1} q)){2}
            /\ (dom G16_Client.uh q){2}
            /\ (dom G16_Client.ws q){2}
            /\ (forall i, 0 <= i < size addpat{1} =>
                  dom G16_Client.h1t (kw, ((backward G16_Client.sk)^i) (oget G16_Client.ws.[q]))
               /\ dom G16_Client.h2t (kw, ((backward G16_Client.sk)^i) (oget G16_Client.ws.[q]))
               ){2}

            /\ (validkeypair (SSIM.pk, SSIM.sk)){1}
            /\ (indexed SophosLeakage.h){1}
            /\ (forall x, mem SophosLeakage.h x => (oh_update x <> None <=> oh_query x = None)){1}
            /\ (forall w, dom G16_Client.uh{2} w <=>
                 filter (fun (z: int * operation * index), z.`2 = ADD) (ahpU SophosLeakage.h{1} w) <> []
               )
            /\ (forall w, dom G16_Client.uh w =>
                    size (filter (fun (z: int * operation * index), z.`2 = ADD) (ahpU SophosLeakage.h{1} w)) = size (oget G16_Client.uh.[w])
               ){2}
            /\ (forall w, dom RF.m w <=> dom G16_Client.ws w){2}
            /\ (forall k, dom SSIM.wssim k <=> dom SSIM.keys k){1}
            /\ (forall w,
                 let spat = (qp SophosLeakage.h{1} w) in
                 let wsim = head witness spat in
                    (dom RF.m w => 0 < size spat /\ SSIM.keys{1}.[wsim] = RF.m.[w])
                 /\ (!dom RF.m w => (0 < size spat => !dom SSIM.keys{1} wsim) /\ forall j, (size SophosLeakage.h{1}) <= j => !dom SSIM.keys{1} j)
               ){2}
            /\ (forall w,
                 let spat = (qp SophosLeakage.h{1} w) in
                 let wsim = head witness spat in
                    (0 < size spat /\ !dom G16_Client.ws w => !dom SSIM.wssim{1} wsim)
                 /\ (0 < size spat /\ dom G16_Client.ws w => SSIM.wssim{1}.[wsim] = G16_Client.ws.[w])
               ){2}
            /\ (forall w, dom G16_Client.uh w =>
                 let ap = filter (fun (z: int * operation * index), z.`2 = ADD) (ahpU SophosLeakage.h{1} w) in
                 let ul = oget G16_Client.uh.[w] in
                 forall i, 0 <= i < size ul =>
                   let apentry = (nth witness ap i) in
                   let j = apentry.`1 in
                   let ind = apentry.`3 in
                   let u = (nth witness ul i).`1 in
                       dom G16_Client.utt u
                    /\ dom G16_Client.et u
                    /\ u < size SophosLeakage.h{1}
                    /\ j < size SophosLeakage.h{1}
                    /\ G16_Client.utt.[u] = SSIM.utokens{1}.[j]
                    /\ G16_Client.et.[u] = Some (ind +^ (oget SSIM.idxs{1}.[j]))
               ){2}
            /\ (forall x, SSIM.h1t.[x]{1} = G16_Client.h1t.[x]{2})
            /\ (forall x, SSIM.h2t.[x]{1} = G16_Client.h2t.[x]{2})
        ).
      while ((0 <= i <= size addpat{1}){1}
            /\    (q,  q, i, kw, s){1}
                = (q, q1, i, kw, s){2}
            /\ ={glob OracleCallsCounter}
            /\   (     SSIM.pk,       SSIM.sk,      SSIM.edb,       SSIM.t, size (SophosLeakage.h)){1}
               = (G4_Server.pk, G16_Client.sk, G4_Server.edb, G16_Client.t,           G16_Client.t){2}
            /\ (addpat = filter (fun (x: int * operation * index) => x.`2 = ADD) (ahpU SophosLeakage.h q)){1}
            /\ (ul = oget G16_Client.uh.[q]){2}
            /\ (w = head witness (qp SophosLeakage.h q)){1}
            /\ (0 < i => s = ((backward G16_Client.sk)^(i - 1)) (oget G16_Client.ws.[q])){2}
            /\ (forall j, 0 <= j < i =>
                  dom G16_Client.h1t (kw, ((backward G16_Client.sk)^j) (oget G16_Client.ws.[q]))
               /\ dom G16_Client.h2t (kw, ((backward G16_Client.sk)^j) (oget G16_Client.ws.[q]))
               ){2}

            /\ (0 < size (qp SophosLeakage.h{1} q1)){2}
            /\ (dom G16_Client.uh q){2}
            /\ (dom G16_Client.ws q){2}
            /\ (validkeypair (SSIM.pk, SSIM.sk)){1}
            /\ (indexed SophosLeakage.h){1}
            /\ (forall x, mem SophosLeakage.h x => (oh_update x <> None <=> oh_query x = None)){1}
            /\ (forall w, dom G16_Client.uh{2} w <=>
                 filter (fun (z: int * operation * index), z.`2 = ADD) (ahpU SophosLeakage.h{1} w) <> []
               )
            /\ (forall w, dom G16_Client.uh w =>
                    size (filter (fun (z: int * operation * index), z.`2 = ADD) (ahpU SophosLeakage.h{1} w)) = size (oget G16_Client.uh.[w])
               ){2}
            /\ (forall w, dom RF.m w <=> dom G16_Client.ws w){2}
            /\ (forall k, dom SSIM.wssim k <=> dom SSIM.keys k){1}
            /\ (forall w,
                 let spat = (qp SophosLeakage.h{1} w) in
                 let wsim = head witness spat in
                    (dom RF.m w => 0 < size spat /\ SSIM.keys{1}.[wsim] = RF.m.[w])
                 /\ (!dom RF.m w => (0 < size spat => !dom SSIM.keys{1} wsim) /\ forall j, (size SophosLeakage.h{1}) <= j => !dom SSIM.keys{1} j)
               ){2}
            /\ (forall w,
                 let spat = (qp SophosLeakage.h{1} w) in
                 let wsim = head witness spat in
                    (0 < size spat /\ !dom G16_Client.ws w => !dom SSIM.wssim{1} wsim)
                 /\ (0 < size spat /\ dom G16_Client.ws w => SSIM.wssim{1}.[wsim] = G16_Client.ws.[w])
               ){2}
            /\ (forall w, dom G16_Client.uh w =>
                 let ap = filter (fun (z: int * operation * index), z.`2 = ADD) (ahpU SophosLeakage.h{1} w) in
                 let ul = oget G16_Client.uh.[w] in
                 forall i, 0 <= i < size ul =>
                   let apentry = (nth witness ap i) in
                   let j = apentry.`1 in
                   let ind = apentry.`3 in
                   let u = (nth witness ul i).`1 in
                       dom G16_Client.utt u
                    /\ dom G16_Client.et u
                    /\ u < size SophosLeakage.h{1}
                    /\ j < size SophosLeakage.h{1}
                    /\ G16_Client.utt.[u] = SSIM.utokens{1}.[j]
                    /\ G16_Client.et.[u] = Some (ind +^ (oget SSIM.idxs{1}.[j]))
               ){2}
            /\ (forall x, SSIM.h1t.[x]{1} = G16_Client.h1t.[x]{2})
            /\ (forall x, SSIM.h2t.[x]{1} = G16_Client.h2t.[x]{2})
        ).
        wp => /=; skip.
        move => &1 &2 [[[_ _] [[_] [_] [_ [_] _]]]] [_] [[_] [_] [_] [_] _] [addpat_def] [_] [w_def] [s_def]; subst.
        move => [hashes_prefilled] [sspat] [q_dom] [q_dom_ws] [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync] [saddpat] sul; subst; progress.
+ rewrite -addz0 lez_add1r //.
+ smt.
+ smt.
+ smt.
+ smt.
+ move : (wssim_ws_sync q{2}); rewrite sspat 2!q_dom_ws /=; move => rwme_idx.
  move : (hash_backup q{2} q_dom 0); rewrite sul /=; move => [_] [_] [_] [_] [rwme_yset] _.
  rewrite rwme_idx -rwme_yset //.
  pose x := (kw{2}, oget G16_Client.ws{2}.[q{2}]).
  move : (hash1_sync x2) => concl.
  case (x2 = x) => // x2x.
  * rewrite -x2x 2!get_set_sameE //.
  * rewrite get_set_neqE // get_set_neqE //.
+ move : (wssim_ws_sync q{2}); rewrite sspat 2!q_dom_ws /=; move => rwme_idx.
  move : (hash_backup q{2} q_dom 0); rewrite sul /=; move => [_] [_] [_] [_] [_ rwme_yset].
  rewrite rwme_idx rwme_yset oget_some //.
  pose x := (kw{2}, oget G16_Client.ws{2}.[q{2}]).
  move : (hash2_sync x2) => concl.
  case (x2 = x) => // x2x.
  * rewrite -x2x 2!get_set_sameE //.
  * rewrite get_set_neqE // get_set_neqE //.
+ smt.
+ smt.
+ smt.
+ smt.
+ move : s_def; have ->/=s_def: 0 < i{2} by rewrite ltz_def H /=; assumption.
  rewrite s_def -eq_sym fcompE H /=.
  pose x := oget G16_Client.ws{2}.[q{2}];
    pose b := backward G16_Client.sk{2}.
  rewrite -/b fcompC_ext //.
    rewrite -(lez_add2r 1) /= -addz0 lez_add1r ltz_def //.
+ smt.
+ smt.
+ move : s_def; have ->/=s_def: 0 < i{2} by rewrite ltz_def H /=; assumption.
  rewrite s_def.
  move : (hash_backup q{2} q_dom i{2}); rewrite sul /=.
  have ->/=: 0 <= i{2} by assumption.
  move => [_] [_] [_] [_] [rwme_yset] _.
  rewrite -rwme_yset //.
  pose b := backward G16_Client.sk{2}.
  rewrite -/b -fcompC_ext //.
    rewrite -(lez_add2r 1) /= -addz0 lez_add1r ltz_def //.
  move : (fcomp_proper (i{2} - 1) b).
  rewrite -(lez_add2r 1) /= -addz0 lez_add1r ltz_def H /=.
  have ->/=: 0 <= i{2} by assumption.
  rewrite eq_sym fun_ext /(\o) => rwme.
  rewrite rwme.
  move : (hash1_sync x2) => concl.
  pose s := oget G16_Client.ws{2}.[q{2}];
    pose x := (kw{2}, (b^i{2}) s).
  rewrite -/s.
  case (x2 = x) => // x2x.
  * rewrite -x2x 2!get_set_sameE //.
  * rewrite get_set_neqE // get_set_neqE //.
+ move : s_def; have ->/=s_def: 0 < i{2} by rewrite ltz_def H /=; assumption.
  rewrite s_def.
  move : (hash_backup q{2} q_dom i{2}); rewrite sul /=.
  have ->/=: 0 <= i{2} by assumption.
  move => [_] [_] [_] [_] [_ rwme_yset].
  rewrite rwme_yset //.
  pose b := backward G16_Client.sk{2}.
  rewrite -/b -fcompC_ext //.
    rewrite -(lez_add2r 1) /= -addz0 lez_add1r ltz_def //.
  move : (fcomp_proper (i{2} - 1) b).
  rewrite -(lez_add2r 1) /= -addz0 lez_add1r ltz_def H /=.
  have ->/=: 0 <= i{2} by assumption.
  rewrite eq_sym fun_ext /(\o) => rwme.
  rewrite rwme.
  move : (hash2_sync x2) => concl.
  pose s := oget G16_Client.ws{2}.[q{2}];
    pose x := (kw{2}, (b^i{2}) s).
  rewrite -/s.
  case (x2 = x) => // x2x.
  * rewrite -x2x 2!get_set_sameE //.
  * rewrite get_set_neqE // get_set_neqE //.
+ smt.
+ smt.
(* end of while *)
wp => /=; skip.
move => &1 &2 [_] [[_] [_] [_] [_] _] [[_ _]] [[_] [_] _] [_] [_] [w_def] [saddpat] [q_dom] [q_dom_ws]; subst.
          move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress.
+ rewrite size_ge0.
+ move : H H0; rewrite andWI -andaE lez_lt_asym //.
+ move : H H0; rewrite andWI -andaE lez_lt_asym //.
+ rewrite -(leakage_size q{2} q_dom) //.
+ rewrite (leakage_size q{2} q_dom) //.
+ smt.
+ smt.
+ smt.
      wp => //.

      while ((0 <= i0 <= c0 + 1){2}
            /\    (q,  q,  i, kw, kw, rl, size addpat, z){1}
                = (q, q1, i0, kw0, kw, r1,     c0 + 1, t){2}
            /\ ={glob OracleCallsCounter}
            /\   (     SSIM.pk,       SSIM.sk,      SSIM.edb,       SSIM.t, size (SophosLeakage.h)){1}
               = (G4_Server.pk, G16_Client.sk, G4_Server.edb, G16_Client.t,           G16_Client.t){2}
            /\ (q1 = q){2}
            /\ (addpat = filter (fun (x: int * operation * index) => x.`2 = ADD) (ahpU SophosLeakage.h q)){1}
            /\ (ul = oget G16_Client.uh.[q]){2}
            /\ (w = head witness (qp SophosLeakage.h q)){1}
            /\ (s = ((backward G16_Client.sk)^(size addpat{1} - 1)) (oget G16_Client.ws.[q])){2}
            /\ (0 <= i0 < size addpat{1} => t = ((backward G16_Client.sk)^(size addpat{1} - i0 - 1)) (oget G16_Client.ws.[q1]) ){2}
            /\ (i0 = size addpat{1} => t = forward G4_Server.pk (oget G16_Client.ws.[q1]) ){2}
            /\ (forall i, 0 <= i < size addpat{1} =>
                  dom G16_Client.h1t (kw0, ((backward G16_Client.sk)^i) (oget G16_Client.ws.[q1]))
               /\ dom G16_Client.h2t (kw0, ((backward G16_Client.sk)^i) (oget G16_Client.ws.[q1]))
               ){2}

            /\ (0 < size (qp SophosLeakage.h{1} q1)){2}
            /\ (dom G16_Client.uh q){2}
            /\ (dom G16_Client.ws q){2}
            /\ (validkeypair (SSIM.pk, SSIM.sk)){1}
            /\ (indexed SophosLeakage.h){1}
            /\ (forall x, mem SophosLeakage.h x => (oh_update x <> None <=> oh_query x = None)){1}
            /\ (forall w, dom G16_Client.uh{2} w <=>
                 filter (fun (z: int * operation * index), z.`2 = ADD) (ahpU SophosLeakage.h{1} w) <> []
               )
            /\ (forall w, dom G16_Client.uh w =>
                    size (filter (fun (z: int * operation * index), z.`2 = ADD) (ahpU SophosLeakage.h{1} w)) = size (oget G16_Client.uh.[w])
               ){2}
            /\ (forall w, dom RF.m w <=> dom G16_Client.ws w){2}
            /\ (forall k, dom SSIM.wssim k <=> dom SSIM.keys k){1}
            /\ (forall w,
                 let spat = (qp SophosLeakage.h{1} w) in
                 let wsim = head witness spat in
                    (dom RF.m w => 0 < size spat /\ SSIM.keys{1}.[wsim] = RF.m.[w])
                 /\ (!dom RF.m w => (0 < size spat => !dom SSIM.keys{1} wsim) /\ forall j, (size SophosLeakage.h{1}) <= j => !dom SSIM.keys{1} j)
               ){2}
            /\ (forall w,
                 let spat = (qp SophosLeakage.h{1} w) in
                 let wsim = head witness spat in
                    (0 < size spat /\ !dom G16_Client.ws w => !dom SSIM.wssim{1} wsim)
                 /\ (0 < size spat /\ dom G16_Client.ws w => SSIM.wssim{1}.[wsim] = G16_Client.ws.[w])
               ){2}
            /\ (forall w, dom G16_Client.uh w =>
                 let ap = filter (fun (z: int * operation * index), z.`2 = ADD) (ahpU SophosLeakage.h{1} w) in
                 let ul = oget G16_Client.uh.[w] in
                 forall i, 0 <= i < size ul =>
                   let apentry = (nth witness ap i) in
                   let j = apentry.`1 in
                   let ind = apentry.`3 in
                   let u = (nth witness ul i).`1 in
                       dom G16_Client.utt u
                    /\ dom G16_Client.et u
                    /\ u < size SophosLeakage.h{1}
                    /\ j < size SophosLeakage.h{1}
                    /\ G16_Client.utt.[u] = SSIM.utokens{1}.[j]
                    /\ G16_Client.et.[u] = Some (ind +^ (oget SSIM.idxs{1}.[j]))
               ){2}
            /\ (forall x, SSIM.h1t.[x]{1} = G16_Client.h1t.[x]{2})
            /\ (forall x, SSIM.h2t.[x]{1} = G16_Client.h2t.[x]{2})
        ).
        rcondf{2} 3; progress.
          wp; skip; move => &hr [[[_ _] [[_] [_] [_ [_] [_] [_] [_] _]]]] [_] [[_] [_] [_] [_] _] [_] [_] [ul_def] [w_def] [s_def] [t_def] [t_max]; subst.
          move => [hashes_prefilled] [sspat] [q_dom] [q_dom_ws] [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync ] [_] _; subst; progress.
pose addpat := (filter (fun (x: int * operation * index) => x.`2 = ADD) (ahpU SophosLeakage.h{m0} q)){hr}.
move : (hashes_prefilled (size addpat - i0{hr} - 1)) (t_def).
have ->/=: 0 <= i0{hr} < size addpat by smt.
have ->/=: 0 <= size addpat - i0{hr} - 1 < size addpat by smt.
move => [concl _] rwme; rewrite rwme; exact concl.
        rcondf{2} 6; progress.
          wp; skip; move => &hr [[[_ _] [[_] [_] [_ [_] [_] [_] [_] _]]]] [_] [[_] [_] [_] [_] _] [_] [_] [ul_def] [w_def] [s_def] [t_def] [t_max]; subst.
          move => [hashes_prefilled] [sspat] [q_dom] [q_dom_ws] [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync ] [_] _; subst; progress.
pose addpat := (filter (fun (x: int * operation * index) => x.`2 = ADD) (ahpU SophosLeakage.h{m0} q)){hr}.
move : (hashes_prefilled (size addpat - i0{hr} - 1)) (t_def).
have ->/=: 0 <= i0{hr} < size addpat by smt.
have ->/=: 0 <= size addpat - i0{hr} - 1 < size addpat by smt.
move => [_ concl] rwme; rewrite rwme; exact concl.
wp; skip; move => &1 &2 [[[_ _] [[_] [_] [_ [_] [_] [_] [_] _]]]] [_] [[_] [_] [_] [_] _] [_] [_] [ul_def] [w_def] [s_def] [t_def] [t_max]; subst.
          move => [hashes_prefilled] [sspat] [q_dom] [q_dom_ws] [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync ] [_] _; subst; progress.
+ smt.
+ smt.
+ smt.
+ rewrite IntID.opprD addzA /= fcompE.
  move : t_def.
  pose addpat := filter (fun (x: int * operation * index) => x.`2 = ADD) (ahpU SophosLeakage.h{1} q{2}).
  have ->/=: 0 <= i0{2} < size addpat by smt.
            pose b := backward G16_Client.sk{2};
              pose f := forward G4_Server.pk{2};
              pose t := (oget G16_Client.ws{2}.[q{2}]).
            rewrite -/b. (* pose b does not rewrite all of them for some reason... *)
            have inj_f: injective f by move : (valk_can_fb (G4_Server.pk, G16_Client.sk){2} valid_keypair); apply (can_inj f b).
            move : (inj_f); rewrite TP.TrapdoorDomain.PermutationDomain.enumD_inj_uniq_isomap -TP.TrapdoorDomain.PermutationDomain.enumD_bij_uniq_isomap => bij_f.
            move : (valk_can_fb (G4_Server.pk, G16_Client.sk){2} valid_keypair); rewrite -/f -/b => can_fb.
            have can_bf: forall x, f (b x) = x by apply (bij_can_sym f b) => //.
  case (size addpat - i0{2} - 2 = 0) => i0val.
  * have ->/=t_def: size addpat - i0{2} - 1 = 1 by smt.
    rewrite t_def fcomp1 /= can_bf //.
  * move => t_def.
    rewrite t_def 2!fcompE i0val.
    have ->/=: size addpat - i0{2} - 1 <> 0 by smt.
    rewrite (fcompC_ext _ _ (b t)); first by smt.
    rewrite can_bf //.
+ move : t_def.
  pose addpat := filter (fun (x: int * operation * index) => x.`2 = ADD) (ahpU SophosLeakage.h{1} q{2}).
  have ->/=t_def: 0 <= i0{2} < size addpat by smt.
  rewrite t_def.
  have ->/=: size addpat - i0{2} - 1 = 0 by smt.
  rewrite fcomp0 /idfun //.
+ smt.
+ smt.
(* end of while *)
  wp => /=; skip.
  move => &1 &2 [_] [[_] [_] [_] [_] _] [[_ _]] [[_] [_] _] [_] [_] [addpat_def] [ul_def] [w_def] [saddpat] [q_dom] [q_dom_ws]; subst.
  move => [hashes_prefilled] [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress.
+ rewrite oget_some /= size_ge0.
+ rewrite oget_some /=; smt.
+ rewrite oget_some /=; smt.
+ rewrite oget_some /=; smt.
+ rewrite oget_some /=; smt.
+ rewrite oget_some /=; smt.
+ smt.
+ smt.
  + (* Queried term was never added in the first place *)
    rcondt{2} 3; progress; first by wp; skip; progress.
    rcondf{1} 8; progress.
      wp; skip; move => /= &hr [[[_] [_] [_] [_] [[_ _]]]]; subst.
      move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync] PPTA q_dom; subst; progress.
      move : (leakage q{m0}); rewrite q_dom /=.
      rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
      rewrite 2!filter_cat 2!map_cat filter_cat /= /= cats0 //.
    rcondt{2} 6; progress; first by wp; skip; progress.
    wp; skip; move => &1 &2 [[[_ [_] [_] [_ [[_] [_] [_] [_] _]]]]]; subst.
    move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress.
+ rewrite size_cat //.
+ rewrite cats1 indexed_rcons //.
      + move : H1 (atomic_operations x2); rewrite mem_cat /=.
        case (mem SophosLeakage.h{1} x2) => //= xmem.
        move => rwme; rewrite -rwme //.
      + move : H1 (atomic_operations x2); rewrite mem_cat /=.
        case (mem SophosLeakage.h{1} x2) => //= xmem.
        move => rwme; rewrite rwme //.
+ have wq: w2 <> q{2} by move : H1; apply absurd => /= wq; rewrite wq H0 //.
  move : (leakage w2); rewrite H1 /= /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
            rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) /=.
  rewrite (eq_sym _ w2) wq /= cats0 //.
+ case (w2 = q{2}) => //= wq.
  * move : H1; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
            rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) /=.
    rewrite wq /= /= cats0 leakage /ahpU /projUpdates /hist 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) //.
  * move : H1; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
            rewrite 2!filter_cat 2!map_cat filter_cat 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) /= /= /= 2!filter_map /preim -filter_predI /predI /= -map_comp /(\o) /=.
    rewrite (eq_sym _ w2) wq /= cats0 //.
    rewrite leakage /ahpU /projUpdates /hist 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) //.
+ have wq: w2 <> q{2} by move : H1; apply absurd => /= wq; rewrite wq H0 //.
  rewrite ahpU_cat filter_cat size_cat -(leakage_size _ H1).
  rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
            rewrite 2!filter_map /preim -2!filter_predI /predI /= -map_comp /(\o) //.
  rewrite (eq_sym _ w2) wq /= //.
+ rewrite qp_cat size_cat /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
            rewrite -2!filter_predI /predI -2!map_comp /(\o) /= /=.
  case (w2 = q{2}) => //= wq.
  * rewrite wq /= -lez_add1r addzC lez_add2r size_ge0 //.
  * rewrite (eq_sym _ w2) wq /= //.
    move : (kw_sync w2); rewrite 2! H1 /= /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
            rewrite -filter_predI /predI -map_comp /(\o) /= /=; move => [concl] _.
    exact concl.
+ move : (kw_sync w2); rewrite 2! H1 /=; move => [aux] concl.
  rewrite qp_cat head_cat //.
    rewrite -size_eq0 eq_sym neq_ltz; left; assumption.
+ move : (kw_sync w2) H2; rewrite H1 /=; move => [aux] c.
  rewrite qp_cat size_cat -nth_head nth_cat nth_head /=.
            pose w := qp SophosLeakage.h{1} w2;
              pose sw := size w;
              pose hw := head witness w.
case (sw = 0) => //= sw0.
* rewrite sw0 /=.
  rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
  rewrite -filter_predI /predI -map_comp /(\o) /=.
  case (w2 = q{2}) => //= wq.
  - rewrite wq /= /= (c (size SophosLeakage.h{1})) //.
  - rewrite (eq_sym _ w2) wq /= //.
* have sw_pos: 0 < sw by rewrite ltz_def sw0 size_ge0 //.
  rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
  rewrite -filter_predI /predI -map_comp /(\o) /=.
  move : aux; rewrite sw_pos /= => aux.
  rewrite aux //.
+ move : (kw_sync w2) H2; rewrite H1 /=; move => [_] c.
  rewrite size_cat /= addzC lez_add1r => pre.
  move : (c j0); rewrite lez_eqVlt pre //.
+ move : (H2); rewrite -kw_ws_sync => w_dom.
  move : (kw_sync w2) (wssim_ws_sync w2) H1; rewrite w_dom H2 /=.
  rewrite qp_cat size_cat -2!nth_head nth_cat nth_head /=.
            pose w := qp SophosLeakage.h{1} w2;
              pose sw := size w;
              pose hw := head witness w.
  move => [_ c] aux.
case (sw = 0) => //= sw0.
* rewrite sw0 /=.
  rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
  rewrite -filter_predI /predI -map_comp /(\o) /=.
  case (w2 = q{2}) => //= wq.
  - rewrite wq /= /= kw_wssim_sync (c (size SophosLeakage.h{1})) //.
  - rewrite (eq_sym _ w2) wq /= //.
* have sw_pos: 0 < sw by rewrite ltz_def sw0 size_ge0 //.
  rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query.
  rewrite -filter_predI /predI -map_comp /(\o) /=.
  move : aux; rewrite sw_pos /= => aux.
  rewrite aux //.
+ move : (H2); rewrite -kw_ws_sync => w_dom.
  move : (kw_sync w2) (wssim_ws_sync w2) H1; rewrite 2!w_dom 2!H2 /=.
  rewrite qp_cat size_cat -2!nth_head nth_cat nth_head /=.
            pose w := qp SophosLeakage.h{1} w2;
              pose sw := size w;
              pose hw := head witness w.
  move => [aux1]; rewrite aux1 /=.
  move => _ concl.
  rewrite concl //.
+ smt.
+ smt.
+ smt.
+ have wq: w2 <> q{2} by move : H1; apply absurd => /= wq; rewrite wq H0 //.
  move : (hash_backup w2 H1 i1); rewrite H2 H3 /=; move => [_] [_] [_] [concl] _.
  move : concl.
  rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
            rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /=.
  rewrite size_cat filter_cat cats0 /=.
  smt.
+ have wq: w2 <> q{2} by move : H1; apply absurd => /= wq; rewrite wq H0 //.
  move : (hash_backup w2 H1 i1); rewrite H2 H3 /=; move => [_] [_] [_] [_] [concl] _.
  move : concl.
  rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
            rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /=.
  rewrite filter_cat cats0 /=.
  smt.
+ have wq: w2 <> q{2} by move : H1; apply absurd => /= wq; rewrite wq H0 //.
  move : (hash_backup w2 H1 i1); rewrite H2 H3 /=; move => [_] [_] [_] [_] [_ concl].
  move : concl.
  rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query.
            rewrite 4!filter_map /preim -4!filter_predI /predI /= -2!map_comp /(\o) /= /=.
  rewrite filter_cat cats0 /=.
  smt.
  + (* o *)
    proc.
    sp; if => //.
    inline*; wp => /=.
    sp; if => //.
    * (* HASH1 *)
      sp; if.
      - (* condition *)
        move => &1 &2 [_] [_] [[inputs] [_] [_] [_]] [[_] [_]] [_] [_] [[_] [_] [_] [_] _]; subst.
        move : inputs; rewrite pairS /=; move => [_] [_] _; subst.
        move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress.
        + move : (hash1_sync (hi{1}, s{1})) H0 => rwme; rewrite 2!domE rwme //.
        + move : (hash1_sync (hi{1}, s{1})) H0 => rwme; rewrite 2!domE rwme //.
      - (* then *) wp; rnd; skip.
        move => &1 &2 [[_] [_] [[inputs] [_] [_] [_]] [[_] [_]] [_] [_] [[_] [_] [_] [_] _]]; subst.
        move : inputs; rewrite pairS /=; move => [_] [_] _; subst.
        move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress.
        + rewrite 2!get_set_sameE //.
        + case (x0 = (hi{1}, s{1})) => //= x0his.
          * rewrite x0his 2!get_set_sameE //.
          * rewrite get_set_neqE // get_set_neqE //.
            apply hash1_sync.
      - (* else *) wp; skip.
        move => &1 &2 [[_] [_] [[inputs] [_] [_] [_]] [[_] [_]] [_] [_] [[_] [_] [_] [_] _]]; subst.
        move : inputs; rewrite pairS /=; move => [_] [_] _; subst.
        move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress.
        rewrite (hash1_sync (hi{1}, s{1})) //.
    * (* NOT HASH1 *)
      if => //.
      (* HASH2 *)
      sp; if.
      - (* condition *)
        move => &1 &2 [_] [_] [[[inputs] [_] [_] [_]] [[_] [_]] [_] [_] [[_] [_] [_] [_] _]]; subst.
        move : inputs; rewrite pairS /=; move => [_] [_] _; subst.
        move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress.
        + move : (hash2_sync (hi0{1}, s0{1})) H1 => rwme; rewrite 2!domE rwme //.
        + move : (hash2_sync (hi0{1}, s0{1})) H1 => rwme; rewrite 2!domE rwme //.
      - (* then *) wp; rnd; skip.
        move => &1 &2 [[_] [_] [[[inputs] [_] [_] [_]] [[_] [_]] [_] [_] [[_] [_] [_] [_] _]]]; subst.
        move : inputs; rewrite pairS /=; move => [_] [_] _; subst.
        move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress.
        + rewrite 2!get_set_sameE //.
        + case (x0 = (hi0{1}, s0{1})) => //= x0his.
          * rewrite x0his 2!get_set_sameE //.
          * rewrite get_set_neqE // get_set_neqE //.
            apply hash2_sync.
      - (* else *) wp; skip.
        move => &1 &2 [[_] [_] [[[inputs] [_] [_] [_]] [[_] [_]] [_] [_] [[_] [_] [_] [_] _]]]; subst.
        move : inputs; rewrite pairS /=; move => [_] [_] _; subst.
        move => [valid_keypair] [timestamps] [atomic_operations] [leakage] [leakage_size] [kw_ws_sync] [kw_wssim_sync] [kw_sync] [wssim_ws_sync] [hash_backup] [hash1_sync hash2_sync]; subst; progress.
        rewrite (hash2_sync (hi0{1}, s0{1})) //.
  + (* Invariant before the distinguisher call *)
    wp; rnd; wp; skip; move => &1 &2 /= [[_] _ _ r _]; subst; progress; expect 21.
    - rewrite  /validkeypair /(\o) /index /= //.
    - rewrite /indexed /= => i; rewrite lez_lt_asym //.
    - move : H0; rewrite mem_empty //.
    - move : H0; rewrite /ahpU /projUpdates /hist /hup_time /hup_event /eup_operation /eup_index /h_time /h_storage /h_update /oh_update /up_query /oh_query /eup_input /ev_storage /h_event /ev_update /oev_update /oev_query //.
    - move : H0; rewrite mem_empty //.
    - move : H0; rewrite mem_empty //.
    - move : H0; rewrite mem_empty //.
    - move : H0; rewrite mem_empty //.
    - move : H0; rewrite mem_empty //.
    - move : H0; rewrite mem_empty //.
    - move : H0; rewrite mem_empty //.
    - move : H1; rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query //.
    - rewrite mem_empty //.
    - move : H0; rewrite /qp /projQueries /hist /hq_time /h_time /h_storage /h_query /oh_query /oh_update /h_update /up_query /h_event /ev_storage /ev_query /oev_query /oev_update /ev_update /oev_query //.
    - move : H1; rewrite mem_empty //.
    - move : H0; rewrite mem_empty //.
    - move : H0; rewrite mem_empty //.
    - move : H0; rewrite mem_empty //.
    - move : H0; rewrite mem_empty //.
    - move : H0; rewrite mem_empty //.
    - move : H0; rewrite mem_empty //.
qed.

  (* LAdaptive Forward Secrecy *)
  lemma sseladaptive_security_sophos_advantage (F<: PRF{Sophos,OracleCallsCounter}) (H1<: HashFunction1{OracleCallsCounter}) (H2<: HashFunction2{OracleCallsCounter})
    (D<: SSEDistROM{Sophos,SSIM,SophosLeakage,F,H1,H2})
  &m:
    is_lossless dcoins =>
    islossless F.keygen =>
    islossless F.f =>
    islossless H1.hash =>
    islossless H2.hash =>
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(OracleCallsCounter(D, SA).SSEAccessBounder).distinguish) =>
    ct TP.index sample forward backward => (* collection of trapdoor permutation *)
    2%r * Pr[SSELAdaptiveSecurityROM(Sophos(F, H1, H2), SSIM, SophosLeakage, OracleCallsCounter(D)).main() @ &m : res] - 1%r =
    Pr[Dsse(OracleCallsCounter(D), Sophos(F, H1, H2)).distinguish() @ &m : res] - Pr[Dsim(OracleCallsCounter(D), SSIM, SophosLeakage).distinguish() @ &m : res].
  proof.
    move => dcoins_ll keygen_ll f_ll h1_ll h2_ll PPTA_DBound ct_pre; move : (ct_pre).
    rewrite /ct /validkeypair /(-<) /cancel forall_and /=.
    move => [_ valk_can_fb].
    rewrite (sseladaptiveexprom_advantage (Sophos(F, H1, H2)) SophosLeakage SSIM (OracleCallsCounter(D)) &m) //.
    + rewrite (sophos_setup_ll F H1 H2) //.
    + rewrite leaksetup_ll //.
    + rewrite (sim_setup_ll CTP) //.
    + rewrite ctp_index_ll //.
    + rewrite (occ_distinguish_ll D (Sophos(F, H1, H2))) (PPTA_DBound (Sophos(F, H1, H2))) //.
      rewrite (sophos_update_ll F H1 H2 f_ll h1_ll h2_ll).
      rewrite (sophos_query_ll F H1 H2 f_ll h1_ll h2_ll).
      rewrite (sophos_o_ll F H1 H2 h1_ll h2_ll).
    + rewrite (occ_distinguish_ll D (SSESimulatorWrapper(SSIM, SophosLeakage))) (PPTA_DBound (SSESimulatorWrapper(SSIM, SophosLeakage))) //.
      - proc; call (sim_update_ll CTP); call (leakupdate_ll) => //.
      - proc; call (sim_query_ll CTP ctp_forward_ll ctp_backward_ll); call (leakquery_ll) => //.
      - proc*; call (sim_o_ll CTP) => //.
    rewrite (sseladaptiveexprom_dsse (Sophos(F, H1, H2)) SophosLeakage SSIM (OracleCallsCounter(D)) &m).
    rewrite (sseladaptiveexprom_dsim (Sophos(F, H1, H2)) SophosLeakage SSIM (OracleCallsCounter(D)) &m) //.
  qed.

  lemma sseladaptive_security_sophos
    (F <: PRF{RKF,OracleCallsCounter,RO1,Sophos,G1,SH1_Red,PRFO1.PRFO1,PRFO2.PRFO2,SP_Red})
    (H1<: HashFunction1{RKF,OracleCallsCounter,RO1,Sophos,G1,G2,SH1_Red,PRFO1.PRFO1,PRFO2.PRFO2,SP_Red,F})
    (H2<: HashFunction2{RKF,OracleCallsCounter,RO1,RO2,Sophos,G1,G2,G3,SH1_Red,PRFO1.PRFO1,PRFO2.PRFO2,SP_Red,F,H1,SH2_Red})
    (D <: SSEDistROM{Sophos,SSIM,SophosLeakage,F,H1,H2,RKF,OracleCallsCounter,RO1,RO2,G1,G2,G3,G4,G5,G6,G7,G8,G9,G10,G11,G12,G13,G14,G15,G16,SH1_Red,PRFO1.PRFO1,PRFO2.PRFO2,SP_Red,SH2_Red,RF})
  &m:
    is_lossless dcoins =>
    islossless F.keygen =>
    islossless F.f =>
    islossless H1.hash =>
    islossless H2.hash =>
    RKF.m{m} = empty =>
    (RO1.m, RO2.m){m} = (empty, empty) =>
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(SA).distinguish) =>
    (forall (SA <: SSEAccess{D}), islossless SA.update => islossless SA.query => islossless SA.o => islossless D(OracleCallsCounter(D, SA).SSEAccessBounder).distinguish) =>
    ct TP.index sample forward backward => (* collection of trapdoor permutation *)
       2%r * Pr[SSELAdaptiveSecurityROM(Sophos(F, H1, H2), SSIM, SophosLeakage, OracleCallsCounter(D)).main() @ &m : res] - 1%r
    <= (2%r * Pr[PRFExp(F, RKF, SP_Red(H1, H2, OracleCallsCounter(D))).main() @ &m : res] - 1%r)
    +  (2%r * Pr[HashExp1(H1, HashRO1, SH1_Red(H2, OracleCallsCounter(D))).main() @ &m : res] - 1%r)
    +  (2%r * Pr[HashExp2(H2, HashRO2, SH2_Red(OracleCallsCounter(D))).main() @ &m : res] - 1%r)
    +  Pr[Dsse(OracleCallsCounter(D),  G5).distinguish() @ &m : G5_Client.bad_rf_coll]
    +  Pr[Dsse(OracleCallsCounter(D),  G5).distinguish() @ &m : G5_Client.bad_update_h1t]
    +  Pr[Dsse(OracleCallsCounter(D),  G5).distinguish() @ &m : G5_Client.bad_update_h2t]
    +  Pr[Dsse(OracleCallsCounter(D),  G5).distinguish() @ &m : G5_Client.bad_update_bt]
    +  Pr[Dsse(OracleCallsCounter(D),  G5).distinguish() @ &m : G5_Client.bad_h1]
    +  Pr[Dsse(OracleCallsCounter(D),  G5).distinguish() @ &m : G5_Client.bad_h2]
    +  Pr[Dsse(OracleCallsCounter(D), G10).distinguish() @ &m : G10_Client.bad_rf_coll]
    +  Pr[Dsse(OracleCallsCounter(D),  G9).distinguish() @ &m : G9_Client.bad_update_h1t]
    +  Pr[Dsse(OracleCallsCounter(D),  G8).distinguish() @ &m : G8_Client.bad_update_h2t]
    +  Pr[Dsse(OracleCallsCounter(D),  G7).distinguish() @ &m : G7_Client.bad_update_bt]
    +  Pr[Dsse(OracleCallsCounter(D),  G6).distinguish() @ &m : G6_Client.bad_h1]
    +  Pr[Dsse(OracleCallsCounter(D),  G5).distinguish() @ &m : G5_Client.bad_h2]
    .
  proof.
    move => dcoins_ll keygen_ll f_ll h1_ll h2_ll rkf_0 ro12_0 PPTA_D PPTA_DBound ct_pre; move : (ct_pre).
    rewrite /ct /validkeypair /(-<) /cancel forall_and /=.
    move => [_ valk_can_fb].
    (* Rewrite games with D notation *)
    have eq2adv: forall p q, p = q <=> 2%r*p - 1%r = 2%r*q - 1%r by smt.
    have ltr_add2l: forall (n p q: real), n + p <= n + q <=> p <= q by smt.
    have ler_subl: forall (p q n: real), p - q <= n <=> p <= q + n by smt.
    have eqr_subl: forall (p q n: real), p - q = n <=> p = q + n by smt.
    have compose: forall (a b p q: real), a <= b => p <= q => a + p <= b + q by smt.
    pose DS := Pr[Dsim(OracleCallsCounter(D), SSIM, SophosLeakage).distinguish() @ &m : res];
      pose D16 := Pr[Dsse(OracleCallsCounter(D), G16).distinguish() @ &m : res];
      pose D15 := Pr[Dsse(OracleCallsCounter(D), G15).distinguish() @ &m : res];
      pose D14 := Pr[Dsse(OracleCallsCounter(D), G14).distinguish() @ &m : res];
      pose D13 := Pr[Dsse(OracleCallsCounter(D), G13).distinguish() @ &m : res];
      pose D12 := Pr[Dsse(OracleCallsCounter(D), G12).distinguish() @ &m : res];
      pose D11 := Pr[Dsse(OracleCallsCounter(D), G11).distinguish() @ &m : res];
      pose D10 := Pr[Dsse(OracleCallsCounter(D), G10).distinguish() @ &m : res];
      pose D10_bad_rf_coll := Pr[Dsse(OracleCallsCounter(D), G10).distinguish() @ &m : G10_Client.bad_rf_coll];
      pose D9 := Pr[Dsse(OracleCallsCounter(D), G9).distinguish() @ &m : res];
      pose D9_bad_update_h1t := Pr[Dsse(OracleCallsCounter(D), G9).distinguish() @ &m : G9_Client.bad_update_h1t];
      pose D8 := Pr[Dsse(OracleCallsCounter(D), G8).distinguish() @ &m : res];
      pose D8_bad_update_h2t := Pr[Dsse(OracleCallsCounter(D), G8).distinguish() @ &m : G8_Client.bad_update_h2t];
      pose D7 := Pr[Dsse(OracleCallsCounter(D), G7).distinguish() @ &m : res];
      pose D7_bad_update_bt := Pr[Dsse(OracleCallsCounter(D), G7).distinguish() @ &m : G7_Client.bad_update_bt];
      pose D6 := Pr[Dsse(OracleCallsCounter(D), G6).distinguish() @ &m : res];
      pose D6_bad_h1 := Pr[Dsse(OracleCallsCounter(D), G6).distinguish() @ &m : G6_Client.bad_h1];
      pose D5 := Pr[Dsse(OracleCallsCounter(D), G5).distinguish() @ &m : res];
      pose D5_bad_h2 := Pr[Dsse(OracleCallsCounter(D), G5).distinguish() @ &m : G5_Client.bad_h2];
      pose D5_bad_h1 := Pr[Dsse(OracleCallsCounter(D), G5).distinguish() @ &m : G5_Client.bad_h1];
      pose D5_bad_update_bt := Pr[Dsse(OracleCallsCounter(D), G5).distinguish() @ &m : G5_Client.bad_update_bt];
      pose D5_bad_update_h2t := Pr[Dsse(OracleCallsCounter(D), G5).distinguish() @ &m : G5_Client.bad_update_h2t];
      pose D5_bad_update_h1t := Pr[Dsse(OracleCallsCounter(D), G5).distinguish() @ &m : G5_Client.bad_update_h1t];
      pose D5_bad_rf_coll := Pr[Dsse(OracleCallsCounter(D), G5).distinguish() @ &m : G5_Client.bad_rf_coll];
      pose D5_bad := D5_bad_rf_coll + D5_bad_update_h1t + D5_bad_update_h2t + D5_bad_update_bt + D5_bad_h1 + D5_bad_h2;
      pose D4 := Pr[Dsse(OracleCallsCounter(D), G4).distinguish() @ &m : res];
      pose D3 := Pr[Dsse(OracleCallsCounter(D), G3).distinguish() @ &m : res];
      pose D2 := Pr[Dsse(OracleCallsCounter(D), G2(H2)).distinguish() @ &m : res];
      pose D1 := Pr[Dsse(OracleCallsCounter(D), G1(H1, H2)).distinguish() @ &m : res];
      pose DSophos := Pr[Dsse(OracleCallsCounter(D), Sophos(F, H1, H2)).distinguish() @ &m : res];
      pose Adv_h1 := 2%r*Pr[HashExp1(H1, HashRO1, SH1_Red(H2, OracleCallsCounter(D))).main() @ &m : res] - 1%r;
      pose Adv_h2 := 2%r*Pr[HashExp2(H2, HashRO2, SH2_Red(OracleCallsCounter(D))).main() @ &m : res] - 1%r;
      pose Adv_f := 2%r*Pr[PRFExp(F, RKF, SP_Red(H1, H2, OracleCallsCounter(D))).main() @ &m : res] - 1%r.
    move : (G16_Sim_indistinguishable D &m ct_pre);
      rewrite (sseladaptiveexprom_dsim G16 SophosLeakage SSIM (OracleCallsCounter(D)) &m);
      rewrite (sseladaptiveexprom_dsse G16 SophosLeakage SSIM (OracleCallsCounter(D)) &m);
      rewrite -/DS -/D16 => D16_DS.
    move : (G15_G16_indistinguishable D &m);
      rewrite (sseexprom_dsse_left  G15 G16 (OracleCallsCounter(D)) &m);
      rewrite (sseexprom_dsse_right G15 G16 (OracleCallsCounter(D)) &m);
      rewrite -/D16 -/D15 => D15_D16.
    move : (G14_G15_indistinguishable D &m ct_pre);
      rewrite (sseexprom_dsse_left  G14 G15 (OracleCallsCounter(D)) &m);
      rewrite (sseexprom_dsse_right G14 G15 (OracleCallsCounter(D)) &m);
      rewrite -/D15 -/D14 => D14_D15.
    move : (G13_G14_indistinguishable D &m);
      rewrite (sseexprom_dsse_left  G13 G14 (OracleCallsCounter(D)) &m);
      rewrite (sseexprom_dsse_right G13 G14 (OracleCallsCounter(D)) &m);
      rewrite -/D14 -/D13 => D13_D14.
    move : (G12_G13_indistinguishable D &m);
      rewrite (sseexprom_dsse_left  G12 G13 (OracleCallsCounter(D)) &m);
      rewrite (sseexprom_dsse_right G12 G13 (OracleCallsCounter(D)) &m);
      rewrite -/D13 -/D12 => D12_D13.
    move : (G11_G12_indistinguishable D &m);
      rewrite (sseexprom_dsse_left  G11 G12 (OracleCallsCounter(D)) &m);
      rewrite (sseexprom_dsse_right G11 G12 (OracleCallsCounter(D)) &m);
      rewrite -/D12 -/D11 => D11_D12.
    move : (G10_G11_indistinguishable_uptobad D &m PPTA_D);
      rewrite (sseexprom_dsse_left  G10 G11 (OracleCallsCounter(D)) &m);
      rewrite (sseexprom_dsse_right G10 G11 (OracleCallsCounter(D)) &m);
      have ->: Pr[SSEExpROM(G10, G11, OracleCallsCounter(D)).game (true) @ &m : G10_Client.bad_rf_coll] = Pr[Dsse(OracleCallsCounter(D), G10).distinguish() @ &m : G10_Client.bad_rf_coll] by byequiv => //; proc; rcondt{1} 1; progress; seq 2 2: (={G10_Client.bad_rf_coll}) => //; sim.
      rewrite -ler_subl -/D11 -/D10 -/D10_bad_rf_coll => D10_D11.
    move : (G9_G10_indistinguishable_uptobad D &m PPTA_D);
      rewrite (sseexprom_dsse_left  G9 G10 (OracleCallsCounter(D)) &m);
      rewrite (sseexprom_dsse_right G9 G10 (OracleCallsCounter(D)) &m);
      have ->: Pr[SSEExpROM(G9, G10, OracleCallsCounter(D)).game (true) @ &m : G9_Client.bad_update_h1t] = Pr[Dsse(OracleCallsCounter(D), G9).distinguish() @ &m : G9_Client.bad_update_h1t] by byequiv => //; proc; rcondt{1} 1; progress; seq 2 2: (={G9_Client.bad_update_h1t}) => //; sim.
      rewrite -ler_subl -/D10 -/D9 -/D9_bad_update_h1t => D9_D10.
    move : (G8_G9_indistinguishable_uptobad D &m PPTA_D);
      rewrite (sseexprom_dsse_left  G8 G9 (OracleCallsCounter(D)) &m);
      rewrite (sseexprom_dsse_right G8 G9 (OracleCallsCounter(D)) &m);
      have ->: Pr[SSEExpROM(G8, G9, OracleCallsCounter(D)).game (true) @ &m : G8_Client.bad_update_h2t] = Pr[Dsse(OracleCallsCounter(D), G8).distinguish() @ &m : G8_Client.bad_update_h2t] by byequiv => //; proc; rcondt{1} 1; progress; seq 2 2: (={G8_Client.bad_update_h2t}) => //; sim.
      rewrite -ler_subl -/D9 -/D8 -/D8_bad_update_h2t => D8_D9.
    move : (G7_G8_indistinguishable_uptobad D &m PPTA_D);
      rewrite (sseexprom_dsse_left  G7 G8 (OracleCallsCounter(D)) &m);
      rewrite (sseexprom_dsse_right G7 G8 (OracleCallsCounter(D)) &m);
      have ->: Pr[SSEExpROM(G7, G8, OracleCallsCounter(D)).game (true) @ &m : G7_Client.bad_update_bt] = Pr[Dsse(OracleCallsCounter(D), G7).distinguish() @ &m : G7_Client.bad_update_bt] by byequiv => //; proc; rcondt{1} 1; progress; seq 2 2: (={G7_Client.bad_update_bt}) => //; sim.
      rewrite -ler_subl -/D8 -/D7 -/D7_bad_update_bt => D7_D8.
    move : (G6_G7_indistinguishable_uptobad D &m PPTA_D);
      rewrite (sseexprom_dsse_left  G6 G7 (OracleCallsCounter(D)) &m);
      rewrite (sseexprom_dsse_right G6 G7 (OracleCallsCounter(D)) &m);
      have ->: Pr[SSEExpROM(G6, G7, OracleCallsCounter(D)).game (true) @ &m : G6_Client.bad_h1] = Pr[Dsse(OracleCallsCounter(D), G6).distinguish() @ &m : G6_Client.bad_h1] by byequiv => //; proc; rcondt{1} 1; progress; seq 2 2: (={G6_Client.bad_h1}) => //; sim.
      rewrite -ler_subl -/D7 -/D6 -/D6_bad_h1 => D6_D7.
    move : (G5_G6_indistinguishable_uptobad D &m PPTA_D);
      rewrite (sseexprom_dsse_left  G5 G6 (OracleCallsCounter(D)) &m);
      rewrite (sseexprom_dsse_right G5 G6 (OracleCallsCounter(D)) &m);
      have ->: Pr[SSEExpROM(G5, G6, OracleCallsCounter(D)).game (true) @ &m : G5_Client.bad_h2] = Pr[Dsse(OracleCallsCounter(D), G5).distinguish() @ &m : G5_Client.bad_h2] by byequiv => //; proc; rcondt{1} 1; progress; seq 2 2: (={G5_Client.bad_h2}) => //; sim.
      rewrite -ler_subl -/D6 -/D5 -/D5_bad_h2 => D5_D6.
    move : (G4_G5_indistinguishable_uptobad_disjoint D &m PPTA_D ro12_0);
      rewrite (sseexprom_dsse_left  G4 G5 (OracleCallsCounter(D)) &m);
      rewrite (sseexprom_dsse_right G4 G5 (OracleCallsCounter(D)) &m).
      have ->: Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_h2] = Pr[Dsse(OracleCallsCounter(D), G5).distinguish() @ &m : G5_Client.bad_h2] by byequiv => //; proc; rcondf{1} 1; progress; seq 2 2: (={G5_Client.bad_h2}) => //; sim.
      have ->: Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_h1] = Pr[Dsse(OracleCallsCounter(D), G5).distinguish() @ &m : G5_Client.bad_h1] by byequiv => //; proc; rcondf{1} 1; progress; seq 2 2: (={G5_Client.bad_h1}) => //; sim.
      have ->: Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_update_h2t] = Pr[Dsse(OracleCallsCounter(D), G5).distinguish() @ &m : G5_Client.bad_update_h2t] by byequiv => //; proc; rcondf{1} 1; progress; seq 2 2: (={G5_Client.bad_update_h2t}) => //; sim.
      have ->: Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_update_h1t] = Pr[Dsse(OracleCallsCounter(D), G5).distinguish() @ &m : G5_Client.bad_update_h1t] by byequiv => //; proc; rcondf{1} 1; progress; seq 2 2: (={G5_Client.bad_update_h1t}) => //; sim.
      have ->: Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_update_bt] = Pr[Dsse(OracleCallsCounter(D), G5).distinguish() @ &m : G5_Client.bad_update_bt] by byequiv => //; proc; rcondf{1} 1; progress; seq 2 2: (={G5_Client.bad_update_bt}) => //; sim.
      have ->: Pr[SSEExpROM(G4, G5, OracleCallsCounter(D)).game(false) @ &m : G5_Client.bad_rf_coll] = Pr[Dsse(OracleCallsCounter(D), G5).distinguish() @ &m : G5_Client.bad_rf_coll] by byequiv => //; proc; rcondf{1} 1; progress; seq 2 2: (={G5_Client.bad_rf_coll}) => //; sim.
      rewrite -15!RField.addrA -ler_subl -/D5 -/D4 -/D5_bad_rf_coll -/D5_bad_update_h1t -/D5_bad_update_h2t -/D5_bad_update_bt -/D5_bad_h1 -/D5_bad_h2 14!RField.addrA => D4_D5.
    move : (G3_G4_indistinguishable D &m rkf_0);
      rewrite (sseexprom_dsse_left  G3 G4 (OracleCallsCounter(D)) &m);
      rewrite (sseexprom_dsse_right G3 G4 (OracleCallsCounter(D)) &m);
      rewrite -/D3 -/D4 => D3_D4.
    move : (G2_G3_reduction_to_hashexp2 H2 D &m).
      rewrite eq2adv (sseexprom_advantage (G2(H2)) G3 (OracleCallsCounter(D)) &m).
      + apply (G2_setup_ll H2 dcoins_ll).
      + apply (G3_setup_ll dcoins_ll).
      + rewrite (occ_distinguish_ll D (G2(H2))) (PPTA_DBound (G2(H2))).
        - apply (G2_update_ll H2 h2_ll).
        - apply (G2_query_ll H2 h2_ll).
        - apply (G2_o_ll H2 h2_ll).
      + rewrite (occ_distinguish_ll D G3) (PPTA_DBound G3 G3_update_ll G3_query_ll G3_o_ll).
      rewrite (sseexprom_dsse_left  (G2(H2)) G3 (OracleCallsCounter(D)) &m);
      rewrite (sseexprom_dsse_right (G2(H2)) G3 (OracleCallsCounter(D)) &m);
      rewrite eqr_subl -/D2 -/D3 -/Adv_h2 => D2_D3.
    move : (G1_G2_reduction_to_hashexp1 H1 H2 D &m);
      rewrite eq2adv (sseexprom_advantage (G1(H1, H2)) (G2(H2)) (OracleCallsCounter(D)) &m).
      + apply (G1_setup_ll H1 H2 dcoins_ll).
      + apply (G2_setup_ll H2 dcoins_ll).
      + rewrite (occ_distinguish_ll D (G1(H1, H2))) (PPTA_DBound (G1(H1, H2))).
        - apply (G1_update_ll H1 H2 h1_ll h2_ll).
        - apply (G1_query_ll H1 H2 h1_ll h2_ll).
        - apply (G1_o_ll H1 H2 h1_ll h2_ll).
      + rewrite (occ_distinguish_ll D (G2(H2))) (PPTA_DBound (G2(H2))).
        - apply (G2_update_ll H2 h2_ll).
        - apply (G2_query_ll H2 h2_ll).
        - apply (G2_o_ll H2 h2_ll).
      rewrite (sseexprom_dsse_left  (G1(H1, H2)) (G2(H2)) (OracleCallsCounter(D)) &m);
      rewrite (sseexprom_dsse_right (G1(H1, H2)) (G2(H2)) (OracleCallsCounter(D)) &m);
      rewrite eqr_subl -/D1 -/D2 -/Adv_h1 => D1_D2.
    move : (sophos_G1_reduction_to_prfexp F H1 H2 D &m);
      rewrite eq2adv (sseexprom_advantage (Sophos(F, H1, H2)) (G1(H1, H2)) (OracleCallsCounter(D)) &m).
      + apply (sophos_setup_ll F H1 H2 dcoins_ll keygen_ll).
      + apply (G1_setup_ll H1 H2 dcoins_ll).
      + rewrite (occ_distinguish_ll D (Sophos(F, H1, H2))) (PPTA_DBound (Sophos(F, H1, H2))).
        - apply (sophos_update_ll F H1 H2 f_ll h1_ll h2_ll).
        - apply (sophos_query_ll F H1 H2 f_ll h1_ll h2_ll).
        - apply (sophos_o_ll F H1 H2 h1_ll h2_ll).
      + rewrite (occ_distinguish_ll D (G1(H1, H2))) (PPTA_DBound (G1(H1, H2))).
        - apply (G1_update_ll H1 H2 h1_ll h2_ll).
        - apply (G1_query_ll H1 H2 h1_ll h2_ll).
        - apply (G1_o_ll H1 H2 h1_ll h2_ll).
      rewrite (sseexprom_dsse_left  (Sophos(F, H1, H2)) (G1(H1, H2)) (OracleCallsCounter(D)) &m);
      rewrite (sseexprom_dsse_right (Sophos(F, H1, H2)) (G1(H1, H2)) (OracleCallsCounter(D)) &m);
      rewrite eqr_subl -/DSophos -/D1 -/Adv_f => DSophos_D1.
    (* Now we can start rewriting the advantage *)
    rewrite (sseladaptiveexprom_advantage (Sophos(F, H1, H2)) SophosLeakage SSIM (OracleCallsCounter(D)) &m).
      + apply (sophos_setup_ll F H1 H2 dcoins_ll keygen_ll).
      + apply leaksetup_ll.
      + apply (sim_setup_ll CTP (ctp_index_ll dcoins_ll)).
      + rewrite (occ_distinguish_ll D (Sophos(F, H1, H2))) (PPTA_DBound (Sophos(F, H1, H2))).
        - apply (sophos_update_ll F H1 H2 f_ll h1_ll h2_ll).
        - apply (sophos_query_ll F H1 H2 f_ll h1_ll h2_ll).
        - apply (sophos_o_ll F H1 H2 h1_ll h2_ll).
      + rewrite (occ_distinguish_ll D (SSESimulatorWrapper(SSIM, SophosLeakage))) (PPTA_DBound (SSESimulatorWrapper(SSIM, SophosLeakage))).
        - apply (simw_update_ll SSIM SophosLeakage leakupdate_ll (sim_update_ll CTP)).
        - apply (simw_query_ll SSIM SophosLeakage leakquery_ll (sim_query_ll CTP ctp_forward_ll ctp_backward_ll)).
        - apply (sim_o_ll CTP).
    rewrite (sseladaptiveexprom_dsse (Sophos(F, H1, H2)) SophosLeakage SSIM (OracleCallsCounter(D)) &m).
    rewrite (sseladaptiveexprom_dsim (Sophos(F, H1, H2)) SophosLeakage SSIM (OracleCallsCounter(D)) &m).
    rewrite -/DSophos -/DS.
    (* Composing games *)
    rewrite -13!RField.addrA.
    (* - Remove Adv_f *)
    rewrite DSophos_D1 (RField.addrC D1) -1!RField.addrA ler_add2l.
    (* - Remove Adv_h1 *)
    rewrite D1_D2 (RField.addrC D2) -1!RField.addrA ler_add2l.
    (* - Remove Adv_h2 *)
    rewrite D2_D3 D3_D4 (RField.addrC D4) -1!RField.addrA ler_add2l.
    (* - From the SIM side *)
    rewrite ler_subl D16_DS -D15_D16 -D14_D15 -D13_D14 -D12_D13 -D11_D12 -ler_subl.
    (* - Complete *)
    move : (compose _ _ _ _   D6_D7  D5_D6); rewrite RField.addrC -RField.addrA (RField.addrA _  D6) /= =>  D5_D7.
    move : (compose _ _ _ _   D7_D8  D5_D7); rewrite RField.addrC -RField.addrA (RField.addrA _  D7) /= =>  D5_D8.
    move : (compose _ _ _ _   D8_D9  D5_D8); rewrite RField.addrC -RField.addrA (RField.addrA _  D8) /= =>  D5_D9.
    move : (compose _ _ _ _  D9_D10  D5_D9); rewrite RField.addrC -RField.addrA (RField.addrA _  D9) /= => D5_D10.
    move : (compose _ _ _ _ D10_D11 D5_D10); rewrite RField.addrC -RField.addrA (RField.addrA _ D10) /= => D5_D11.
    move : (compose _ _ _ _  D5_D11  D4_D5); rewrite RField.addrC -RField.addrA (RField.addrA _  D5).
    rewrite (RField.addrC _ D5_bad) -6!RField.addrA //.
  qed.

  end section SophosSecurity.

end section Sophos.
