(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2018 - Roberto Metere <r.metere2@ncl.ac.uk>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(*
 * Sophos.
 *)
require import Core.
require import TacticsExt.
require import Bool.
require import Int.
require import IntExtra.
require import IntExt.
require import LogicExt.
require import Ring Real.
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
(*---*) import Ring.IntID.

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
          + rewrite opprD addzA /= -(ltz_add2l (- c{hr})) 3!addzA /= -(ltz_add2r (i{hr})) -addzA //.
        wp; skip; progress.
        + rewrite (lez_trans c{hr}) // -(lez_add2l (-c{hr})) addzA //.
        + rewrite lezNgt /= -lez_add1r -(lez_add2r (-i0)) /= -addzA addzC; assumption.
        (* ! 0 <= c *)
        rcondf 1; progress.
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
   * The simulator is not able to correctly call the hash functions, since it does not know the right arguments.
   * In this step toward the simulator, we simulate utokens with a table (query, int -> utoken).
   * Simulating utokens (with a table working as random function) will also require to manipulate the hash functions.
   * Getting rid of the hash functions is not as easy as the previous step, since both the server and the client use it.
   * Some additional care has to be taken in order to keep some consistency.
   *
   * This particular construction resembles the original G2 in CCS'16 with corrections from CCS'17.
   * We show that, even with the corrections, the original proof is incorrect.
   *)
  module G5_Client_Inconsistent(H2: HashFunction2): SSEClient = {
    var sk: tau
    var ws: (query, stoken list) fmap

    var utt: (query * int, utoken) fmap
    var h1t: (mapquery * stoken, utoken) fmap

    var badupdate: bool (* bad event raised by update *)
    var badh1: bool (* bad event raised by h1 *)

    proc setup(): setupserver = {
      var pk;

      (pk, sk) <@ CTP.index();
      ws <- empty;

      utt <- empty;
      h1t <- empty;

      badupdate <- false;
      badh1 <- false;

      return pk;
    }

    (*
     * In the CCS'16 paper the incorrectness of H1 simulating procedure is blatant;
     * they must have noticed such inconsistency in the CCS'17 paper
     * and attempted to silently fix it, with slightly different construction.
     * However, we show that their fix does not work for Sophos anyways.
     *)
    module SimH1: HashFunction1 = {
      proc hash(kw: mapquery, s: stoken): utoken = {
        var c, ls, y, qs, cand_ws, w;

        if (!(dom h1t (kw, s))) {
          (*
           * Additional care when h1t is not synced with utt (i.e. update was not called before it)
           *)
          qs <- fdom (filter (fun (q: query) k => k = kw) RF.m); (* queries mapping to kw *)
          cand_ws <- filter (fun (q: query) (ts: stoken list) => mem qs q /\ has ((=) s) ts) ws; (* occurrences in the ws map *)
          if (cand_ws <> empty) { (* occurrence found *)
            badh1 <- true;
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

    proc update(o: operation, q: query, i: index): (utoken * index) option = {
      var kw, s, c, sc, idx, ti, y;

      if (o = ADD) {
        kw <@ RF.f(q);
        if (!dom ws q) {
          s <$ dstoken;
          c <- 0;
          ws.[q] <- [s];
        } else {
          sc <- oget ws.[q];
          c <- size sc;
          s <@ CTP.backward(sk, last witness sc);
          ws.[q] <- sc ++ [s];
        }
        (*
         * Extra care to keep consistency (someone already queried this)
         *)
        if (! (dom h1t (kw, s))) {
          y <$ dutoken;
          utt.[(q, c)] <- y;
        } else {
          badupdate <- true;
          utt.[(q, c)] <- oget h1t.[(kw, s)];
        }
        idx <@ H2.hash(kw, s);
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

        (* Lazily programming the hash table *)
        i <- 0;
        while (i < size sc) {
          s <- nth witness sc i;
          h1t.[(kw, s)] <- oget utt.[(q, i)];
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
        h2 <@ H2.hash(argv);
        h <- Some(None, Some(h2));
      }

      return h;
    }
  }.

  module G5_Server(H1: HashFunction1, H2: HashFunction2): SSEServer = {
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
        (* We expect to have "dom edb ut" always true for all legitimate queries *)
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

  module G5_Inconsistent(H2: HashFunction2) = SSEProtocol(G5_Client_Inconsistent(H2), G5_Server(G5_Client_Inconsistent(H2).SimH1, H2)).

  lemma G5_Client_Inconsistent_o_ll (H2<: HashFunction2):
    islossless H2.hash =>
    islossless G5_Client_Inconsistent(H2).o.
  proof.
    move => H2_hash_ll; proc; inline *.
    wp; sp; if => //.
    + sp; if => //.
      + sp; if => //.
        + wp; trivial.
        - wp; rnd; skip; progress; smt(dut_ll).
      - wp; skip; progress.
    + if => //.
      wp; call H2_hash_ll; skip; trivial.
  qed.

  lemma G5_Client_Inconsistent_o1_ll (H2<: HashFunction2):
    phoare[ G5_Client_Inconsistent(H2).o : i = HASH1 ==> true] = 1%r.
  proof.
    proc; inline *.
    rcondt 2.
    + wp; skip; trivial.
      wp; sp; if => //.
      + sp; if => //.
        + wp; trivial.
        - wp; rnd; skip; progress; smt(dut_ll).
  qed.

  (*
   * The inconsistency issue can happen with simple consequent calls
   * to the update function.
   *)
  module G5_Inconsistency(H2: HashFunction2) = {
    proc inc(q, i, q', i'): unit = {

      G5_Client_Inconsistent(H2).update(ADD, q , i );
      G5_Client_Inconsistent(H2).update(ADD, q', i');
    }
  }.

  const pr_ds: { real | 0%r < pr_ds /\ (forall x, mu1 ds x = pr_ds) } as dstoken_pr.

  (*
   * For easiness, we consider the case when pr_ds is the probability
   * of uniformly sampling from the distribution ds.
   * Such probability is greater strictly positive.
   * We then refer to e, which is the difference of pr_ds and the
   * probability of sampling the same value 
   *)
  lemma G5_inconsistency
    (H2<: HashFunction2{RF,RO1,G5_Inconsistent,G5_Client_Inconsistent,G5_Server}) e w w':
    e = pr_ds * (1%r - inv (2^utlen)%r) =>
    islossless H2.hash =>
    phoare[ G5_Inconsistency(H2).inc :
      (*
       * - Precondition
       * The two terms w and w' are different and in the RF.
       * Update were never called with those, since ws, h1t and utt are empty.
       * 
       * We need to set the local input q and q' to w and w'.
       * Being local, they are NOT available in the post-condition.
       *)
      (q, q') = (w, w') /\ 
      q <> q' /\
      dom RF.m q /\
      dom RF.m q' /\
      RF.m.[q] = RF.m.[q'] /\
      G5_Client_Inconsistent.ws = empty /\
      G5_Client_Inconsistent.h1t = empty /\
      G5_Client_Inconsistent.utt = empty
      ==>
      (*
       * - Post-condition
       * The two updates called subsequently have a non-zero probability
       * of breaking the consistency we need for later searches and calls to hash1.
       * In particular, while the values in ws can be the same,
       * the pre-computed (actually sampled) hash1 values in utt can differ.
       * 
       * When this happens, the two games are totally distinguishable,
       * by simply the following simple steps:
       * 1. search(w) → (kw,ws[w],0) - programs h1t[kw,ws[w]] ← utt[w, 0];
       * 2. H1(kw,ws[w]) → utt[w, 0];
       * 3. search(w') → (kw,ws[w'],0) = (kw,ws[w],0);
       * 4. H1(kw,ws[w]) again → utt[w', 0] ≠ utt[w, 0].
       * 5. the distinguisher knows it must not be the original Sophos.
       * 
       * On the contrary, calling H2(kw,ws[w]) does not show any problems.
       * Moreover, H1 is not even a function any longer; so, investigating whether
       * this probability is or can be done negligible may not be worth it.
       * This is also because, from the point of view of formalising proofs, 
       * those "bad" cases can become too difficult to handle.
       *)
         G5_Client_Inconsistent.ws.[w] = G5_Client_Inconsistent.ws.[w']
      /\ G5_Client_Inconsistent.utt.[(w, 0)] <> G5_Client_Inconsistent.utt.[(w', 0)]
    ] >= e.
  proof.
    move => epr h2_ll; proc; inline*.
    rcondt 4; first by wp; skip; progress.
    rcondf 5; first by wp; skip; progress.
    rcondt 6; first wp; skip; progress; smt.
    rcondt 9; first wp; rnd; wp; skip; progress; smt.
    rcondt 17; first wp; call (_: true) => //; wp; rnd; wp; skip; progress.
    rcondf 18; first wp; call (_: true) => //; wp; rnd; wp; rnd; wp; skip; progress.
    rcondt 19; first wp; call (_: true) => //; wp; rnd; wp; rnd; wp; skip; progress; smt.
    rcondt 22; first wp; rnd; wp; call (_: true) => //; wp; rnd; wp; rnd; wp; skip; progress; smt.
    swap 6 -5.
    swap 19 -17.
    swap 10 -7.
    swap 22 -18.

    seq 2: (
           (q, q') = (w, w')  /\
           q <> q' /\
           dom RF.m q /\
           dom RF.m q' /\
           RF.m.[q] = RF.m.[q'] /\
           G5_Client_Inconsistent.ws = empty /\
           G5_Client_Inconsistent.h1t = empty /\
           G5_Client_Inconsistent.utt = empty /\
           s = s0) (pr_ds) (1%r - inv (2^utlen)%r) (1%r - pr_ds) (0%r).
      + rnd; rnd; skip; progress.
      + seq 1: (
               (q, q') = (w, w')  /\
               q <> q' /\
               dom RF.m q /\
               dom RF.m q' /\
               RF.m.[q] = RF.m.[q'] /\
               G5_Client_Inconsistent.ws = empty /\
               G5_Client_Inconsistent.h1t = empty /\
               G5_Client_Inconsistent.utt = empty /\
               (s = s0 \/ s <> s0)) (pr_ds).
        + rnd; skip; progress.
        + rnd; skip; progress.
          have ->: pr_ds / pr_ds = 1%r by smt.
          smt.
        + rnd; skip; progress.
          rewrite H H0 H1 H3 /=.
          have ->: (fun x => s{hr} = x) = pred1 s{hr} by rewrite /predC /pred1 /= fun_ext /(==) => x; rewrite eq_iff eq_sym //.
          smt.
        + rnd; skip; progress; smt.
        + smt.
      + seq 2: (
               (q, q') = (w, w')  /\
               q <> q' /\
               dom RF.m q /\
               dom RF.m q' /\
               RF.m.[q] = RF.m.[q'] /\
               G5_Client_Inconsistent.ws = empty /\
               G5_Client_Inconsistent.h1t = empty /\
               G5_Client_Inconsistent.utt = empty /\
               s = s0 /\
               y <> y0) (1%r - inv (2^utlen)%r) (1%r) (inv (2^utlen)%r) (0%r).
        + rnd; rnd; skip; progress.
        + seq 1: (
               (q, q') = (w, w')  /\
               q <> q' /\
               dom RF.m q /\
               dom RF.m q' /\
               RF.m.[q] = RF.m.[q'] /\
               G5_Client_Inconsistent.ws = empty /\
               G5_Client_Inconsistent.h1t = empty /\
               G5_Client_Inconsistent.utt = empty /\
               s = s0 /\
               (y = y0 \/ y <> y0)) (1%r - inv (2^utlen)%r).
          + rnd; skip; progress.
          + rnd; skip; progress.
            pose p := (1%r - inv (2 ^ utlen)%r).
            have ->: p / p = 1%r by smt.
            have ->: q{hr} <> q'{hr} by rewrite H.
            have ->: dom RF.m{hr} q{hr} by rewrite H0.
            have ->: dom RF.m{hr} q'{hr} by rewrite H1.
            have ->: RF.m{hr}.[q{hr}] = RF.m{hr}.[q'{hr}] by rewrite H3.
            simplify.
            have ->: (fun (x : utoken) => x = y0{hr} \/ x <> y0{hr}) = fun (_: utoken) => true by rewrite fun_ext => x; smt.
            smt.
          + rnd; skip; progress.
            rewrite H H0 H1 H3 /=.
            have ->: (fun x => y{hr} <> x) = predC (pred1 y{hr}) by rewrite /predC /pred1 /= fun_ext /(==) => x; rewrite eq_iff eq_sym //.
            smt.
          + rnd; skip; progress; smt.
        + smt.
      + wp; (kill 20; first by call (_: true) => //).
        wp; (kill 9; first by call (_: true) => //).
        wp; wp; skip; progress; first by smt.
        have pairdiff: (q'{hr}, 0) <> (q{hr}, 0) by smt.
        rewrite get_set_sameE set_setE pairdiff /= get_set_sameE //.
      + auto; smt.
      + auto; smt.
    + auto; smt.
    + auto; smt.
  qed.
  (* Inconsistency -- END *)

  end section SophosSecurity.

end section Sophos.

print G5_Client_Inconsistent.
print G5_Inconsistency.
print G5_inconsistency.
