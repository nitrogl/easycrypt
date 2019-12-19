(* --------------------------------------------------------------------
 * Copyright (c) - 2016--2017 Roberto Metere (r.metere2@ncl.ac.uk)
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(*
 * A formalisation of (dynamic) Searchable Symmetric Encryption
 *)
require import Distr.
require import DBool.
require import Real.
require import Int.
require import List.
require import SmtMap.
require import FSet.
require (*--*) Lazy NewROM.

theory SearchableSymmetricEncryption.
  type key.
  type query. (* search is a keyword in EC, so here "query" is used as synonym of "search query" *)
  type mapquery. (* when the queries are transformed or mapped *)
  type index.
  type storage = (index, query list) fmap. (* database of indexes *)
  type encryptedstorage. (* the real database with files *)
  type state.
  type setupserver.
  type client_update_out.
  type client_query_out.
  type server_query_out.
  const empty_out : server_query_out.

  (* Some common operations *)
  type sse_protocol = [ UPDATE | SEARCH ].
  type operation = [ ADD | DEL ].
  type operationinput.
  op extract_query (o: operation) (oargs: operationinput) : query.
  op extract_index (o: operation) (oargs: operationinput) : index.

  (* distributions *)
  op dkey: key distr.
  op dmapquery: mapquery distr.

  (* Generating random queries *)
  op dupdate: (operation * operationinput) distr.
  op dquery: query distr.

  (** match returns all the (file) indexes matching some query *)
  op match (db: storage) (q: query): index list = elems (fdom (filter (fun _ => has ((=) q)) db)).

  (** final result is the list of indexes *)
  op elaborate_indexes (so: server_query_out) : index list.

  (** history lists "timed" database snapshots with queries *)
  type updateevent = storage * (operation * operationinput).
  type queryevent  = storage * query.
  type event = storage *
      (operation * operationinput) option (* update *)
    * query option.                      (* search *)
  type updatehistory = (int * updateevent) list.
  type queryhistory = (int * queryevent) list.
  type history = (int * event) list.

  (** Operations for high level understanding *)
  op eup_storage   (e: updateevent) = fst e.
  op eup_input     (e: updateevent) = snd e.
  op eup_operation (e: updateevent) = fst (eup_input e).
  op eup_query     (e: updateevent) : query.
  op eup_index     (e: updateevent) : index.
  op up_query     (i: operationinput) : query.
  op up_index     (i: operationinput) : index.
  op eq_storage   (e: queryevent) = fst e.
  op eq_query     (e: queryevent) = snd e.
  op ev_storage (e: event) = e.`1.
  op oev_update (e: event) = e.`2.
  op oev_query  (e: event) = e.`3.
  op ev_update  (e: event) = oget e.`2.
  op ev_query   (e: event) = oget e.`3.
  op h_time     (h: int * event) = fst h.
  op h_event     (h: int * event) = snd h.
  op h_storage   (h: int * event) = ev_storage (h_event h).
  op oh_update  (h: int * event) = oev_update (h_event h).
  op oh_query   (h: int * event) = oev_query (h_event h).
  op h_update   (h: int * event) = ev_update (h_event h).
  op h_query    (h: int * event) = ev_query (h_event h).
  op hup_time   (e: int * updateevent) = fst e.
  op hup_event  (e: int * updateevent) = snd e.
  op hq_time    (e: int * queryevent) = fst e.
  op hq_event   (e: int * queryevent) = snd e.

  (** Projection of the subset of the history containing only updates *)
  op projUpdates (h: history): updatehistory = map (fun (e: int * event) => (h_time e, (h_storage e, h_update e)))
                                                   (filter (fun (e: int * event) => oh_update e <> None) h).
  (** Projection of the subset of the history containing only search queries *)
  op projQueries (h: history): queryhistory  = map (fun (e: int * event) => (h_time e, (h_storage e, h_query e)))
                                                   (filter (fun (e: int * event) => oh_query e <> None) h).

  (** Subset of the history regarding some specific query *)
  op hist (h: history) (q: query): history = filter (fun (e: int * event) => (oh_update e <> None /\ up_query (snd (h_update e)) = q) \/ oh_query e = Some q) h.
  op lastdb (h: history): storage = (h = []) ? empty : h_storage (nth witness h (size h - 1)).

  (** Access pattern with history for each search queries ad updates, then mixed *)
  type uhpattern = (int * operation * index) list.
  type qhpattern = (int * index list) list.
  type ahpattern = uhpattern * qhpattern.
  op ahpU (h: history) (q: query): uhpattern = map (fun (z: int * updateevent) => (hup_time z, eup_operation (hup_event z), eup_index (hup_event z))) (projUpdates (hist h q)).
  op ahpQ (h: history) (q: query): qhpattern = map (fun (z: int * queryevent) => (hq_time z, match (eq_storage (hq_event z)) (eq_query (hq_event z)))) (projQueries (hist h q)).
  op ahp (h: history) (q: query): ahpattern = (ahpU h q, ahpQ h q). (* The order can be recovered from the indexes *)

  lemma ahpU_cat q h1 h2: ahpU (h1 ++ h2) q = (ahpU h1 q) ++ (ahpU h2 q).
  proof. rewrite /ahpU /projUpdates /hist 2!filter_cat 2!map_cat -2!filter_predI /predI -2!map_comp /(\o) //. qed.
  lemma ahpQ_cat q h1 h2: ahpQ (h1 ++ h2) q = (ahpQ h1 q) ++ (ahpQ h2 q).
  proof. rewrite /ahpQ /projQueries /hist 2!filter_cat 2!map_cat -2!filter_predI /predI -2!map_comp /(\o) //. qed.

  (** All queries (update+search) pattern, aka access pattern: all "times" when some specific query appears in the history *)
  op ap (h: history) (q: query): int list = map h_time (hist h q).

  lemma ap_cat q h1 h2: ap (h1 ++ h2) q = (ap h1 q) ++ (ap h2 q).
  proof. rewrite /ap /hist filter_cat map_cat //. qed.

  lemma mem_ap q h x: mem (ap h q) x => mem (map fst (hist h q)) x.
  proof. rewrite mem_map_fst //. qed.

  (** Search-queries-only pattern *)
  op qp (h: history) (q: query): int list = map hq_time (projQueries (hist h q)).

  lemma qp_cat q h1 h2: qp (h1 ++ h2) q = (qp h1 q) ++ (qp h2 q).
  proof. rewrite /qp /projQueries /hist 2!filter_cat 2!map_cat -2!filter_predI /predI -2!map_comp /(\o) //. qed.

  lemma mem_qp_ap q h x: mem (qp h q) x => mem (ap h q) x.
  proof.
    rewrite /ap /qp /projQueries -map_comp /(\o) /= 2!mem_map_fst //.
    move => [qe]; rewrite mem_filter /=; move => [_] concl.
    exists qe => //.
  qed.

  (** Leakage, leakage is stateful *)
  type Lsetup.
  type Lupdate.
  type Lquery.
  type L = Lsetup * Lupdate * Lquery. (* unneeded? *)

  module type SSELeakage = {
    proc leakSetup(_: unit): Lsetup
    proc leakUpdate(o: operation, oin: operationinput): Lupdate
    proc leakQuery(q: query): Lquery
  }.

  (** Trace collects, with respect to initial setupserver, input and output of update, search, and oracle calls *)
  type update_view. (* ((operation * operationinput) * client_update_out option)  *)
  type query_view. (* (query * client_query_out option * server_query_out) *)
  type update_trace = (operation * operationinput) * update_view.
  type query_trace = query * query_view.
  type trace = (setupserver, (
      (update_trace option)  (* update *)
    * (query_trace option) (* search *)
  ) list) fmap.
  op trace_add_update (s: setupserver) (ut: update_trace) (t: trace): trace.
  op trace_add_query (s: setupserver) (qt: query_trace) (t: trace): trace.
  op extract_result (qv: query_view) : server_query_out.

  (*
   * To support proofs in the ROM, we make oracles out of SSE schemes.
   *)
  (* Here, the oracle exposes *at least* update and query functions, as well as customisable o function (the client is supposed to be able to implement it) *)
  theory SSEOracleTheory.
    type sseo_args_t.
    type sseo_res_t.

    module type SSEOracle = {
      proc init()    : unit
      proc update(o: operation, oin: operationinput): update_view
      proc query(q: query): query_view
      proc o (x: int * sseo_args_t): sseo_res_t option
    }.

    (* Adversaries are restricted to update, query, or customised o access *)
    module type SSEAccess = {
      proc update(o: operation, oin: operationinput): update_view
      proc query(q: query): query_view
      proc o(x: int * sseo_args_t): sseo_res_t option
    }.

    (* Adversaries are passed the oracles restricted as oracle access *)
    module type SSEDistROM(SA: SSEAccess) = {
      proc distinguish(): bool
    }.
  end SSEOracleTheory.
  import SSEOracleTheory.

  (**
   * SSE scheme includes three procedures: setup, update, and query (aka search).
   *
   * The additional procedure "o" may not enjoy any real implementation: In such a case, the simple constant "None" can be safely returned.
   *)
  module type SSEClient = {
    proc setup(): setupserver
    proc update(o: operation, oin: operationinput): client_update_out option
    proc query(q: query): client_query_out option
    proc o(oin: int * sseo_args_t): sseo_res_t option
  }.

  module type SSEServer = {
    proc setup(s: setupserver): unit
    proc update(o: operation, uin: client_update_out): unit
    proc query(qin: client_query_out): server_query_out
  }.

  (* The scheme leaving all traces and exposes oracle access *)
  module type SSEScheme = {
    proc setup(): setupserver
    proc update(o: operation, oin: operationinput): update_view
    proc query(q: query): query_view
    proc o(oin: int * sseo_args_t): sseo_res_t option
  }.

  (* First try - It looks more difficult to prove than many other protocols. *)
  module Correctness(S: SSEScheme) = {
    proc main(n: int): bool = {
      var r, i, b, queryres, idxs;
      var o, oargs, q, ind, qv;
      var db: storage;

      S.setup();

      db <- empty;
      r <- true; (* correct until shown otherwise *)
      i <- 0;
      while (i < n) {
        b <$ {0,1};
        if (b) { (* b - UPDATE *)
          (o, oargs) <$ dupdate;
          S.update(o, oargs);
          if (o = ADD) {
            (* store the updates in clear *)
              q <- extract_query ADD oargs;
            ind <- extract_index ADD oargs;
            if (!(dom db ind)) {
              db.[ind] <- [q];
            } else {
              db.[ind] <- (oget db.[ind]) ++ [q];
            }
          } else {
            if (o = DEL) {
                q <- extract_query DEL oargs;
              ind <- extract_index DEL oargs;
              if (!(dom db ind)) {
                db.[ind] <- [];
              } else {
                db.[ind] <- rem q (oget db.[ind]);
              }
            }
          }
        } else { (* ¬b - SEARCH *)
          q <$ dquery;
          qv <@ S.query(q);
          queryres <- extract_result qv;
          if (queryres <> empty_out) {
            idxs <- elaborate_indexes queryres;
            r <- r /\ perm_eq idxs (match db q);
          }
        }
      }

      return r;
    }
  }.

  (** Simulator *)
  module type SSESimulator = {
    proc setup(ls: Lsetup): setupserver
    proc update(lu: Lupdate): update_view
    proc query(lq: Lquery): query_view
    proc o(oin: int * sseo_args_t): sseo_res_t option
  }.

  (** Adaptive distinguisher. It distiguishes by the trace of execution *)
  module type SSEDist = {
    proc adaptiveUorQ(t: trace): sse_protocol (* what's next? update query or search query? *)
    proc sortInputsU(): operation * operationinput
    proc sortInputsQ(): query
    proc distinguish(t: trace): bool
  }.

  (**
   * This experiment calls a distinguisher between two schemes.
   * The experiment is useful for game based reductions (but may not be the "last" experiment).
   * The experiment already limits the attacker to at most n runs of the protocol
   *)
  module SSEExperiment(S1: SSEScheme, S2: SSEScheme, D: SSEDist) = {

    proc game(real: bool, n: int): bool = {
      var g, i, iU, oU, iQ, oQ, oS, t, what;

      (* Setup games *)
      if (real) oS <@ S1.setup();
      else      oS <@ S2.setup();

      (* Initialise the trace *)
      t = empty;
      t.[oS] <- [];

      i = 0;
      while(i < n) {
        if (real) {
          what <@ D.adaptiveUorQ(t);
          if (what = UPDATE) {
            iU <@ D.sortInputsU();
            oU <@ S1.update(iU);
            t <- trace_add_update oS (iU, oU) t;
          } elif (what = SEARCH) {
            iQ <@ D.sortInputsQ();
            oQ <@ S1.query(iQ);
            t <- trace_add_query oS (iQ, oQ) t;
          }
        } else {
          what <@ D.adaptiveUorQ(t);
          if (what = UPDATE) {
            iU <@ D.sortInputsU();
            oU <@ S2.update(iU);
            t <- trace_add_update oS (iU, oU) t;
          } elif (what = SEARCH) {
            iQ <@ D.sortInputsQ();
            oQ <@ S2.query(iQ);
            t <- trace_add_query oS (iQ, oQ) t;
          }
        }
        if (what = UPDATE \/ what = SEARCH) i = i + 1;
        else i = n; (* break the loop smoothly *)
      }
      g <@ D.distinguish(t);

      return g;
    }

    (* n is supposed to be some polynomial bound to how many queries D can do *)
    proc main(n: int): bool = {
      var b, b';

      b  <$ {0,1};
      b' <@ game(b, n);

      return b = b';
    }
  }.

  (**
   * L-adaptive-security is a desirable property of the protocol.
   * It is basically the experiment above, but between a scheme and a simulator of the scheme (given leakage functions).
   *)
  module SSELAdaptiveSecurity(S1: SSEScheme, S2: SSESimulator, L: SSELeakage, D: SSEDist) = {
      
    proc game(real: bool, n: int): bool = {
      var g, i, iU, oU, iQ, oQ, oS, t, what, ls, lu, lq;

      (* Setup games *)
      if (real) {
        oS <@ S1.setup();
      } else {
        ls <@ L.leakSetup();
        oS <@ S2.setup(ls);
      }

      (* Initialise the trace *)
      t = empty;
      t.[oS] <- [];

      i = 0;
      while(i < n) {
        if (real) {
          what <@ D.adaptiveUorQ(t);
          if (what = UPDATE) {
            iU <@ D.sortInputsU();
            oU <@ S1.update(iU);
            t <- trace_add_update oS (iU, oU) t;
          } elif (what = SEARCH) {
            iQ <@ D.sortInputsQ();
            oQ <@ S1.query(iQ);
            t <- trace_add_query oS (iQ, oQ) t;
          }
        } else {
          what <@ D.adaptiveUorQ(t);
          if (what = UPDATE) {
            iU <@ D.sortInputsU();
            lu <@ L.leakUpdate(iU);
            oU <@ S2.update(lu);
            t <- trace_add_update oS (iU, oU) t;
          } elif (what = SEARCH) {
            iQ <@ D.sortInputsQ();
            lq <@ L.leakQuery(iQ);
            oQ <@ S2.query(lq);
            t <- trace_add_query oS (iQ, oQ) t;
          }
        }
        if (what = UPDATE \/ what = SEARCH) i = i + 1;
        else i = n; (* break the loop smoothly *)
      }
      g <@ D.distinguish(t);

      return g;
    }

    (* n is supposed to be some polynomial bound to how many queries D can do *)
    proc main(n: int): bool = {
      var b, b';

      b  <$ {0,1};
      b' <@ game(b, n);

      return b = b';
    }
  }.

  (* Experiment in the ROM *)
  module SSEExpROM(S1: SSEScheme, S2: SSEScheme, D: SSEDistROM) = {

    proc game(real: bool): bool = {
      var g;

      (* Setup games *)
      if (real) {
        S1.setup();
        g <@ D(S1).distinguish();
      } else {
        S2.setup();
        g <@ D(S2).distinguish();
      }

      return g;
    }

    proc main(): bool = {
      var b, b';

      b  <$ {0,1};
      b' <@ game(b);

      return b = b';
    }
  }.

  lemma sseexprom_game_ll (S1<: SSEScheme) (S2<: SSEScheme) (D<: SSEDistROM):
    islossless S1.setup =>
    islossless S2.setup =>
    islossless D(S1).distinguish =>
    islossless D(S2).distinguish =>
    islossless SSEExpROM(S1, S2, D).game.
  proof.
    move => S1setup_ll S2setup_ll Ddistinguish1_ll Ddistinguish2_ll.
    proc => //.
    if => //.
      (* real *)
      call Ddistinguish1_ll; call S1setup_ll; wp; skip; trivial.
      (* !real *)
      call Ddistinguish2_ll; call S2setup_ll; wp; skip; trivial.
  qed.

  lemma sseexp_main_ll (S1<: SSEScheme) (S2<: SSEScheme) (D<: SSEDistROM):
    islossless S1.setup =>
    islossless S2.setup =>
    islossless D(S1).distinguish =>
    islossless D(S2).distinguish =>
    islossless SSEExpROM(S1, S2, D).main.
  proof.
    move => S1setup_ll S2setup_ll Ddistinguish1_ll Ddistinguish2_ll.
    have game_ll: islossless SSEExpROM(S1, S2, D).game by apply (sseexprom_game_ll S1 S2 D).
    proc; call game_ll; rnd; skip; progress; apply (dboolE predT).
  qed.

  (*
   * Total probability
   * Pr[Main] = 1/2 Pr[Real] + 1/2 Pr[!Ideal]
   *)
  lemma sseexprom_total_probability (S1<: SSEScheme) (S2<: SSEScheme) (D<: SSEDistROM{S1,S2}) &m:
    Pr[SSEExpROM(S1, S2, D).main() @ &m : res] = 1%r/2%r * (Pr[SSEExpROM(S1, S2, D).game(true) @ &m : res] + Pr[SSEExpROM(S1, S2, D).game(false) @ &m : !res]).
  proof.
    pose prReal := Pr[SSEExpROM(S1, S2, D).game(true) @ &m : res].
    pose prIdeal := Pr[SSEExpROM(S1, S2, D).game(false) @ &m : !res].
    byphoare (_: (glob D, glob S1, glob S2) = (glob D, glob S1, glob S2){m} ==> _) => //; proc => //.
    seq 1: (b) (1%r/2%r) prReal (1%r/2%r) prIdeal ((glob D, glob S1, glob S2) = (glob D, glob S1, glob S2){m}).
      rnd; wp; skip; smt.
      (* post = b *)
      rnd; wp; skip; smt.
      rewrite /prReal.
        (* b *)
        call (_: (glob D, glob S1, glob S2) = (glob D, glob S1, glob S2){m} /\ real ==> res) => //; last by skip; progress; smt.
        bypr; progress; rewrite H2.
        byequiv => //; by sim; progress; smt.
      (* post = !b *)
      rnd; wp; skip; smt.
      rewrite /prIdeal.
        (* !b *)
        call (_: (glob D, glob S1, glob S2) = (glob D, glob S1, glob S2){m} /\ !real ==> !res) => //; last by skip; progress; smt.
        bypr; progress; rewrite H2.
        byequiv => //; by sim; progress; smt.
    progress; smt.
  qed.

  (*
  *  Advantage: |2*Pr[Main] - 1| = Pr[Real] - Pr[Ideal]
  *)
  lemma sseexprom_advantage (S1<: SSEScheme) (S2<: SSEScheme) (D<: SSEDistROM{S1, S2}) &m:
    islossless S1.setup =>
    islossless S2.setup =>
    islossless D(S1).distinguish =>
    islossless D(S2).distinguish =>
    2%r * Pr[SSEExpROM(S1, S2, D).main() @ &m : res] - 1%r =
    Pr[SSEExpROM(S1, S2, D).game(true) @ &m : res] - Pr[SSEExpROM(S1, S2, D).game(false) @ &m : res].
  proof.
    move => S1setup_ll S2setup_ll Ddistinguish1_ll Ddistinguish2_ll.
    pose prReal := Pr[SSEExpROM(S1, S2, D).game(true) @ &m : res].
    have ->: Pr[SSEExpROM(S1, S2, D).game(false) @ &m : res] = 1%r - Pr[SSEExpROM(S1, S2, D).game(false) @ &m : !res].
      rewrite Pr [mu_not].
      have ->: Pr[SSEExpROM(S1, S2, D).game(false) @ &m : true] = 1%r.
        byphoare => //; apply (sseexprom_game_ll S1 S2 D) => //.
      smt.
    pose prIdeal := Pr[SSEExpROM(S1, S2, D).game(false) @ &m : !res].
    have ->: (2%r * Pr[SSEExpROM(S1, S2, D).main() @ &m : res] - 1%r = prReal - (1%r - prIdeal)) = (Pr[SSEExpROM(S1, S2, D).main() @ &m : res] = 1%r/2%r * (prReal + prIdeal)) by smt.
    apply (sseexprom_total_probability S1 S2 D &m).
  qed.
  
  (* Combine the simulator and the leakage function to create a (fake) scheme *)
  module SSESimulatorWrapper(S: SSESimulator, L: SSELeakage) : SSEScheme = {
    proc setup(): setupserver= {
      var input, output;
      
      input <@ L.leakSetup();
      output <@ S.setup(input);
      
      return output;
    }
    
    proc update(o: operation, oin: operationinput): update_view = {
      var input, output;
      
      input <@ L.leakUpdate(o, oin);
      output <@ S.update(input);
      
      return output;
    }
    
    proc query(q: query): query_view = {
      var input, output;
      
      input <@ L.leakQuery(q);
      output <@ S.query(input);
      
      return output;
    }
    
    proc o = S.o
  }.

  lemma simw_setup_ll (S<: SSESimulator) (L<: SSELeakage):
    islossless L.leakSetup =>
    islossless S.setup =>
    islossless SSESimulatorWrapper(S, L).setup.
  proof.
    move => l_ll sim_ll.
    proc; inline*; call sim_ll; call l_ll; skip; progress.
  qed.

  lemma simw_update_ll (S<: SSESimulator) (L<: SSELeakage):
    islossless L.leakUpdate =>
    islossless S.update =>
    islossless SSESimulatorWrapper(S, L).update.
  proof.
    move => l_ll sim_ll.
    proc; inline*; call sim_ll; call l_ll; skip; progress.
  qed.

  lemma simw_query_ll (S<: SSESimulator) (L<: SSELeakage):
    islossless L.leakQuery =>
    islossless S.query =>
    islossless SSESimulatorWrapper(S, L).query.
  proof.
    move => l_ll sim_ll.
    proc; inline*; call sim_ll; call l_ll; skip; progress.
  qed.

  (* Experiment in the ROM for L-adaptive security (with simulator and leakage) *)
  module SSELAdaptiveSecurityROM(S1: SSEScheme, S2: SSESimulator, L: SSELeakage, D: SSEDistROM) = {

    proc game(real: bool): bool = {
      var g;

      (* Setup games *)
      if (real) {
        S1.setup();
        g <@ D(S1).distinguish();
      } else {
        SSESimulatorWrapper(S2, L).setup();
        g <@ D(SSESimulatorWrapper(S2, L)).distinguish();
      }

      return g;
    }

    proc main(): bool = {
      var b, b';

      b  <$ {0,1};
      b' <@ game(b);

      return b = b';
    }
  }.

  lemma sseladaptiveexprom_game_ll (S1<: SSEScheme) (S2<: SSESimulator) (L<: SSELeakage) (D<: SSEDistROM):
    islossless S1.setup =>
    islossless L.leakSetup =>
    islossless S2.setup =>
    islossless D(S1).distinguish =>
    islossless D(SSESimulatorWrapper(S2, L)).distinguish =>
    islossless SSELAdaptiveSecurityROM(S1, S2, L, D).game.
  proof.
    move => S1setup_ll Lsetup_ll S2setup_ll Ddistinguish1_ll Ddistinguish2_ll.
    proc => //.
    if => //.
      (* real *)
      call Ddistinguish1_ll; call S1setup_ll; wp; skip; trivial.
      (* !real *)
      inline *.
      call Ddistinguish2_ll; call S2setup_ll; call Lsetup_ll; wp; skip; trivial.
  qed.

  lemma sseladaptiveexprom_main_ll (S1<: SSEScheme) (S2<: SSESimulator) (L<: SSELeakage) (D<: SSEDistROM):
    islossless S1.setup =>
    islossless L.leakSetup =>
    islossless S2.setup =>
    islossless D(S1).distinguish =>
    islossless D(SSESimulatorWrapper(S2, L)).distinguish =>
    islossless SSELAdaptiveSecurityROM(S1, S2, L, D).main.
  proof.
    move => S1setup_ll Lsetup_ll S2setup_ll Ddistinguish1_ll Ddistinguish2_ll.
    have game_ll: islossless SSELAdaptiveSecurityROM(S1, S2, L, D).game by apply (sseladaptiveexprom_game_ll S1 S2 L D).
    proc; call game_ll; rnd; skip; progress; apply (dboolE predT).
  qed.

  (*
   * Total probability
   * Pr[Main] = 1/2 Pr[Real] + 1/2 Pr[!Ideal]
   *)
  lemma sseladaptiveexprom_total_probability (S1<: SSEScheme) (L<: SSELeakage) (S2<: SSESimulator{L}) (D<: SSEDistROM{S1,S2,L}) &m:
    Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).main() @ &m : res] = 1%r/2%r * (Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).game(true) @ &m : res] + Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).game(false) @ &m : !res]).
  proof.
    pose prReal := Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).game(true) @ &m : res].
    pose prIdeal := Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).game(false) @ &m : !res].
    byphoare (_: (glob D, glob S1, glob S2, glob L) = (glob D, glob S1, glob S2, glob L){m} ==> _) => //; proc => //.
    seq 1: (b) (1%r/2%r) prReal (1%r/2%r) prIdeal ((glob D, glob S1, glob S2, glob L) = (glob D, glob S1, glob S2, glob L){m}).
      rnd; wp; skip; smt.
      (* post = b *)
      rnd; wp; skip; smt.
      rewrite /prReal.
        (* b *)
        call (_: (glob D, glob S1, glob S2, glob L) = (glob D, glob S1, glob S2, glob L){m} /\ real ==> res) => //; last by skip; progress; smt.
        bypr; progress; rewrite H3.
        byequiv => //.
        proc; inline *.
        rcondt{1} 1; progress.
        rcondt{2} 1; progress.
        by sim; progress; smt.
      (* post = !b *)
      rnd; wp; skip; smt.
      rewrite /prIdeal.
        (* !b *)
        call (_: (glob D, glob S1, glob S2, glob L) = (glob D, glob S1, glob S2, glob L){m} /\ !real ==> !res) => //; last by skip; progress; smt.
        bypr; progress; rewrite H3.
        byequiv => //.
        proc; inline *.
        rcondf{1} 1; progress.
        rcondf{2} 1; progress.
        sim; progress; smt.
    progress; smt.
  qed.

  (*
  *  Advantage: |2*Pr[Main] - 1| = Pr[Real] - Pr[Ideal]
  *)
  lemma sseladaptiveexprom_advantage (S1<: SSEScheme) (L<: SSELeakage) (S2<: SSESimulator{L}) (D<: SSEDistROM{S1, S2, L}) &m:
    islossless S1.setup =>
    islossless L.leakSetup =>
    islossless S2.setup =>
    islossless D(S1).distinguish =>
    islossless D(SSESimulatorWrapper(S2, L)).distinguish =>
    2%r * Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).main() @ &m : res] - 1%r =
    Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).game(true) @ &m : res] - Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).game(false) @ &m : res].
  proof.
    move => S1setup_ll Lsetup_ll S2setup_ll Ddistinguish1_ll Ddistinguish2_ll.
    pose prReal := Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).game(true) @ &m : res].
    have ->: Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).game(false) @ &m : res] = 1%r - Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).game(false) @ &m : !res].
      rewrite Pr [mu_not].
      have ->: Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).game(false) @ &m : true] = 1%r.
        byphoare => //; apply (sseladaptiveexprom_game_ll S1 S2 L D) => //.
      smt.
    pose prIdeal := Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).game(false) @ &m : !res].
    have ->: (2%r * Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).main() @ &m : res] - 1%r = prReal - (1%r - prIdeal)) = (Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).main() @ &m : res] = 1%r/2%r * (prReal + prIdeal)) by smt.
    apply (sseladaptiveexprom_total_probability S1 L S2 D &m).
  qed.

  (**
   * These are adversary wrappers that run the setup before distinguishing.
   * It can be seen as half of the experiment games.
   * It sensibly facilitates the composition of games.
   *)
  module Dsse(D: SSEDistROM, S: SSEScheme) = {
    proc distinguish(): bool = {
      var g;

      S.setup();
      g <@ D(S).distinguish();

      return g;
    }
  }.

  module Dsim(D: SSEDistROM, S: SSESimulator, L: SSELeakage) = {
    proc distinguish(): bool = {
      var g;

      SSESimulatorWrapper(S, L).setup();
      g <@ D(SSESimulatorWrapper(S, L)).distinguish();

      return g;
    }
  }.

  lemma sseexprom_dsse_left (S1<: SSEScheme) (S2<: SSEScheme) (D<: SSEDistROM{S1, S2}) &m:
    Pr[SSEExpROM(S1, S2, D).game(true) @ &m : res] = Pr[Dsse(D, S1).distinguish() @ &m : res].
  proof.
    byequiv => //; proc; rcondt{1} 1; progress; sim.
  qed.

  lemma sseexprom_dsse_right (S1<: SSEScheme) (S2<: SSEScheme) (D<: SSEDistROM{S1, S2}) &m:
    Pr[SSEExpROM(S1, S2, D).game(false) @ &m : res] = Pr[Dsse(D, S2).distinguish() @ &m : res].
  proof.
    byequiv => //; proc; rcondf{1} 1; progress; sim.
  qed.

  lemma sseladaptiveexprom_dsse (S1<: SSEScheme) (L<: SSELeakage) (S2<: SSESimulator{L}) (D<: SSEDistROM{S1, S2, L}) &m:
    Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).game(true) @ &m : res] = Pr[Dsse(D, S1).distinguish() @ &m : res].
  proof.
    byequiv => //; proc; rcondt{1} 1; progress; sim.
  qed.

  lemma sseladaptiveexprom_dsim (S1<: SSEScheme) (L<: SSELeakage) (S2<: SSESimulator{L}) (D<: SSEDistROM{S1, S2, L}) &m:
    Pr[SSELAdaptiveSecurityROM(S1, S2, L, D).game(false) @ &m : res] = Pr[Dsim(D, S2, L).distinguish() @ &m : res].
  proof.
    byequiv => //; proc; rcondf{1} 1; progress; sim.
  qed.

end SearchableSymmetricEncryption.
