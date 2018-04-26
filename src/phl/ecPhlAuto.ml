(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcModules

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
let tc_noauto_error pf ?loc () =
  tc_error pf ?loc "nothing to automatize"

(* -------------------------------------------------------------------- *)
let t_exfalso_r tc =
  let post = tc1_get_post tc in

  FApi.t_or
    EcPhlTAuto.t_core_exfalso
    (FApi.t_seqsub
       (EcPhlConseq.t_conseq f_false post)
       [t_id; t_logic_trivial; EcPhlTAuto.t_core_exfalso])
    tc

let t_exfalso = FApi.t_low0 "exfalso" t_exfalso_r

(* -------------------------------------------------------------------- *)
let prnd_info =
  EcParsetree.PSingleRndParam f_predT

(* -------------------------------------------------------------------- *)
let t_auto_rnd_hoare_r tc =
  EcPhlRnd.t_hoare_rnd tc

(* -------------------------------------------------------------------- *)
let t_auto_rnd_bdhoare_r tc =
  let hs = tc1_as_bdhoareS tc in

  match List.olast hs.bhs_s.s_node with
  | Some { i_node = Srnd _ } -> EcPhlRnd.t_bdhoare_rnd prnd_info tc
  | _ -> tc_noauto_error !!tc ()

(* -------------------------------------------------------------------- *)
let t_auto_rnd_equiv_r tc =
  let env = FApi.tc1_env tc in
  let es  = tc1_as_equivS tc in

  let tl  = List.olast es.es_sl.s_node |> omap i_node in
  let tr  = List.olast es.es_sr.s_node |> omap i_node in

  match tl, tr with
  | Some (Srnd (_, e1)), Some (Srnd (_, e2)) ->
      if   EcReduction.EqTest.for_type env e1.e_ty e2.e_ty
      then EcPhlRnd.wp_equiv_rnd None tc
      else tc_noauto_error !!tc ()

  | Some (Srnd _), _ -> EcPhlRnd.wp_equiv_disj_rnd `Left  tc
  | _, Some (Srnd _) -> EcPhlRnd.wp_equiv_disj_rnd `Right tc

  | _, _ -> tc_noauto_error !!tc ()

(* -------------------------------------------------------------------- *)
let t_auto_rnd_hoare   = FApi.t_low0 "auto-rnd-hoare"   t_auto_rnd_hoare_r
let t_auto_rnd_bdhoare = FApi.t_low0 "auto-rnd-bdhoare" t_auto_rnd_bdhoare_r
let t_auto_rnd_equiv   = FApi.t_low0 "auto-rnd-equiv"   t_auto_rnd_equiv_r

(* -------------------------------------------------------------------- *)
let t_auto_rnd =
  t_hS_or_bhS_or_eS
    ~th:t_auto_rnd_hoare
    ~tbh:t_auto_rnd_bdhoare
    ~te:t_auto_rnd_equiv

(* -------------------------------------------------------------------- *)
let rec t_auto_phl_r tc =
  FApi.t_seqs
    [ EcPhlWp.t_wp None;
      FApi.t_ors [ FApi.t_seq t_auto_rnd t_auto_phl_r;
                   EcPhlSkip.t_skip;
                   t_id ]]
    tc

let t_auto_phl = FApi.t_low0 "auto-phl" t_auto_phl_r

(* -------------------------------------------------------------------- *)
let t_auto_r tc =
  let subtc =
    FApi.t_ors [ EcPhlTAuto.t_hoare_true;
                 EcPhlTAuto.t_core_exfalso;
                 EcPhlPr.t_prbounded false;
                 t_auto_phl ]
  in
  FApi.t_try
    (FApi.t_seqs [ FApi.t_try (t_assumption `Conv);
                   t_progress t_id;
                   FApi.t_try (t_assumption `Conv);
                   subtc; t_logic_trivial])
    tc

let t_auto = FApi.t_low0 "auto" t_auto_r

(* -------------------------------------------------------------------- *)
let t_phl_trivial_r tc =
  let subtc =
    FApi.t_ors [ EcPhlTAuto.t_hoare_true;
                 EcPhlTAuto.t_core_exfalso;
                 EcPhlPr.t_prbounded false;
                 EcPhlSkip.t_skip ]
  in FApi.t_try subtc tc

(* -------------------------------------------------------------------- *)
let t_phl_trivial = FApi.t_low0 "phl-trivial" t_phl_trivial_r

(* -------------------------------------------------------------------- *)
type ll_strategy =
  LL_WP | LL_RND | LL_CALL | LL_COND of ll_strategy list pair

exception NoLLStrategy

let rec ll_strategy_of_stmt (s : stmt) =
  List.rev_map ll_strategy_of_instr s.s_node

and ll_strategy_of_instr (i : instr) =
  match i.i_node with
  | Sasgn _ -> LL_WP
  | Srnd  _ -> LL_RND
  | Scall _ -> LL_CALL

  | Sif (_, s1, s2) ->
      LL_COND (ll_strategy_of_stmt s1, ll_strategy_of_stmt s2)

  | _ -> raise NoLLStrategy

(* -------------------------------------------------------------------- *)
let rec apply_ll_strategy (lls : ll_strategy list) tc =
  match lls with
  | [] ->
      t_id tc

  | lls1 :: lls ->
      FApi.t_last (apply_ll_strategy lls) (apply_ll_strategy1 lls1 tc)

and apply_ll_strategy1 (lls : ll_strategy) tc =
  tc |> match lls with

  | LL_WP ->
      EcPhlWp.t_wp (Some (Single (-1)))

  | LL_RND ->
         EcPhlRnd.t_bdhoare_rnd PNoRndParams
      @> EcPhlConseq.t_bdHoareS_conseq f_true f_true
      @~ FApi.t_on1 (-1) ~ttout:t_trivial t_id

  | LL_CALL ->
         EcPhlCall.t_bdhoare_call f_true f_true None
      @~ FApi.t_swap_goals 0 1

  | LL_COND (lls1, lls2) ->
      let condtc =
        EcPhlCond.t_bdhoare_cond
        @+ [apply_ll_strategy lls1; apply_ll_strategy lls2]
      in

        ( EcPhlApp.t_bdhoare_app
           (-1) (f_true, f_true, f_r1, f_r1, f_r0, f_r1)

        @~ FApi.t_onalli (function
           | 1 -> t_id
           | 2 -> condtc
           | _ -> t_close t_auto))

        @~ FApi.t_rotate `Left 1

(* -------------------------------------------------------------------- *)
let t_lossless_r tc =
  let lls = ll_strategy_of_stmt (tc1_as_bdhoareS tc).bhs_s in

  let tt =
    (  apply_ll_strategy lls
    @~ FApi.t_onall (FApi.t_try EcPhlSkip.t_skip))
    @~ FApi.t_onall (EcLowGoal.t_crush ~delta:true) in

  let tactic =
    (EcPhlConseq.t_bdHoareS_conseq f_true f_true
        @~ FApi.t_on1 (-1) ~ttout:t_trivial
             (EcPhlConseq.t_bdHoareS_conseq_bd FHeq f_r1))
        @~ FApi.t_on1 (-1) ~ttout:t_trivial
             tt

  in FApi.t_onall t_trivial (tactic tc)

(* -------------------------------------------------------------------- *)
let t_lossless = FApi.t_low0 "lossless" t_lossless_r
