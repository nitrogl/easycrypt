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
open EcFol
open EcModules

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal
open EcPhlAuto

(* -------------------------------------------------------------------- *)
type ll_strategy =
  | LL_WP
  | LL_RND
  | LL_CALL
  | LL_JUMP
  | LL_COND of ll_strategy list pair

(* -------------------------------------------------------------------- *)
let rec ll_strategy_of_stmt (s : stmt) =
  List.rev_map ll_strategy_of_instr s.s_node

and ll_strategy_of_instr (i : instr) =
  match i.i_node with
  | Sasgn _ -> LL_WP
  | Srnd  _ -> LL_RND
  | Scall _ -> LL_CALL

  | Sif (_, s1, s2) ->
      LL_COND (ll_strategy_of_stmt s1, ll_strategy_of_stmt s2)

  | _ -> LL_JUMP

(* -------------------------------------------------------------------- *)
let ll_trivial = EcPhlAuto.t_pl_trivial ~bases:["random"]

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
      @~ FApi.t_on1 (-1) ~ttout:ll_trivial t_id

  | LL_CALL ->
         EcPhlCall.t_bdhoare_call f_true f_true None
      @~ FApi.t_swap_goals 0 1

  | LL_JUMP ->
        ( EcPhlApp.t_bdhoare_app
           (-1) (f_true, f_true, f_r1, f_r1, f_r0, f_r1)

        @~ FApi.t_onalli (function
           | 1 -> t_id
           | 2 -> t_id
           | _ -> t_close t_auto))

        @~ FApi.t_rotate `Left 1

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
let t_lossless1_r tc =
  let lls = ll_strategy_of_stmt (tc1_as_bdhoareS tc).bhs_s in

  let tt =
    (  apply_ll_strategy lls
    @~ FApi.t_onall (FApi.t_try EcPhlSkip.t_skip))
    @~ FApi.t_onall (EcLowGoal.t_crush ~delta:true) in

  let tactic =
    (EcPhlConseq.t_bdHoareS_conseq f_true f_true
        @~ FApi.t_on1 (-1) ~ttout:ll_trivial
             (EcPhlConseq.t_bdHoareS_conseq_bd FHeq f_r1))
        @~ FApi.t_on1 (-1) ~ttout:ll_trivial
             tt

  in FApi.t_onall ll_trivial (tactic tc)

(* -------------------------------------------------------------------- *)
let t_lossless_r =
     FApi.t_try EcPhlFun.t_bdhoareF_fun_def
  @! t_lossless1_r
  @! FApi.t_do `Maybe None
      (FApi.t_seq EcPhlFun.t_bdhoareF_fun_def t_lossless1_r)

(* -------------------------------------------------------------------- *)
let t_lossless = FApi.t_low0 "lossless" t_lossless_r
