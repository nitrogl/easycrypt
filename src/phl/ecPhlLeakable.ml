(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 * Copyright (c) - 2018 - Roberto Metere <r.metere2@ncl.ac.uk>
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcTypes
open EcEnv
open EcDecl
open EcModules

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module Sid = EcIdent.Sid
module CI = EcCoreLib

(* -------------------------------------------------------------------- *)
let path_to_expr path env =
  let module E = struct exception Abort end in
  let opkind = (Op.by_path path env).op_kind in
  match opkind with
  | OB_oper(Some (OP_Plain(e))) -> e
  | _ -> raise E.Abort

(* -------------------------------------------------------------------- *)
let t_hoare_declassify_r tc =
  let concl = FApi.tc1_goal tc in
  let hs = tc1_as_hoareS tc in
  let (lv, leakable), s = tc1_last_secasgn tc hs.hs_s in
  FApi.xmutate1 tc `SecAsgn [concl]

(* -------------------------------------------------------------------- *)
let t_equiv_declassify_sided_r side tc =
  let module E = struct exception Abort end in

  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let m, s =
    match side with
    | `Left  -> es.es_ml, es.es_sl
    | `Right -> es.es_mr, es.es_sr
  in
  let (lv, rv), s' = tc1_last_secasgn tc s in
  let ty = proj_leakable_ty env (rv.e_ty) in
  let e_inst_op = path_to_expr CI.CI_Leakable.p_inst env in (* of type leakable['a] -> 'a *)
  let e_inst = e_app e_inst_op [rv] ty in (* of type Top.Y[] *)
  let e_leaked = path_to_expr CI.CI_Leakable.p_min_leakage env in
(*   Printf.printf "%s\n" (dump_ty e_inst.e_ty); *)
  let assignment = s_asgn (lv, e_tuple [e_inst; e_leaked]) in
  let s' = s_seq s' assignment in
  let rv = EcFol.form_of_expr (EcMemory.memory m) rv in
  let declassification = f_is_leaked ty rv in
  let post = es.es_po in
(*   let assignment = lv_subst m lv in *)
(*   let assignment = mk_let_of_lv_substs ~uselet:false env ([], post) in *)
(*   let assignment = f_eq assignment assignment in *)
(*   let post = f_andas [declassification; post] in *)
  
  Printf.printf "%d\n" (tc1_pos_last_secasgn tc s);
  
  let concl =
    match side with
    | `Left  -> f_equivS_r { es with es_ml = m; es_sl=s'; es_po=post; }
    | `Right -> f_equivS_r { es with es_mr = m; es_sr=s'; es_po=post; }
  in
  FApi.xmutate1 tc `SecAsgn [concl]

(* -------------------------------------------------------------------- *)
let t_equiv_declassify_unsided_r tc =
  let module E = struct exception Abort end in

  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  
  let post = es.es_po in
  let post = f_andas [post; post] in
  
  let concl = f_equivS_r { es with es_po=post; } in
  FApi.xmutate1 tc `SecAsgn [concl]

(* -------------------------------------------------------------------- *)
let t_equiv_declassify_r side tc =
  match side with
  | Some side -> t_equiv_declassify_sided_r side tc
  | None -> t_equiv_declassify_unsided_r tc

(* -------------------------------------------------------------------- *)
let t_hoare_declassify   = FApi.t_low0 "hoare-declassify"   t_hoare_declassify_r
(* let t_bdhoare_declassify = FApi.t_low0 "bdhoare-declassify" t_bdhoare_declassify_r *)
let t_equiv_declassify   = FApi.t_low1 "equiv-declassify"   t_equiv_declassify_r

(* -------------------------------------------------------------------- *)
let process_declassify side tc =
  let concl = FApi.tc1_goal tc in

  match side with
  | None when is_hoareS concl ->
      t_hoare_declassify tc

(*   | None when is_bdHoareS concl -> *)
(*       t_bdhoare_declassify tc *)

  | _ when is_equivS concl ->
      t_equiv_declassify side tc

  | _ -> tc_error !!tc "invalid arguments"