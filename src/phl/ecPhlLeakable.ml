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
open EcPath
open EcTypes
open EcEnv
open EcDecl
open EcModules

open EcBigInt

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module Sid = EcIdent.Sid
module CI = EcCoreLib

(* -------------------------------------------------------------------- *)
let rec expr_to_string e = match e.e_node with (* [[remove me]] *)
  | Eint   (i) -> "Eint(" ^ (EcBigInt.to_string i) ^ ")"
  | Elocal (_) -> "Elocal"
  | Evar   (v) -> "Evar(" ^ (EcTypes.string_of_pvar v) ^ ")"
  | Eop    (p, tl) -> "Eop(" ^ (EcPath.tostring p) ^ ", [" ^ (List.fold_left (^) "" (List.map ((^) ":") (List.map dump_ty tl))) ^ "])"
  | Eapp   (e, el) -> "Eapp(" ^ (expr_to_string e) ^ ", [" ^ (List.fold_left (^) "" (List.map ((^) ", ") (List.map expr_to_string el))) ^ "])"
  | Equant (_) -> "Equant"
  | Elet   (_) -> "Elet"
  | Etuple (l) -> "Etuple(" ^ (List.fold_left (^) "," (List.map expr_to_string l)) ^ ")"
  | Eif    (c, t, e) -> "Eif(" ^ (expr_to_string c) ^ ", then " ^ (expr_to_string t) ^ ", else " ^ (expr_to_string e) ^ ")"
  | Ematch (e, el, t) -> "Ematch(" ^ (expr_to_string e) ^ ", [" ^ (List.fold_left (^) " " (List.map ((^) ", ") (List.map expr_to_string el))) ^ "], type: " ^ (dump_ty t) ^ ")"
  | Eproj  (t, i) -> "Eproj(" ^ (expr_to_string t) ^ " at [" ^ (string_of_int i) ^ "])"

let lvalue_to_string lv = match lv with (* [[remove me]] *)
  | LvVar   (v, t) -> "Variable " ^ (string_of_pvar v) ^ ": " ^ (dump_ty t)
  | LvTuple (l) -> "[tuple" ^ (List.fold_left (^) ", " (List.map string_of_pvar (List.map fst l))) ^ "]"
  | LvMap   ((p, tl), v, e, t) -> "Map[" ^ (EcPath.tostring p) ^ ":" ^ (String.concat ", " (List.map dump_ty tl)) ^ "] of " ^ (string_of_pvar v) ^ "@{" ^ (expr_to_string e) ^ ": " ^ (dump_ty t) ^ "}"
  
(* -------------------------------------------------------------------- *)
let path_to_expr path env = (* [[remove me]] *)
  let module E = struct exception Abort end in
  let opkind = (Op.by_path path env).op_kind in
  match opkind with
  | OB_oper(Some (OP_Plain(e))) -> e
  | _ -> raise E.Abort

(* -------------------------------------------------------------------- *)
let destr_ty_map e : ty * ty * ty = (* [[move me to ecTypes?]] *)
  let module E = struct exception Abort end in
  match e.e_node with
  | Eapp (e, _) -> (match e.e_node with
    | Eop (op, tl) when List.length tl = 2
        -> (match e.e_ty.ty_node with
           | Tfun(mty, _) -> (mty, List.nth tl 0, List.nth tl 1)
           | _ -> raise E.Abort)
    | _ -> raise E.Abort)
  | _ -> raise E.Abort

(* -------------------------------------------------------------------- *)
let destr_op_map e : path = (* [[move me to ecTypes?]] *)
  let module E = struct exception Abort end in
  match e.e_node with
  | Eapp (e, _) -> (match e.e_node with
    | Eop (op, _) -> op
    | _ -> raise E.Abort)
  | _ -> raise E.Abort

(* -------------------------------------------------------------------- *)
let destr_map e : expr * prog_var = (* [[move me to ecTypes?]] *)
  let module E = struct exception Abort end in
  match e.e_node with
  | Eapp (e, vl) when List.length vl = 2
      -> (List.nth vl 1, destr_var (List.nth vl 0))
  | _ -> raise E.Abort

(* -------------------------------------------------------------------- *)
(* ------------------- Declassification (</) -------------------------- *)
(* -------------------------------------------------------------------- *)

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
  
  let (lv, leakable), s' = tc1_last_secasgn tc s in
  let ty_leakable = proj_leakable_ty env (e_ty leakable) in
  
  (* Assignment from the instance value of the leakable entry *)
  let e_inst = e_proj leakable 0 ty_leakable in
  let assignment = s_asgn (lv, e_inst) in
  
  (* Flag the map value as "LEAKED" *)
  let map_lv = List.nth (snd (split_args leakable)) 0 in
  let mapty, xty, mty = destr_ty_map map_lv in
  let ex, vm = destr_map map_lv in
  
  let e_distr = e_proj leakable 1 ty_leakable in
  let e_leaked = e_op CI.CI_Leakable.p_leaked [] tconfidentiality in
(*   let e_leaked = e_proj leakable 2 ty_leakable in *)
  
(* LvMap (op, m, x, ty)
 * - op is the map-set operator
 * - m  is the map to be updated
 * - x  is the index to update
 * - ty is the type of the value [m]
  | LvMap((p,tys),pv,e,ty) ->
    let set = f_op p tys (toarrow [ty; e.e_ty; f.f_ty] ty) in
    let f   = f_app set [f_pvar pv ty m; form_of_expr m e; f] ty in
    LvVar(pv,ty), m, f
    *)
  let p_set = destr_op_map map_lv in
  let mlv = LvMap((p_set, [xty; mty]), vm, ex, mapty) in
  let et = e_tuple [e_inst; e_distr; e_leaked] in
  let declassification = s_asgn (lv, et) in
  
  (*
    | LvMap ((p, tys), pv, e', ty) ->
        let mtype = toarrow [ty; e'.e_ty; e.e_ty] ty in
        let set   = e_op p tys mtype in
        let e     = e_app set [e_var pv ty; e'; e] ty in
        sp_asgn mem env (LvVar (pv, ty)) e (bds, assoc, pre)
   *)     
        
  Printf.printf "assign lvalue is: %s %s\n" (lvalue_to_string mlv) (EcPath.tostring (psymbol (symbol_of_lv mlv)));
  Printf.printf "ex: %s\n" (expr_to_string et);
  
  (* Build up the mutation *)
  let s' = s_seq s' declassification in
  let s' = s_seq s' assignment in
  let post = es.es_po in
  
  let concl =
    match side with
    | `Left  -> f_equivS_r { es with es_ml = m; es_sl=s'; es_po=post; }
    | `Right -> f_equivS_r { es with es_mr = m; es_sr=s'; es_po=post; }
  in
  FApi.xmutate1 tc `SecAsgn [concl]

(* -------------------------------------------------------------------- *)
let t_equiv_declassify   = FApi.t_low1 "equiv-declassify"   t_equiv_declassify_sided_r

(* -------------------------------------------------------------------- *)
let process_declassify side tc =
  let concl = FApi.tc1_goal tc in

  match side with
  | _ when is_equivS concl ->
      t_equiv_declassify side tc

  | _ -> tc_error !!tc "conclusion is not equiv"

(* -------------------------------------------------------------------- *)
(* ------------------- Secure sampling (</$) -------------------------- *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
let t_equiv_secsample_sided_r side tc =
  let module E = struct exception Abort end in

  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let m, s =
    match side with
    | `Left  -> es.es_ml, es.es_sl
    | `Right -> es.es_mr, es.es_sr
  in
  
  let (lv, distr), s' = tc1_last_secrnd tc s in
  let dty = e_ty distr in
  let ty_distr = proj_distr_ty env dty in
  
  (* Create a variable where to save the sampled value *)
  let v = { v_name = "sv"; v_type = ty_distr } in
  let m, s = fresh_pv m v in
  let f = EcMemory.xpath m in
  let sv = EcTypes.pv_loc f s in
  let slv = LvVar(sv, ty_distr) in
  let sampling = s_rnd (slv, distr) in
  
  (* Leakable secure assignment is a (controlled) tuple assignment *)
  let ex = e_var sv ty_distr in
  let e_some = e_op CI.CI_Option.p_some [dty] (toption dty) in
  let o_distr = e_app e_some [distr] (toption dty) in
  let e_secret = e_op CI.CI_Leakable.p_secret [] tconfidentiality in
  let et = e_tuple [ex; o_distr; e_secret] in
  let assignment = s_asgn (lv, et) in
  
  Printf.printf "assign lvalue is: %s %s\n" (lvalue_to_string lv) (EcPath.tostring (psymbol (symbol_of_lv lv)));
  Printf.printf "assign rvalue is: %s\n" (expr_to_string et);
  
  let s' = s_seq s' sampling in
  let s' = s_seq s' assignment in
  let post = es.es_po in
  
  let concl =
    match side with
    | `Left  -> f_equivS_r { es with es_ml = m; es_sl=s'; es_po=post; }
    | `Right -> f_equivS_r { es with es_mr = m; es_sr=s'; es_po=post; }
  in
  FApi.xmutate1 tc `SecAsgn [concl]

(* -------------------------------------------------------------------- *)
let t_equiv_secsample   = FApi.t_low1 "equiv-secsample"   t_equiv_secsample_sided_r

(* -------------------------------------------------------------------- *)
let process_secsample side tc =
  let concl = FApi.tc1_goal tc in

  match side with

  | _ when is_equivS concl ->
      t_equiv_secsample side tc

  | _ -> tc_error !!tc "conclusion is not equiv"
