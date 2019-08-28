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
open EcModules
open EcFol

open EcCoreGoal
open EcLowPhlGoal

open EcTypes
open EcPath

module CI = EcCoreLib

let rec expr_to_string e = match e.e_node with (* [[remove me]] *)
  | Eint   (i) -> "Eint(" ^ (EcBigInt.to_string i) ^ ")"
  | Elocal (_) -> "Elocal"
  | Evar   (v) -> "Evar(" ^ (EcTypes.string_of_pvar v) ^ ")"
  | Eop    (p, tl) -> "Eop(" ^ (EcPath.tostring p) ^ " : " ^ (String.concat " -> " (List.map dump_ty tl)) ^ ")"
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
  | LvMap   ((p, tl), v, e, t) -> "Map[" ^ (EcPath.tostring p) ^ ":" ^ (String.concat " -> " (List.map dump_ty tl)) ^ "] of " ^ (string_of_pvar v) ^ "@{" ^ (expr_to_string e) ^ ": " ^ (dump_ty t) ^ "}"

(* -------------------------------------------------------------------- *)

let dump_tys tl = String.concat " -> " (List.map dump_ty tl)

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
let destr_expr_appmap e : expr * prog_var = (* [[move me to ecTypes?]] *)
  let module E = struct exception Abort end in
  match e.e_node with
  | Eapp (e, vl) when List.length vl = 2
      -> (List.nth vl 1, destr_var (List.nth vl 0))
  | _ -> raise E.Abort
  
(* -------------------------------------------------------------------- *)
let destr_tuple e : expr list = (* [[move me to ecTypes?]] *)
  let module E = struct exception Abort end in
  match e.e_node with
  | Etuple es -> es
  | _ -> raise E.Abort

(* -------------------------------------------------------------------- *)
let destr_tuple_proj e i : expr = (* [[move me to ecTypes?]] *)
  let module E = struct exception Abort end in
  match e.e_node with
  | Etuple es -> List.nth es i
  | _ -> raise E.Abort

(* -------------------------------------------------------------------- *)
let destr_proj e : expr * int = (* [[move me to ecTypes?]] *)
  let module E = struct exception Abort end in
  match e.e_node with
  | Eproj (e, i) -> (e, i)
  | _ -> raise E.Abort

(* -------------------------------------------------------------------- *)
let destr_app e : expr list = (* [[move me to ecTypes?]] *)
  let module E = struct exception Abort end in
  match e.e_node with
  | Eapp (e, el) -> e::el
  | _ -> raise E.Abort

(* -------------------------------------------------------------------- *)
module LowInternal = struct
  exception No_wp

  let wp_asgn_aux m lv e (lets, f) =
    let let1 = lv_subst m lv (form_of_expr m e) in
      (let1::lets, f)

  let rec wp_stmt onesided env m (stmt: EcModules.instr list) letsf =
    match stmt with
    | [] -> stmt, letsf
    | i :: stmt' ->
        try
          let letsf = wp_instr onesided env m i letsf in
          wp_stmt onesided env m stmt' letsf
        with No_wp -> (stmt, letsf)

  and wp_instr onesided env m i letsf =
    match i.i_node with
    | Sasgn (lv,ex) ->
  Printf.printf "assign lvalue is: %s %s\n" (lvalue_to_string lv) (EcPath.tostring (psymbol (symbol_of_lv lv)));
  Printf.printf "assign rvalue is: %s\n" (expr_to_string ex);
  (match lv with
  | LvMap((p,tys), v, e, t) -> 
      Printf.printf "map types for set: %s\n" (String.concat " -> " (List.map dump_ty tys));
      (*
      let map_lv = List.nth (destr_app (fst (destr_proj (destr_tuple_proj ex 0)))) 1 in
  Printf.printf "\n extracted: %s : %s\n" (expr_to_string map_lv) (dump_ty map_lv.e_ty);
      let mapty, xty, mty = destr_ty_map map_lv in
      let e, v = destr_expr_appmap map_lv in

      let mlv = LvMap((CI.CI_FMap.p_set, tys), v, e, mapty) in
      Printf.printf "\n ---- lveq : %s\n\n" (if (lv_equal lv mlv) then "true" else "false")
      *)
  | _ -> Printf.printf "");
        wp_asgn_aux m lv ex letsf

    | Sif (e,s1,s2) ->
        let r1,letsf1 = wp_stmt onesided env m (List.rev s1.s_node) letsf in
        let r2,letsf2 = wp_stmt onesided env m (List.rev s2.s_node) letsf in
        if List.is_empty r1 && List.is_empty r2 then begin
          let post1 = mk_let_of_lv_substs env letsf1 in
          let post2 = mk_let_of_lv_substs env letsf2 in
          let post  = f_if (form_of_expr m e) post1 post2 in
            ([], post)
        end else raise No_wp

    | Sassert e when onesided ->
        let phi = form_of_expr m e in
        let lets,f = letsf in
        (lets, EcFol.f_and_simpl phi f)

    | _ -> raise No_wp
end

let wp ?(uselet=true) ?(onesided=false) env m s post =
  let r,letsf =
    LowInternal.wp_stmt onesided env m (List.rev s.s_node) ([],post)
  in
  let pre = mk_let_of_lv_substs ~uselet env letsf in
  (List.rev r, pre)

(* -------------------------------------------------------------------- *)
module TacInternal = struct
  let check_wp_progress tc i (_s : stmt) rm =
    if EcUtils.is_some i && not (List.is_empty rm) then
      tc_error !!tc "remaining %i instruction(s)" (List.length rm)

  let t_hoare_wp ?(uselet=true) i tc =
    let env = FApi.tc1_env tc in
    let hs = tc1_as_hoareS tc in
    let (s_hd, s_wp) = o_split i hs.hs_s in
    let m = EcMemory.memory hs.hs_m in
    let s_wp = EcModules.stmt s_wp in
    let (s_wp, post) = wp ~uselet ~onesided:true env m s_wp hs.hs_po in
    check_wp_progress tc i hs.hs_s s_wp;
    let s = EcModules.stmt (s_hd @ s_wp) in
    let concl = f_hoareS_r { hs with hs_s = s; hs_po = post} in
    FApi.xmutate1 tc `Wp [concl]

  let t_bdhoare_wp ?(uselet=true) i tc =
    let env = FApi.tc1_env tc in
    let bhs = tc1_as_bdhoareS tc in
    let (s_hd, s_wp) = o_split i bhs.bhs_s in
    let s_wp = EcModules.stmt s_wp in
    let m = EcMemory.memory bhs.bhs_m in
    let s_wp,post = wp ~uselet env m s_wp bhs.bhs_po in
    check_wp_progress tc i bhs.bhs_s s_wp;
    let s = EcModules.stmt (s_hd @ s_wp) in
    let concl = f_bdHoareS_r { bhs with bhs_s = s; bhs_po = post} in
    FApi.xmutate1 tc `Wp [concl]

  let t_equiv_wp ?(uselet=true) ij tc =
    let env = FApi.tc1_env tc in
    let es = tc1_as_equivS tc in
    let i = omap fst ij and j = omap snd ij in
    let s_hdl,s_wpl = o_split i es.es_sl in
    let s_hdr,s_wpr = o_split j es.es_sr in
    let meml, s_wpl = EcMemory.memory es.es_ml, EcModules.stmt s_wpl in
    let memr, s_wpr = EcMemory.memory es.es_mr, EcModules.stmt s_wpr in
    let post = es.es_po in
    let s_wpl, post = wp ~uselet env meml s_wpl post in
    let s_wpr, post = wp ~uselet env memr s_wpr post in
    check_wp_progress tc i es.es_sl s_wpl;
    check_wp_progress tc j es.es_sr s_wpr;
    let sl = EcModules.stmt (s_hdl @ s_wpl) in
    let sr = EcModules.stmt (s_hdr @ s_wpr) in
    let concl = f_equivS_r {es with es_sl = sl; es_sr=sr; es_po = post} in
    FApi.xmutate1 tc `Wp [concl]
end

(* -------------------------------------------------------------------- *)
let t_wp_r ?(uselet=true) k g =
  let module T = TacInternal in

  let (th, tbh, te) =
    match k with
    | None -> (Some (T.t_hoare_wp   ~uselet None),
               Some (T.t_bdhoare_wp ~uselet None),
               Some (T.t_equiv_wp   ~uselet None))

    | Some (Single i) -> (Some (T.t_hoare_wp   ~uselet (Some i)),
                          Some (T.t_bdhoare_wp ~uselet (Some i)),
                          None (* ------------------- *))

    | Some (Double (i, j)) ->
        (None, None, Some (T.t_equiv_wp ~uselet (Some (i, j))))

  in
    t_hS_or_bhS_or_eS ?th ?tbh ?te g

let t_wp ?(uselet=true) = FApi.t_low1 "wp" (t_wp_r ~uselet)
