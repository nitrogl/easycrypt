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
let path_to_expr path env = (* [[remove me]] *)
  let module E = struct exception Abort end in
  let opkind = (Op.by_path path env).op_kind in
  match opkind with
  | OB_oper(Some (OP_Plain(e))) -> e
  | _ -> raise E.Abort

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
let destr_proj e : expr * int = (* [[move me to ecTypes?]] *)
  let module E = struct exception Abort end in
  match e.e_node with
  | Eproj (e, i) -> (e, i)
  | _ -> raise E.Abort

(* -------------------------------------------------------------------- *)
let destr_expr_pvar_appmap e : expr * prog_var = (* [[move me to ecTypes?]] *)
  let module E = struct exception Abort end in
  match e.e_node with
  | Eapp (e, vl) when List.length vl = 2
      -> (List.nth vl 1, destr_var (List.nth vl 0))
  | _ -> raise E.Abort

(* -------------------------------------------------------------------- *)
let destr_expr_appmap e : expr * expr = (* [[move me to ecTypes?]] *)
  let module E = struct exception Abort end in
  match e.e_node with
  | Eapp (e, vl) when List.length vl = 2
      -> (List.nth vl 1, List.nth vl 0)
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
let destr_and_l : form -> form list = (* [[move me to ecTypes?]] *)
  let rec destr_and_l' aux f =
    let a, af =
      try destr_and f
      with DestrError _ -> (f, f)
    in
    if (f = af) then []
    else destr_and_l' (aux @ [a]) af
  in
  destr_and_l' []

(* -------------------------------------------------------------------- *)
(* ------------------- Declassification (</) -------------------------- *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
let declassify_hoare_r s tc =
  let env = FApi.tc1_env tc in
  
  let (lv, leakable), s' = tc1_last_secasgn tc s in
  let ty_leakable = fun i -> proj_leakable_ty env i (e_ty leakable) in
  
  (* Assignment from the instance value of the leakable entry *)
  let e_inst = e_proj leakable 0 (ty_leakable 0) in
  let assignment = s_asgn (lv, e_inst) in
  
  (* Flag the map value as "LEAKED" *)
  let map_lv = List.nth (snd (split_args leakable)) 0 in
  let mapty, xty, mty = destr_ty_map map_lv in
  let e, v = destr_expr_pvar_appmap map_lv in
  
  let e_distr = e_proj leakable 1 (ty_leakable 1) in
  let e_leaked = e_op CI.CI_Leakable.p_leaked [] tconfidentiality in
(*   let e_leaked = e_proj leakable 2 (ty_leakable 2) in *)

(*   Printf.printf "map_lv = %s : %s\n" (expr_to_string map_lv) (dump_ty map_lv.e_ty); *)
  let tys = [xty; mty] in
  let mlv = LvMap((CI.CI_FMap.p_set, tys), v, e, mapty) in
(*   Printf.printf "types for map set %s \n" (dump_tys tys); *)
  let et = e_tuple [e_inst; e_distr; e_leaked] in
  let declassification = s_asgn (mlv, et) in
(*   Printf.printf "assign lvalue is: %s %s\n" (lvalue_to_string mlv) (EcPath.tostring (psymbol (symbol_of_lv mlv))); *)
(*   Printf.printf "assign rvalue is: %s\n" (expr_to_string et); *)
  
  (* Build up the mutation *)
  let s' = s_seq s' declassification in
  let s' = s_seq s' assignment in
  s'

(* -------------------------------------------------------------------- *)
let t_hoare_declassify_r tc =
  let hs = tc1_as_hoareS tc in
  let concl = f_hoareS_r { hs with hs_s=declassify_hoare_r hs.hs_s tc; } in
  FApi.xmutate1 tc `SecAsgn [concl]

(* -------------------------------------------------------------------- *)
let t_equiv_declassify_sided_r side tc =
  let es = tc1_as_equivS tc in
  let concl =
    match side with
    | `Left  ->
        f_equivS_r { es with es_sl=declassify_hoare_r es.es_sl tc; }
    | `Right ->
        f_equivS_r { es with es_sr=declassify_hoare_r es.es_sr tc; }
  in
  FApi.xmutate1 tc `SecAsgn [concl]

(* -------------------------------------------------------------------- *)
let t_equiv_declassify = FApi.t_low1 "equiv-declassify" t_equiv_declassify_sided_r
let t_hoare_declassify = FApi.t_low0 "hoare-declassify" t_hoare_declassify_r

(* -------------------------------------------------------------------- *)
let process_declassify oside tc =
  let concl = FApi.tc1_goal tc in

  match oside with
  | Some(side) when is_equivS concl ->
      t_equiv_declassify side tc
      
  | Some(_) -> tc_error !!tc "conclusion is not equiv"
      
  | None when is_hoareS concl ->
      t_hoare_declassify tc

  | None -> tc_error !!tc "conclusion is not hoare"

(* -------------------------------------------------------------------- *)
(* ------------------- Undeclassification (</) ------------------------ *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
let process_undeclassify oside tc =
  tc_error !!tc "undeclassify tactic not yet implemented"

(* -------------------------------------------------------------------- *)
(* ------------------- Secure sampling (</$) -------------------------- *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
let secrnd_hoare_r m s tc =
  let env = FApi.tc1_env tc in
  
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
  let e_sv = e_var sv ty_distr in
  let e_some = e_op CI.CI_Option.p_some [dty] (toption dty) in
  let e_odistr = e_app e_some [distr] (toption dty) in
  let e_secret = e_op CI.CI_Leakable.p_secret [] tconfidentiality in
  let et = e_tuple [e_sv; e_odistr; e_secret] in
  let assignment = s_asgn (lv, et) in
  
(*   Printf.printf "assign lvalue is: %s %s\n" (lvalue_to_string lv) (EcPath.tostring (psymbol (symbol_of_lv lv))); *)
(*   Printf.printf "assign rvalue is: %s\n" (expr_to_string et); *)
  
  (* TODO: Additionally, we need the distribution not to be a singleton *)
  
  let s' = s_seq s' sampling in
  let s' = s_seq s' assignment in
  s'

(* -------------------------------------------------------------------- *)
let t_hoare_secrnd_r tc =
  let hs = tc1_as_hoareS tc in
  let concl = f_hoareS_r { hs with hs_s=secrnd_hoare_r hs.hs_m hs.hs_s tc; } in
  FApi.xmutate1 tc `SecAsgn [concl]

(* -------------------------------------------------------------------- *)
let t_equiv_secrnd_sided_r side tc =
  let es = tc1_as_equivS tc in
  let concl =
    match side with
    | `Left  ->
        f_equivS_r { es with es_sl=secrnd_hoare_r es.es_ml es.es_sl tc; }
    | `Right ->
        f_equivS_r { es with es_sr=secrnd_hoare_r es.es_mr es.es_sr tc; }
  in
  FApi.xmutate1 tc `SecAsgn [concl]

(* -------------------------------------------------------------------- *)
let t_equiv_secrnd = FApi.t_low1 "equiv-secrnd" t_equiv_secrnd_sided_r
let t_hoare_secrnd = FApi.t_low0 "hoare-secrnd" t_hoare_secrnd_r

(* -------------------------------------------------------------------- *)
let process_secrnd oside tc =
  let concl = FApi.tc1_goal tc in

  match oside with
  | Some(side) when is_equivS concl ->
      t_equiv_secrnd side tc
      
  | Some(_) -> tc_error !!tc "conclusion is not equiv"
      
  | None when is_hoareS concl ->
      t_hoare_secrnd tc

  | None -> tc_error !!tc "conclusion is not hoare"

(* -------------------------------------------------------------------- *)
(* -------------- Secure random Assignment (</$ </ ~ </) -------------- *)
(* -------------------------------------------------------------------- *)
 
(* -------------------------------------------------------------------- *)
let t_equiv_secrndasgn_r tc =
  let module E = struct exception Abort end in
  
  let env = FApi.tc1_env tc in
  let es  = tc1_as_equivS tc in

  (* TODO: contemplate the symmetric situation *)
  let (l_lv, l_leakable), l_s = tc1_last_secasgn tc es.es_sl in
  let (r_lv, r_leakable), r_s = tc1_last_secasgn tc es.es_sr in

  let (a_lv, distr), l_s = tc1_last_secrnd tc l_s in
  let dty = e_ty distr in
  let ty_distr = proj_distr_ty env dty in
  
  let l_ty_leakable = fun i -> proj_leakable_ty env i (e_ty l_leakable) in
  let r_ty_leakable = fun i -> proj_leakable_ty env i (e_ty r_leakable) in
  
  (* Assignment from the instance value of the leakable entry *)
  let l_e_inst = e_proj l_leakable 0 (l_ty_leakable 0) in
  let l_assignment = s_secasgn (l_lv, l_leakable) in
  
(*   let r_e_inst = e_proj r_leakable 0 (r_ty_leakable 0) in *)
  let r_assignment = s_secasgn (r_lv, r_leakable) in
  
  (* Create a variable matching the value of the already filled map *)
  let v = { v_name = "v"; v_type = r_leakable.e_ty } in
  let m, s = fresh_pv es.es_ml v in
  let f = EcMemory.xpath m in
  let sv = EcTypes.pv_loc f s in
  let v = f_pvar sv v.v_type (fst m) in
  let v_mem = form_of_expr (fst es.es_mr) r_leakable in
  let eq_v_m = f_eq v v_mem in
  
  (* Then modify the sampling to the required assignment *)
  let a_e_inst = e_var sv r_leakable.e_ty in
  let a_assignment = s_asgn (a_lv, a_e_inst) in
  
  (* The precondition requires a "bridge" linking the lazily-sampled value 
   * with the eagerly-sampled value
   *)
  let l_s' = s_seq l_s a_assignment in
  let l_s' = s_seq l_s' l_assignment in
  let r_s' = s_seq r_s r_assignment in
  let pre = f_and_simpl es.es_pr eq_v_m in
  
  (*
   * In the post-condition, we need the secrndasgn_invariant_fmap to hold
   *)
  let l_map = List.nth (snd (split_args l_leakable)) 0 in
  let r_map = List.nth (snd (split_args r_leakable)) 0 in
  let _, l_e = destr_expr_appmap l_map in
  let r_idx, r_e = destr_expr_appmap r_map in
  let l_v = destr_var l_e in
  let r_v = destr_var r_e in
  let f_distr = form_of_expr (fst es.es_ml) distr in
  
  (* TODO: we should not add inv_v if it is already amongst the post *)
  let andl = destr_and_l es.es_po in
  
  let secret_v = f_is_secret (l_e_inst.e_ty) v in
  let distr_v = f_sampled_from env f_distr (form_of_expr (fst es.es_ml) l_leakable) in
  let inv_v =
(*     Printf.printf "r_idx = %s : %s\n" (expr_to_string r_idx) (dump_ty r_idx.e_ty); *)
(*     Printf.printf "l_e = %s : %s\n" (expr_to_string l_e) (dump_ty l_e.e_ty); *)
(*     Printf.printf "r_e = %s : %s\n" (expr_to_string r_e) (dump_ty r_e.e_ty); *)
(*     Printf.printf "l = %s : %s\n" (expr_to_string l_leakable) (dump_ty l_leakable.e_ty); *)
(*     Printf.printf "r = %s : %s\n" (expr_to_string r_leakable) (dump_ty r_leakable.e_ty); *)
    f_secrndasgn_invariant_fmap
      r_idx.e_ty
      (r_ty_leakable 0)
      (f_pvar l_v l_e.e_ty (fst es.es_ml))
      (f_pvar r_v r_e.e_ty (fst es.es_mr))
      f_distr
  in
  let post = f_and_simpl distr_v es.es_po in
  let post = f_and_simpl inv_v post in
  
  let secrecy = f_equivS_r { es with
(*     es_ml = m; *)
    es_sl=l_s;
    es_sr=r_s;
    es_pr=pre;
    es_po=f_and_simpl pre secret_v;
  } in
  
  let concl = f_equivS_r { es with
(*     es_ml = m; *)
    es_sl=l_s';
    es_sr=r_s';
    es_pr=pre;
    es_po=post;
  } in
  FApi.xmutate1 tc `SecAsgn [secrecy; concl]

(* -------------------------------------------------------------------- *)
let t_equiv_secrndasgn   = FApi.t_low0 "equiv-secrndasgn"   t_equiv_secrndasgn_r

(* -------------------------------------------------------------------- *)
let process_secrndasgn tc =
  let concl = FApi.tc1_goal tc in

  if is_equivS concl
  then t_equiv_secrndasgn tc
  else tc_error !!tc "conclusion is not equiv"

