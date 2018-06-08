open EcUtils
open EcIdent
open EcTypes
open EcEnv
open EcFol
open EcReduction
open EcBaseLogic
module BI = EcBigInt

(* -------------------------------------------------------------- *)

type state = {
    st_ri    : reduction_info;
    st_hyps  : LDecl.hyps;
    st_env   : env;
  }

(* -------------------------------------------------------------- *)
type subst = f_subst

let subst_id = Fsubst.f_subst_id

let subst = Fsubst.f_subst

let bind_local = Fsubst.f_bind_local

let bind_locals s ids es =
  List.fold_left2 (fun s (x,_) e -> bind_local s x e) s ids es

(* -------------------------------------------------------------- *)

let f_ands_simpl fs =
  match List.rev fs with
  | [] -> f_true
  | [x] -> x
  | f::fs -> f_ands_simpl (List.rev fs) f

let rec f_eq_simpl st f1 f2 =
  if f_equal f1 f2 then f_true
  else match f1.f_node, f2.f_node with
  | Fapp({f_node = Fop (p1, _)}, args1),
    Fapp({f_node = Fop (p2, _)}, args2)
      when EcEnv.Op.is_dtype_ctor st.st_env p1
           && EcEnv.Op.is_dtype_ctor st.st_env p2 ->
    let idx p =
      let idx = EcEnv.Op.by_path p st.st_env in
      snd (EcDecl.operator_as_ctor idx)
    in
    if   idx p1 <> idx p2
    then f_false
    else f_ands_simpl (List.map2 (f_eq_simpl st) args1 args2)

  | Ftuple args1, Ftuple args2 ->
    f_ands_simpl (List.map2 (f_eq_simpl st) args1 args2)

  | _, _ ->
    if (EqTest.for_type st.st_env f1.f_ty EcTypes.tunit
        && EqTest.for_type st.st_env f2.f_ty EcTypes.tunit) ||
         is_alpha_eq st.st_hyps f1 f2 then
      f_true
    else EcFol.f_eq_simpl f1 f2

(* -------------------------------------------------------------- *)
let rec f_map_get_simpl st m x bty =
  match m.f_node with
  | Fapp({f_node = Fop(p,_)}, [e])
    when EcPath.p_equal p EcCoreLib.CI_Map.p_cst ->
    e

  | Fapp({f_node = Fop(p, _)}, [m'; x'; e])
    when EcPath.p_equal p EcCoreLib.CI_Map.p_set ->
    let t = f_eq_simpl st x' x in
    if f_equal t f_true then e
    else if f_equal t f_false then f_map_get_simpl st m' x bty
    else
      let m' = f_map_set_simplify st m' x in
      let m' = f_map_set m' x' e in
      f_map_get m' x bty
  | _ -> f_map_get m x bty

and f_map_set_simplify st m x =
  match m.f_node with
  | Fapp({f_node = Fop(p, _)}, [m'; x'; e])
    when EcPath.p_equal p EcCoreLib.CI_Map.p_set ->
    let t = f_eq_simpl st x' x in
    if f_equal t f_true then f_map_cst x.f_ty e
    else if f_equal t f_false then f_map_set_simplify st m' x
    else
      let m' = f_map_set_simplify st m' x in
      f_map_set m' x' e
  | _ -> m

(* -------------------------------------------------------------- *)

type args =
  | Aempty of ty
  | Aapp of form list * args

let is_Aempty = function
  | Aempty _ -> true
  | _ -> false

let mk_args args args' =
  if args = [] then args' else Aapp(args, args')

let rec get1_args = function
  | Aempty _ -> assert false
  | Aapp([], args) -> get1_args args
  | Aapp(a::args, args') -> a, mk_args args args'

let rec flatten_args = function
  | Aempty ty -> [], ty
  | Aapp(args, Aempty ty) -> args, ty
  | Aapp(args, args') ->
    let args', ty = flatten_args args' in
    args @ args', ty

(* -------------------------------------------------------------- *)

let norm_xfun st s f =
  let f  = Fsubst.subst_xpath s f in
  if st.st_ri.modpath then EcEnv.NormMp.norm_xfun st.st_env f
  else f

let norm_stmt s c = Fsubst.subst_stmt s c

let norm_me s me = Fsubst.subst_me s me

(* -------------------------------------------------------------- *)
(* FIXME : I think substitution in type is wrong *)

let rec norm st s f =
 let f = cbv st s f (Aempty (Fsubst.subst_ty s f.f_ty)) in
 norm_lambda st f

and norm_lambda (st:state) (f:form) =
  match f.f_node with
  | Fquant(Llambda, b, f) ->
    let s, b = Fsubst.add_bindings subst_id b in
    let st = {st with st_env = Mod.add_mod_binding b st.st_env } in
    let f = norm st s f in
    f_lambda b f
  | Fapp(f1,args) ->
    f_app (norm_lambda st f1) (List.map (norm_lambda st) args) f.f_ty

  | Ftuple args -> f_tuple (List.map (norm_lambda st) args)

  | Fproj (f1,i) -> f_proj (norm_lambda st f1) i f.f_ty

  | Fquant _ | Fif _ | Fmatch _
  | Flet _ | Fint _ | Flocal _
  | Fglob _ | Fpvar _ | Fop _
  | FhoareF _ | FhoareS _ | FbdHoareF _ | FbdHoareS _
  | FequivF _ | FequivS _ | FeagerF _ | Fpr _ -> f

and betared st s bd f args =
  match bd, args with
  | _, Aapp([], args) -> betared st s bd f args
  | [], _      -> cbv st s f args
  | _ , Aempty _ -> subst s (f_quant Llambda bd f)
  | (x,GTty _)::bd, Aapp(v::args, args') ->
    let s = bind_local s x v in
    betared st s bd f (Aapp(args,args'))
  | _::_, _ -> assert false


and app_red st f1 args =
  match f1.f_node, args with
  | _, Aempty _ -> f1
  (* β-reduction *)
  | Fquant(Llambda, bd, f2), _ when st.st_ri.beta ->
    betared st subst_id bd f2 args

  (* ι-reduction (records projection) *)
  | Fop (p, _), _ when st.st_ri.iota && EcEnv.Op.is_projection st.st_env p ->
    let mk, args1 = get1_args args in
    begin match mk.f_node with
    | Fapp ({ f_node = Fop (mkp, _) }, mkargs)
        when (EcEnv.Op.is_record_ctor st.st_env mkp) ->
      let v = oget (EcEnv.Op.by_path_opt p st.st_env) in
      let v = proj3_2 (EcDecl.operator_as_proj v) in
      app_red st (List.nth mkargs v) args1
    | _ ->
      let args, ty = flatten_args args in
      f_app f1 args ty
    end

  (* logical reduction *)
  | Fop(p,tys), _ when is_some st.st_ri.logic && is_logical_op p ->
    let pcompat =
      match oget st.st_ri.logic with `Full -> true | `ProductCompat -> false
    in
    let args, ty = flatten_args args in
    begin match op_kind p, args with
    | Some (`Not), [f1]    when pcompat -> f_not_simpl f1
    | Some (`Imp), [f1;f2] when pcompat -> f_imp_simpl f1 f2
    | Some (`Iff), [f1;f2] when pcompat -> f_iff_simpl f1 f2

    | Some (`And `Asym), [f1;f2] -> f_anda_simpl f1 f2
    | Some (`Or  `Asym), [f1;f2] -> f_ora_simpl f1 f2
    | Some (`And `Sym ), [f1;f2] -> f_and_simpl f1 f2
    | Some (`Or  `Sym ), [f1;f2] -> f_or_simpl f1 f2
    | Some (`Int_le   ), [f1;f2] -> f_int_le_simpl f1 f2
    | Some (`Int_lt   ), [f1;f2] -> f_int_lt_simpl f1 f2
    | Some (`Real_le  ), [f1;f2] -> f_real_le_simpl f1 f2
    | Some (`Real_lt  ), [f1;f2] -> f_real_lt_simpl f1 f2
    | Some (`Int_add  ), [f1;f2] -> f_int_add_simpl f1 f2
    | Some (`Int_opp  ), [f]     -> f_int_opp_simpl f
    | Some (`Int_mul  ), [f1;f2] -> f_int_mul_simpl f1 f2
    | Some (`Real_add ), [f1;f2] -> f_real_add_simpl f1 f2
    | Some (`Real_opp ), [f]     -> f_real_opp_simpl f
    | Some (`Real_mul ), [f1;f2] -> f_real_mul_simpl f1 f2
    | Some (`Real_inv ), [f]     -> f_real_inv_simpl f
    | Some (`Eq       ), [f1;f2] -> f_eq_simpl st f1 f2
    | Some (`Map_get  ), [f1;f2] ->
      f_map_get_simpl st f1 f2 (snd (as_seq2 tys))
    | _, _ ->
      reduce_user st (f_app f1 args ty)
    end
  (* FIXME: reduction of fixpoint *)
  | _ ->
    let args, ty = flatten_args args in
    reduce_user st (f_app f1 args ty)


and reduce_user st f =
  match reduce_user_gen (cbv_init st subst_id) st.st_ri st.st_env st.st_hyps f with
  | f -> reduce_user st f
  | exception NotReducible -> f

and cbv_init st s f =
  cbv st s f (Aempty (Fsubst.subst_ty s f.f_ty))

and cbv (st:state) (s:subst) (f:form) (args:args) : form =
  match f.f_node with
  | Fquant((Lforall | Lexists) as q, b, f) ->
    assert (is_Aempty args);
    let s, b = Fsubst.add_bindings s b in
    let st = {st with st_env = Mod.add_mod_binding b st.st_env } in
    let f = norm st s f in
    begin match q with
    | Lforall -> f_forall_simpl b f
    | Lexists -> f_exists_simpl b f
    | _       -> assert false
    end

  | Fquant(Llambda, b, f1) ->
    betared st s b f1 args

  | Fif(f,f1,f2) ->
    if st.st_ri.iota then
      let f = cbv_init st s f in
      if f_equal f f_true then cbv st s f1 args
      else if f_equal f f_false then cbv st s f2 args
      else
        (* FIXME: should we normilize f, f1 and f2 ? *)
        app_red st
          (f_if_simpl (norm_lambda st f) (norm st s f1) (norm st s f2)) args
    else
      app_red st
        (f_if (norm st s f) (norm st s f1) (norm st s f2)) args

  | Fmatch _ -> assert false

  | Flet(p, f1, f2) ->
    let f1 = cbv_init st s f1 in
    begin match p, f1.f_node with
    (* ζ-reduction *)
    | LSymbol(x,_), _ when st.st_ri.zeta ->
      let s = bind_local s x f1 in
      cbv st s f2 args
    (* ζ-reduction *)
    | LTuple ids, Ftuple es when st.st_ri.zeta ->
      let s = bind_locals s ids es in
      cbv st s f2 args
    (* FIXME: LRecord *)
    | _, _ ->
      let f1 = norm_lambda st f1 in
      let s, p = Fsubst.subst_lpattern s p in
      let f2 = norm st s f2 in
      app_red st (f_let p f1 f2) args
    end

  | Fint _ -> assert (is_Aempty args); f

  | Flocal _ -> app_red st (Fsubst.f_subst s f) args

  (* μ-reduction *)
  | Fglob _ ->
    let mp, m = destr_glob (subst s f) in
    let f =
      if st.st_ri.modpath then EcEnv.NormMp.norm_glob st.st_env m mp
      else f_glob mp m in
    app_red st f args

  (* μ-reduction *)
  | Fpvar _ ->
    let pv, m = destr_pvar (subst s f) in
    let pv =
      if st.st_ri.modpath then EcEnv.NormMp.norm_pvar st.st_env pv
      else pv in
    app_red st (f_pvar pv f.f_ty m) args

  (* δ-reduction *)
  | Fop _ -> (* FIXME maybe this should be done in app_red *)
    let f = subst s f in
    let p, tys = destr_op f in
    if  st.st_ri.delta_p p && Op.reducible st.st_env p then
      let f = Op.reduce st.st_env p tys in
      cbv st subst_id f args
    else app_red st f args

  | Fapp(f1, args1) ->
    let args1 = List.map (cbv_init st s) args1 in
    cbv st s f1 (Aapp(args1, args))

  | Ftuple args1 ->
    assert (is_Aempty args);
    f_tuple (List.map (cbv_init st s) args1)

  | Fproj(f1,i) ->
    let f1 = cbv_init st s f1 in
    let f1 =
      match f1.f_node with
      | Ftuple args when st.st_ri.iota -> List.nth args i
      | _ -> f_proj (norm_lambda st f1) i f.f_ty in
    app_red st f1 args

  | FhoareF hf ->
    assert (is_Aempty args);
    assert (not (Mid.mem mhr s.fs_mem) && not (Mid.mem mhr s.fs_mem));
    let hf_pr = norm st s hf.hf_pr in
    let hf_po = norm st s hf.hf_po in
    let hf_f  = norm_xfun st s hf.hf_f in
    f_hoareF_r { hf_pr; hf_f; hf_po }

  | FhoareS hs ->
    assert (is_Aempty args);
    assert (not (Mid.mem (fst hs.hs_m) s.fs_mem));
    let hs_pr = norm st s hs.hs_pr in
    let hs_po = norm st s hs.hs_po in
    let hs_s  = norm_stmt s hs.hs_s in
    let hs_m  = norm_me s hs.hs_m in
    f_hoareS_r { hs_pr; hs_po; hs_s; hs_m }

  | FbdHoareF hf ->
    assert (is_Aempty args);
    assert (not (Mid.mem mhr s.fs_mem) && not (Mid.mem mhr s.fs_mem));
    let bhf_pr = norm st s hf.bhf_pr in
    let bhf_po = norm st s hf.bhf_po in
    let bhf_f  = norm_xfun st s hf.bhf_f in
    let bhf_bd = norm st s hf.bhf_bd in
    f_bdHoareF_r { hf with bhf_pr; bhf_po; bhf_f; bhf_bd }

  | FbdHoareS bhs ->
    assert (is_Aempty args);
    assert (not (Mid.mem (fst bhs.bhs_m) s.fs_mem));
    let bhs_pr = norm st s bhs.bhs_pr in
    let bhs_po = norm st s bhs.bhs_po in
    let bhs_s  = norm_stmt s bhs.bhs_s in
    let bhs_bd = norm st s bhs.bhs_bd in
    let bhs_m  = norm_me s bhs.bhs_m in
    f_bdHoareS_r { bhs with bhs_m; bhs_pr; bhs_po; bhs_s; bhs_bd }

  | FequivF ef ->
    assert (is_Aempty args);
    assert (not (Mid.mem mleft s.fs_mem) && not (Mid.mem mright s.fs_mem));
    let ef_pr = norm st s ef.ef_pr in
    let ef_po = norm st s ef.ef_po in
    let ef_fl = norm_xfun st s ef.ef_fl in
    let ef_fr = norm_xfun st s ef.ef_fr in
    f_equivF_r {ef_pr; ef_fl; ef_fr; ef_po }

  | FequivS es ->
    assert (is_Aempty args);
    assert (not (Mid.mem (fst es.es_ml) s.fs_mem) &&
                not (Mid.mem (fst es.es_mr) s.fs_mem));
    let es_pr = norm st s es.es_pr in
    let es_po = norm st s es.es_po in
    let es_sl = norm_stmt s es.es_sl in
    let es_sr = norm_stmt s es.es_sr in
    let es_ml  = norm_me s es.es_ml in
    let es_mr  = norm_me s es.es_mr in
    f_equivS_r {es_ml; es_mr; es_pr; es_sl; es_sr; es_po }

  | FeagerF eg ->
    assert (is_Aempty args);
    assert (not (Mid.mem mleft s.fs_mem) && not (Mid.mem mright s.fs_mem));
    let eg_pr = norm st s eg.eg_pr in
    let eg_po = norm st s eg.eg_po in
    let eg_fl = norm_xfun st s eg.eg_fl in
    let eg_fr = norm_xfun st s eg.eg_fr in
    let eg_sl = norm_stmt s eg.eg_sl in
    let eg_sr = norm_stmt s eg.eg_sr in
    f_eagerF_r {eg_pr; eg_sl; eg_fl; eg_fr; eg_sr; eg_po }

  | Fpr pr ->
    assert (is_Aempty args);
    assert (not (Mid.mem mhr s.fs_mem));
    let pr_mem   = Fsubst.subst_m s pr.pr_mem in
    let pr_fun   = norm_xfun st s pr.pr_fun in
    let pr_args  = norm st s pr.pr_args in
    let pr_event = norm st s pr.pr_event in
    f_pr_r { pr_mem; pr_fun; pr_args; pr_event; }


(* FIXME : initialize the subst with let in hyps *)
let norm_cbv (ri : reduction_info) hyps f =
  let st = {
      st_hyps = hyps;
      st_env  = LDecl.toenv hyps;
      st_ri   = ri
    } in
  (* compute the selected delta in hyps and push it into the subst *)
  let add_hyp s (x,k) =
    match k with
    | LD_var (_, Some e) when ri.delta_h x ->
      let v = cbv_init st s e in
      bind_local s x v
    | _ -> s in
  let s =
    List.fold_left add_hyp subst_id (List.rev (LDecl.tohyps hyps).h_local) in
  norm st s f
