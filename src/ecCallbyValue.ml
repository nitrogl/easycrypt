open EcUtils
open EcTypes
open EcEnv
open EcFol
open EcReduction

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
  Format.eprintf "eq_simpl@.";
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
  Format.eprintf "get_simpl@.";
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
  Format.eprintf "set_simpl@.";
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

type stack =
    (* [] *)
  | Sempty
    (* [] ? f1 : f2 *)
  | Sif       of subst * form * form * stack
  | Sif1      of subst * form * form * stack
  | Sif2      of         form * form * stack
  | Slet      of subst * lpattern * form * stack
  | Sapp_arg  of subst * form * form list * form list * ty * stack
    (* [] f1...fn *)
  | Sapp_fun  of form list * ty * stack
    (* (f1..[] .. fn) *)
  | Stuple    of subst * form list * form list * stack
    (* [].`i *)
  | Sproj     of int * ty * stack
  (* TODO add stack for XXhoare; equiv; eager; pr *)

let hd_rev l =
  match List.rev l with
  | a :: rl -> a, rl
  | _ -> assert false

(* Warning : the state should contains value of variables in hyps *)

let rec cbv (st:state) (s:subst) (head:form) (stk:stack) : form =
  Format.eprintf "cbv@.";
  match head.f_node, stk with
  (* Contextual rules *)
  | Fif (f, f1, f2), _ ->
    cbv st s f (Sif(s, f1, f2, stk))
  | Flet (p, fx, fin), _ ->
    cbv st s fx (Slet(s, p, fin, stk))
  | Fapp(f, args), _ ->
    let an, rargs = hd_rev args in
    cbv st s an (Sapp_arg(s, f, rargs, [], head.f_ty, stk))
  | Ftuple args, _ ->
    let an, rargs = hd_rev args in
    cbv st s an (Stuple(s, rargs, [], stk))
  | Fproj (f, i), _ ->
    cbv st s f (Sproj(i, head.f_ty, stk))
  (* β-reduction, perform here also to avoid subst *)
  | Fquant(Llambda, bd, f), Sapp_fun(args, ty, stk) when st.st_ri.beta ->
    betared st s bd f args ty stk
  (* δ-reduction *)
  | Fop (p, tys), _ when st.st_ri.delta_p p && Op.reducible st.st_env p->
    let f = Op.reduce st.st_env p tys in
    cbv st subst_id f stk

  (* ------------------------- *)
  | _ ->
    let head = subst s head in
    let head =
      match head.f_node with
      (* μ-reduction *)
      | Fglob (mp, m) when st.st_ri.modpath ->
        EcEnv.NormMp.norm_glob st.st_env m mp
      (* μ-reduction *)
      | Fpvar (pv, m) when st.st_ri.modpath ->
        let pv' = EcEnv.NormMp.norm_pvar st.st_env pv in
        f_pvar pv' head.f_ty m
      | _ -> head in
    head_red st head stk

and betared st s bd f args ty stk =
  Format.eprintf "beta@.";
  match bd, args with
  | [], [] -> cbv st s f stk
  | _, []  -> cbv st s (f_quant Llambda bd f) stk
  | [], _  -> cbv st s f (Sapp_fun(args, ty, stk))
  | (x,GTty _)::bd, v::args ->
    let s = bind_local s x v in
    betared st s bd f args ty stk
  | _::_, _::_ -> assert false

and head_red st hd stk =
  Format.eprintf "head red@.";
  match hd.f_node, stk with
  | _, Sempty -> hd

  (* ι-reduction (if-then-else) *)
  | _, Sif (s, f1, f2, stk) ->
    Format.eprintf "Sif@.";
    if st.st_ri.iota && f_equal hd f_true then cbv st s f1 stk
    else if st.st_ri.iota && f_equal hd f_false then cbv st s f2 stk
    else cbv st s f2 (Sif1(s,hd,f1,stk))

  | _, Sif1(s,f,f1,stk) ->
    Format.eprintf "Sif1@.";
    cbv st s f1 (Sif2(f,hd,stk))

  | _, Sif2(f,f2,stk) ->
    Format.eprintf "Sif2@.";
    let hd =
      if st.st_ri.iota then f_if_simpl f hd f2
      else f_if f hd f2 in
    head_red st hd stk

  (* ι-reduction (tuples projection) *)
  | _, Sproj(i, ty, stk) ->
    Format.eprintf "Sproj@.";
    let hd =
      if st.st_ri.iota then f_proj_simpl hd i ty
      else f_proj hd i ty in
    head_red st hd stk

  (* ζ-reduction *)
  | _, Slet(s, LSymbol(x,_), f, stk) when st.st_ri.zeta ->
    Format.eprintf "red Slet@.";
    let s = bind_local s x hd in
    cbv st s f stk

  (* ζ-reduction *)
  | Ftuple es, Slet(s, LTuple ids, f, stk) when st.st_ri.zeta ->
    Format.eprintf "Slet tuple@.";
    let s = bind_locals s ids es in
    cbv st s f stk

  | _, Slet(s, p, f, stk) ->
    Format.eprintf "Slet nored@.";
    let f = subst s f in
    head_red st (f_let p hd f) stk

  (* β-reduction *)
  | Fquant(Llambda, bd, f), Sapp_fun(args, ty, stk) when st.st_ri.beta ->

    betared st subst_id bd f args ty stk

  (* logical reduction *)
  | Fop(p,tys), Sapp_fun(args, ty, stk)
      when is_some st.st_ri.logic && is_logical_op p ->
     Format.eprintf "logical red @.";
     let pcompat =
       match oget st.st_ri.logic with `Full -> true | `ProductCompat -> false
     in
     let f =
       match op_kind p, args with
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
       | _, _ -> f_app hd args ty in
     head_red st f stk

  (* FIXME add reduction rule for fix *)
  | _, Sapp_fun(args, ty, stk) ->
    head_red st (f_app hd args ty) stk

  (* Contextual rules *)
  | _, Sapp_arg(s, f, a::rargs, args, ty, stk) ->
    cbv st s a (Sapp_arg(s, f, rargs, hd::args, ty, stk))

  | _, Sapp_arg(s, f, [], args, ty, stk) ->
    cbv st s f (Sapp_fun(hd::args, ty, stk))

  | _, Stuple(s, a::rargs, args, stk) ->
    cbv st s a (Stuple(s, rargs, hd::args, stk))

  | _, Stuple(_, [], args, stk) ->
    head_red st (f_tuple (hd::args)) stk

let norm_cbv (ri : reduction_info) hyps f =
  let st = {
      st_hyps = hyps;
      st_env  = LDecl.toenv hyps;
      st_ri   = ri
    } in
  cbv st subst_id f Sempty
