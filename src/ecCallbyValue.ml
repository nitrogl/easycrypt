open EcUtils
open EcIdent
open EcPath
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcReduction

module BI = EcBigInt

type state = {
    st_ri    : reduction_info;
    st_env   : LDecl.hyps;
    st_subst : f_subst;
  }

type stack =
    (* [] *)
  | Sempty
    (* [] ? f1 : f2 *)
  | Sif       of state * form * form * stack
  | Slet      of state * lpattern * form * stack
  | Sapp_arg  of state * form * form list * form list * stack
    (* [] f1...fn *)
  | Sapp_fun  of form list * stack
    (* (f1..[] .. fn) *)
  | Stuple    of state * form list * form list * stack
    (* [].`i *)
  | Sproj     of int * stack
  (* TODO add stack for XXhoare; equiv; eager; pr *)

let hd_rev l =
  match List.rev l with
  | a :: rl -> a, rl
  | _ -> assert false

let rec cbv (st:state) (head:form) (stk:stack) =
  match head.f_node with
  (* Contextual rules *)
  | Fif (f, f1, f2) ->
    cbv st f (Sif st f1 f2 stk)
  | Flet (p, fx, fin) ->
    cbv st fx (Slet_x st fin stk)
  | Fapp(f, args) ->
    let an, rargs = hd_rev args in
    cbv st an (Sapp_arg st f rargs [] stk)
  | Ftuple args ->
    let an, rargs = hd_rev args in
    cbv st an (Stuple st rargs [] stk)
  | Fproj (f, i) ->
    cbv st f (Sproj st i stk)
  (* ------------------------- *)
  | _ ->
    let head =
      match Fsubst.f_subst st.st_subst head with
      | Fglob (mp, m) when ri.modpath -> EcEnv.NormMp.norm_glob env m mp
      | Fpvar (pv, m) when ri.modpath -> EcEnv.NormMp.norm_pvar env pv
      | h -> h in
    head_red head stk

and head_red hd stk =
  match stk with
  | Sempty -> hd
  | Sif (st, f1, f2, stk) ->
    let f = f_if hd f1 f2 in
    if st.st_ri.iota then
      let fs = f_if_simpl hd f1 f2 in
      if f_equal f fs then head_read f stk
      else cbv st fs stk
  | Slet(st, LSymbol(x,_), f, stk) when st.st_ri.zeta ->
    let st = {st with st_susbt = Fsubst.f_bind_local st.st_subst x hd} in
    cbv st f stk
  (* TODO : Add other let reduction , tuple ... *)
  | Sapp_arg(st, f, a::rargs, args, stk) ->
    cbv st a (Sapp_arg(st, f, rargs, hd::args, stk))
  | Sapp_arg(st, f, [], args, stk) ->
    cbv st f (Sapp_fun(hd::args, stk))
  | Sapp_fun(args, stk) ->
    (* TODO beta *)
    assert false
  | Stuple(st,a::rargs, args, stk) ->
    cbv st a (Stuple(st, rargs, hd::args))
  | Stuple(st, [], args, stk) ->
    head_red st (f_tuple args) stk
  | Sproj(st,i,stk) ->
    let hd = if st.st_ri.iota then f_proj_simpl hd i ty else f_proj hd i ty in
    head_red hd stk
