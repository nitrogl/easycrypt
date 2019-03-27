(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(*
 * This file contains a formalization of leakable values
 *)

(* -------------------------------------------------------------------- *)

pragma +implicits.
pragma -oldip.

(* -------------------------------------------------------------------- *)
(*
 * This is different from Known|Unkown flags you can read in crypto/rom/PROM.
 * Secret and Unknown should both model confidentiality when it holds, but
 * Leaked does not mean Known, but that it is partially known.
 *)
type confidentiality = [ SECRET | LEAKED ].
type 'a leakable = 'a * ('a distr) option * confidentiality.

pred is_secret (v: 'a leakable) = SECRET = v.`3.
pred is_leaked (v: 'a leakable) = !(is_secret v).
op inst (v: 'a leakable) = v.`1.
pred distribution_compatible (v: 'a leakable) (d: 'a distr) = v.`2 = Some d. (* equality can be too strong, but should be alright for now *)
