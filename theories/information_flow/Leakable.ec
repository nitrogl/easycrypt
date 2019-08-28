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

require import SmtMap.

(* -------------------------------------------------------------------- *)
(*
 * This is different from Known|Unkown flags you can read in crypto/rom/PROM.
 * Secret and Unknown should both model confidentiality when it holds, but
 * Leaked does not mean Known, but that it is partially known.
 *)
type confidentiality = [ SECRET | LEAKED ].
type 'a leakable = 'a * ('a distr) option * confidentiality.

op is_secret ['a] (v: 'a leakable) = SECRET = v.`3.
op is_leaked ['a] (v: 'a leakable) = !(is_secret v).
op inst ['a] (v: 'a leakable) = v.`1.
op (|) ['a] (v: 'a leakable) (d: 'a distr) = v.`2 = Some d. (* equality can be too strong, but should be alright for now *)

op vget ['a] (olx: ('a leakable) option) = inst (oget olx).

op v_eq   ['a] (v w: 'a leakable) = v.`1 = w.`1.
op d_eq   ['a] (v w: 'a leakable) = v.`2 = w.`2.
op vd_eq  ['a] (v w: 'a leakable) = (v.`1, v.`2) = (w.`1, w.`2).
op ov_eq  ['a] (v w: ('a leakable) option) = (oget v).`1 = (oget w).`1.
op od_eq  ['a] (v w: ('a leakable) option) = (oget v).`2 = (oget w).`2.
op ovd_eq ['a] (v w: ('a leakable) option) = ((oget v).`1, (oget v).`2) = ((oget w).`1, (oget w).`2).

abbrev (==)  (v w: ('a leakable) option) = ov_eq v w.
abbrev (===) (v w: ('a leakable) option) = ovd_eq v w.
abbrev (=|=) (v w: ('a leakable) option) = od_eq v w.

(* -------------------------------------------------------------------- *)
(* This can be used in proofs when convenient *)
op undeclassify_invariant_fmap ['a, 'b] (l m: ('a, 'b leakable) fmap) =
     (forall x, dom l x => dom m x /\ l.[x] === m.[x] )
  /\ (forall x, dom l x => is_leaked (oget m.[x]) => l.[x] = m.[x])
  /\ (forall x, !dom l x => dom m x => is_secret (oget m.[x]))
.
