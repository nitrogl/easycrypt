(* --------------------------------------------------------------------
 * Copyright (c) - 2018 - Roberto Metere <r.metere2@ncl.ac.uk>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Core Int IntDiv IntExtra List FSet SmtMap.
require import ListExt SmtMapExt.
require (*--*) FinType.

type D.

clone import FinType as PermutationDomain with
  type t  <- D
rename "enum" as "enumD"
rename "card" as "cardD".

(*
 * --------------------------------------------------------------------
 *                        Permutations
 * --------------------------------------------------------------------
 * Derangements are permutations with no fixed points.
 *)
op permute ['a] (s: 'a list) (A: 'a fset) = perm_eq s (elems A).
op are_permutations ['a] (s1 s2: 'a list) = permute s1 (oflist s2).
abbrev (>-<) ['a] (s1 s2: 'a list) = are_permutations s1 s2.
op are_derangements ['a] (s1 s2: 'a list) = s1 >-< s2 /\ forall n, 0 <= n < size s1 => nth witness s1 n <> nth witness s2 n.
abbrev (><) ['a] (s1 s2: 'a list) = are_derangements s1 s2.

(* As functions *)
pred is_permutation (f: 'a -> 'a) = bijective f.
pred is_derangement (f: 'a -> 'a) = is_permutation f /\ forall x, f x <> x.

(*
 * --------------------------------------------------------------------
 *               Chauchy Notation of Permutations
 * --------------------------------------------------------------------
 * Permutations can be represented with explicit substitutions.
 *
 * With this notation we do NOT establish any ordering of elements. Therefore,
 * we call sigma-list every list of pairs that are interpretable as substituting pairs.
 * Then, we define sigma-equivalence of sigma-lists as equivalence of their substitution maps.
 *)
pred is_substitution ['a] (sigma: ('a, 'a) fmap) = elems (fdom sigma) >-< elems (frng sigma).
op list2sigma (s: ('a * 'a) list) =
  with s = []      => empty
  with s = x :: xs => (list2sigma xs).[fst x <- snd x].
pred sigma_eq (s1 s2: ('a * 'a) list) = list2sigma s1 = list2sigma s2 /\ is_substitution (list2sigma s1).

lemma nosmt sigma_eq_subst (s1 s2: ('a * 'a) list):
  sigma_eq s1 s2 => is_substitution (list2sigma s2).
proof. rewrite /sigma_eq; move => [s1_s2 sub]; rewrite -s1_s2 sub //. qed.

(*
 * --------------------------------------------------------------------
 *               Arrangements and Circular Permutations
 * --------------------------------------------------------------------
 * 
 * We call arrangements those permutations that establish an "order" of the elements,
 * regardless of the (not necessarily existing) ordering of the set which the
 * elements of the list come from.
 *
 * For this reason, arrangements can enjoy simple list notation.
 *
 * A list can also be interpreted as a linear ordering of its elements.
 * This embraces the notion of circular permutations, where the permutation
 * itself linearly orders the set in a specific way.
 * 
 * Even if any simple list can be interpreted as such, we overload their
 * notation by calling them pi-lists.
 * Differently from pi-list notation, a corresponding circular map will
 * explicitly join the last element to the first element of the pi-list.
 * Then, we define pi-equivalence of pi-lists as single cutting and catting
 * one of the two lists such that it equals the other.
 *)
op list2pi' ['a] x0 (s: 'a list) =
  with s = []      => empty
  with s = x :: xs => (uniq s) ? (list2pi' x0 xs).[x <- (xs = []) ? x0 : head witness xs] : empty.
abbrev list2pi (s: 'a list) = list2pi' (head witness s) s.

lemma list2pi0: list2pi [<: 'a>] = empty by trivial.

lemma list2pi1 (x: 'a): list2pi [x] = empty.[x <- x] by trivial.

(*
 * The operator extract_cycle does not guarantee that the result will be a (portion of a) cycle.
 * However, if called with x = x0 of an element in a cycle, it gets the whole cycle in a list.
 *)
op extract_cycle ['a]: {
    'a -> 'a -> ('a, 'a) fmap -> 'a list
  | forall x x0 pi,
      extract_cycle x x0 pi = (dom pi x) ? let y = oget pi.[x] in
                                           (x0 = y) ? [x] (* last element of the cycle *)
                                                    : ((dom pi y) ? x :: extract_cycle y x0 (rem pi x)
                                                                  : [] (* element breaks the cycle *))
                                        : [] (* element does not belong *)
  } as extract_cycle_def.
abbrev pi2list (pi: ('a, 'a) fmap) = let x = head witness (elems (fdom pi)) in extract_cycle x x pi.

lemma pi2list0 ['a]: pi2list empty = [<: 'a>].
proof. rewrite /= /pi2list extract_cycle_def fdom0 elems_fset0 /= mem_empty emptyE //. qed.

pred pi_eq (s1 s2: 'a list) = perm_eq s1 s2 /\ uniq s1 /\ (s1 = [] \/ let i = index (head witness s1) s2 in s1 = (drop i s2) ++ (take i s2)).

pred is_circular_permutation ['a] (pi: ('a, 'a) fmap) = card (fdom pi) = size (pi2list pi).
