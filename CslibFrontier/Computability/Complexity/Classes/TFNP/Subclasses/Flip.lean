/-
Copyright (c) 2026 Evelyn Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Fable 5.2
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.Completeness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Circuit `Flip` is `PLS`-complete

`Flip` [JohnsonPapadimitriouYannakakis1988] is local search with the *flip neighbourhood*: given a
cost circuit, find an input such that flipping any single bit does not decrease the cost. It is the
starting point of the reductions of [SchafferYannakakis1991] to local Max-Cut and other problems
whose neighbourhoods change one coordinate at a time.

Hardness is proved for every uniform polynomial-time local-search family `(n, N, C)` rather than
for circuit `LocalOpt` alone, so no circuit is built by hand: the cost of a gadget is a
polynomial-time function, compiled by `exists_costCodes`. The gadget has `2 * n + 1` bits
`x ++ y ++ [b]`. With `b = false`, `x` is the current vertex and `y` moves bit by bit towards the
neighbor `N x`; once `y = N x` and it is cheaper, `b` flips. With `b = true`, `y` is the current
vertex and `x` moves towards `y`; once `x = y`, `b` flips back. The cost `flipCost` orders states
by the cost of the current vertex, then by `b`, then by the remaining Hamming distance, so each of
these moves decreases it. A state that no flip improves has `b = false`, `y = N x` and
`C x ≤ C (N x)`, so `x` is a local optimum of the family
(`localOptRel_of_flipOptRel_flipCost`). This is an original presentation of the standard argument
and is not transcribed from a source.

## Main definitions

* `Cslib.Complexity.flipBit`: flip one bit of a bit string.
* `Cslib.Complexity.flipOptRel`: the search relation of a local-search family with the flip
  neighbourhood.
* `Cslib.Complexity.FlipInstance`, `Cslib.Complexity.encFlip`, `Cslib.Complexity.Flip`: circuit
  `Flip`, with the number of inputs in unary.
* `Cslib.Complexity.flipCost`: the cost of the gadget.

## Main results

* `Cslib.Complexity.flipOptRel_mem_PLS`: polynomial-time flip-neighbourhood families are in `PLS`.
* `Cslib.Complexity.localOptRel_searchReducible_Flip`: every uniform polynomial-time local-search
  family reduces to `Flip`.
* `Cslib.Complexity.Flip_searchComplete`: `Flip` is `PLS`-complete.

## References

* [D. S. Johnson, C. H. Papadimitriou, M. Yannakakis, *How easy is local
  search?*][JohnsonPapadimitriouYannakakis1988]
* [A. A. Schäffer, M. Yannakakis, *Simple local search problems that are hard to
  solve*][SchafferYannakakis1991]
-/

public section

namespace Cslib.Complexity

open Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool}

/-- The bit string `w` with bit `i` flipped; `w` itself when `i` is not a position of `w`. -/
@[expose] def flipBit (w : List Bool) (i : ℕ) : List Bool :=
  (List.range w.length).map fun j => if j = i then !w.getD j false else w.getD j false

/-- Flipping a bit preserves the length. -/
@[simp]
theorem length_flipBit (w : List Bool) (i : ℕ) : (flipBit w i).length = w.length := by
  simp [flipBit]

/-- `flipBit` replaces entry `i` by its negation. -/
theorem flipBit_eq_set (w : List Bool) (i : ℕ) : flipBit w i = w.set i (!w.getD i false) := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    have hj : j < w.length := by simpa using h1
    by_cases hji : j = i
    · subst hji
      simp [flipBit, List.getD_eq_getElem?_getD, hj]
    · simp [flipBit, hji, List.getD_eq_getElem?_getD, hj, Ne.symm hji]

/-- Flipping a bit is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_flipBit {encIn : α ↪ List Bool} {w : α → List Bool} {i : α → ℕ}
    (hw : ComputableInPolyTime w encIn encBits) (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun a => flipBit (w a) (i a)) encIn encBits := by
  unfold flipBit
  fun_prop

/-- The search relation of a local-search family with the **flip neighbourhood**: a vertex `u`
of length `n a` is a solution if flipping any single bit does not strictly decrease the cost. -/
@[expose] def flipOptRel (n : α → ℕ) (C : α × List Bool → ℕ) (a : α) (u : List Bool) : Prop :=
  u.length = n a ∧ ∀ i < n a, C (a, u) ≤ C (a, flipBit u i)

/-- The standard neighbor map for the flip neighbourhood: flip the first bit whose flip strictly
decreases the cost, or stay put if there is none. -/
@[expose] def flipStep (n : α → ℕ) (C : α × List Bool → ℕ) (p : α × List Bool) : List Bool :=
  ((List.range (n p.1)).find? fun i => decide (C (p.1, flipBit p.2 i) < C p)).elim p.2
    (flipBit p.2)

/-- The standard neighbor map preserves the length. -/
theorem preservesWidth_flipStep (n : α → ℕ) (C : α × List Bool → ℕ) :
    PreservesWidth n (flipStep n C) := by
  intro a u hu
  unfold flipStep
  cases (List.range (n a)).find? fun i => decide (C (a, flipBit u i) < C (a, u)) with
  | none => exact hu
  | some i => simpa using hu

/-- The flip-neighbourhood relation is the local-search relation of `flipStep`. -/
theorem flipOptRel_eq_localOptRel (n : α → ℕ) (C : α × List Bool → ℕ) :
    flipOptRel n C = localOptRel n (flipStep n C) C := by
  funext a u
  apply propext
  simp only [flipOptRel, localOptRel]
  refine and_congr_right fun _ => ?_
  unfold flipStep
  cases hf : (List.range (n a)).find? fun i => decide (C (a, flipBit u i) < C (a, u)) with
  | none =>
    simp only [Option.elim, le_refl, iff_true]
    intro i hi
    simpa using List.find?_eq_none.1 hf i (List.mem_range.2 hi)
  | some i =>
    have hi : i < n a := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    have hlt : C (a, flipBit u i) < C (a, u) := by simpa using List.find?_some hf
    simp only [Option.elim]
    exact ⟨fun h => absurd (h i hi) (not_le.2 hlt), fun h => absurd h (not_le.2 hlt)⟩

/-- Every flip-neighbourhood family has a local optimum. -/
theorem isTotalSearch_flipOptRel (n : α → ℕ) (C : α × List Bool → ℕ) :
    IsTotalSearch (flipOptRel n C) := by
  rw [flipOptRel_eq_localOptRel]
  exact isTotalSearch_localOptRel (preservesWidth_flipStep n C)

/-- Every uniform polynomial-time local-search family with the flip neighbourhood is in `PLS`. -/
theorem flipOptRel_mem_PLS {n : α → ℕ} {C : α × List Bool → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hC : ComputableInPolyTime C (encPair enc encBits) encNat) : flipOptRel n C ∈ PLS enc := by
  rw [flipOptRel_eq_localOptRel]
  refine localOptRel_mem_PLS hn ?_ hC (preservesWidth_flipStep n C)
  unfold flipStep
  fun_prop

/-! ### Circuit `Flip` -/

/-- An instance of **circuit `Flip`**: a cost circuit on `inputs` input bits. -/
structure FlipInstance where
  /-- The number of input bits. -/
  inputs : ℕ
  /-- The code of the cost circuit; its outputs are read as a binary number. -/
  cost : CircuitCode

/-- Instances of `Flip` are encoded as the number of inputs in unary followed by the circuit
code. -/
enc_structure encFlip : FlipInstance where
  inputs : encUnary, cost : encCode

attribute [fun_prop] encFlip_inputs_polyTime encFlip_cost_polyTime encFlip_mk_polyTime

/-- **Circuit `Flip`** [JohnsonPapadimitriouYannakakis1988]: given a cost circuit, find an input
such that flipping any single bit does not strictly decrease the cost
`binaryValue (evalCircuitOutputs cost ·)`. -/
@[expose] def Flip : FlipInstance → List Bool → Prop :=
  flipOptRel FlipInstance.inputs fun p => binaryValue (evalCircuitOutputs p.1.cost p.2)

/-- Circuit `Flip` is total. -/
theorem isTotalSearch_Flip : IsTotalSearch Flip := isTotalSearch_flipOptRel _ _

/-- Circuit `Flip` is in `PLS`. -/
theorem Flip_mem_PLS : Flip ∈ PLS encFlip :=
  flipOptRel_mem_PLS (by fun_prop) (by fun_prop)

/-! ### Hardness -/

/-- The number of positions of `y` at which `y` and `z` differ. -/
@[expose] def hammingDiff (y z : List Bool) : ℕ :=
  ((List.range y.length).map fun i => if y.getD i false = z.getD i false then 0 else 1).sum

/-- The cost of the flip gadget for a local-search family `(n, N, C)`, on strings `x ++ y ++ [b]`
with `x` and `y` of length `n a`. With `b = false`, `x` is the current vertex and `y` moves towards
its neighbor `N (a, x)`; with `b = true`, `y` is the current vertex and `x` moves towards `y`. The
cost orders states by the cost of the current vertex, then by `b`, then by the remaining
distance. -/
@[expose] def flipCost (n : α → ℕ) (N : α × List Bool → List Bool) (C : α × List Bool → ℕ)
    (p : α × List Bool) : ℕ :=
  if p.2.getD (2 * n p.1) false = true then
    (2 * C (p.1, (p.2.drop (n p.1)).take (n p.1)) + 1) * (n p.1 + 1) +
      hammingDiff (p.2.take (n p.1)) ((p.2.drop (n p.1)).take (n p.1))
  else
    2 * C (p.1, p.2.take (n p.1)) * (n p.1 + 1) +
      hammingDiff ((p.2.drop (n p.1)).take (n p.1)) (N (p.1, p.2.take (n p.1)))

/-- The cost of the flip gadget is computable in polynomial time. -/
theorem flipCost_polyTime {n : α → ℕ} {N : α × List Bool → List Bool} {C : α × List Bool → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hN : ComputableInPolyTime N (encPair enc encBits) encBits)
    (hC : ComputableInPolyTime C (encPair enc encBits) encNat) :
    ComputableInPolyTime (flipCost n N C) (encPair enc encBits) encNat := by
  unfold flipCost hammingDiff
  fun_prop

/-- The bits of `flipBit w i`. -/
theorem getD_flipBit (w : List Bool) (i j : ℕ) :
    (flipBit w i).getD j false =
      if j = i ∧ j < w.length then !w.getD j false else w.getD j false := by
  rw [flipBit_eq_set]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hji : i = j
  · subst hji
    by_cases hj : i < w.length <;> simp [hj]
  · simp [hji, Ne.symm hji]

/-- Flipping a bit of the first part of an append. -/
theorem flipBit_append_left (x l : List Bool) {i : ℕ} (hi : i < x.length) :
    flipBit (x ++ l) i = flipBit x i ++ l := by
  simp [flipBit_eq_set, hi, List.getD_eq_getElem?_getD, List.getElem?_append]

/-- Flipping a bit of the second part of an append. -/
theorem flipBit_append_right (x l : List Bool) {m : ℕ} (hx : x.length = m) (i : ℕ) :
    flipBit (x ++ l) (m + i) = x ++ flipBit l i := by
  subst hx
  simp [flipBit_eq_set, List.getD_eq_getElem?_getD, List.getElem?_append]

/-- Two strings differ in at most as many positions as the first has. -/
theorem hammingDiff_le (y z : List Bool) : hammingDiff y z ≤ y.length := by
  unfold hammingDiff
  calc _ ≤ ((List.range y.length).map fun _ => 1).sum :=
        List.sum_le_sum fun i _ => by split <;> simp
    _ = y.length := by simp

/-- Flipping a position at which `y` and `z` differ brings `y` closer to `z`. -/
theorem hammingDiff_flipBit_lt {y z : List Bool} {j : ℕ} (hj : j < y.length)
    (hne : y.getD j false ≠ z.getD j false) : hammingDiff (flipBit y j) z < hammingDiff y z := by
  unfold hammingDiff
  rw [length_flipBit]
  refine List.sum_lt_sum _ _ (fun i _ => ?_) ⟨j, List.mem_range.2 hj, ?_⟩
  · by_cases hij : i = j
    · subst hij
      rw [ite_eq_right_of_eq_false _ _ (eq_false hne)]
      split_ifs <;> omega
    · have e : (flipBit y j).getD i false = y.getD i false := by
        rw [getD_flipBit]
        exact ite_eq_right_of_eq_false _ _ (eq_false fun h => hij h.1)
      rw [e]
  · have hb : (flipBit y j).getD j false = z.getD j false := by
      rw [getD_flipBit, ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, hj⟩)]
      revert hne
      cases y.getD j false <;> cases z.getD j false <;> simp
    rw [ite_eq_left_of_eq_true _ _ (eq_true hb), ite_eq_right_of_eq_false _ _ (eq_false hne)]
    exact Nat.zero_lt_one

private theorem exists_getD_ne {y z : List Bool} (h : y.length = z.length) (hne : y ≠ z) :
    ∃ j < y.length, y.getD j false ≠ z.getD j false := by
  by_contra H
  push Not at H
  refine hne (List.ext_getElem h fun i h1 h2 => ?_)
  simpa [List.getD_eq_getElem?_getD, h1, h2] using H i h1

private theorem flipCost_append (n : α → ℕ) (N : α × List Bool → List Bool)
    (C : α × List Bool → ℕ) {a : α} {x y : List Bool} (b : Bool) (hx : x.length = n a)
    (hy : y.length = n a) :
    flipCost n N C (a, x ++ (y ++ [b])) =
      if b = true then (2 * C (a, y) + 1) * (n a + 1) + hammingDiff x y
      else 2 * C (a, x) * (n a + 1) + hammingDiff y (N (a, x)) := by
  have h1 : (x ++ (y ++ [b])).getD (2 * n a) false = b := by
    simp [List.getD_eq_getElem?_getD, hx, hy, two_mul]
  have h2 : (x ++ (y ++ [b])).take (n a) = x := List.take_left' hx
  have h3 : ((x ++ (y ++ [b])).drop (n a)).take (n a) = y := by
    rw [List.drop_left' hx, List.take_left' hy]
  simp only [flipCost, h1, h2, h3]

private theorem le_of_flipCost_le {n : α → ℕ} {N : α × List Bool → List Bool}
    {C : α × List Bool → ℕ} (hlen : PreservesWidth n N) {a : α} {x y : List Bool} {b : Bool}
    (hx : x.length = n a) (hy : y.length = n a)
    (hopt : ∀ i < 2 * n a + 1, flipCost n N C (a, x ++ (y ++ [b])) ≤
      flipCost n N C (a, flipBit (x ++ (y ++ [b])) i)) :
    C (a, x) ≤ C (a, N (a, x)) := by
  have hmode := hopt (n a + n a) (by omega)
  have hb : flipBit (y ++ [b]) (n a) = y ++ [!b] := by
    have h := flipBit_append_right y [b] hy 0
    rw [Nat.add_zero] at h
    rw [h]
    cases b <;> rfl
  rw [flipBit_append_right x _ hx, hb] at hmode
  rw [flipCost_append n N C b hx hy, flipCost_append n N C (!b) hx hy] at hmode
  cases b with
  | false =>
    have hyN : y = N (a, x) := by
      by_contra hne
      obtain ⟨j, hj, hd⟩ := exists_getD_ne (hy.trans (hlen a x hx).symm) hne
      have h := hopt (n a + j) (by omega)
      rw [flipBit_append_right x _ hx, flipBit_append_left y _ hj,
        flipCost_append n N C false hx hy,
        flipCost_append n N C false hx ((length_flipBit y j).trans hy)] at h
      have := hammingDiff_flipBit_lt hj hd
      simp only [Bool.false_eq_true, ite_false] at h
      omega
    simp only [Bool.false_eq_true, ite_false, Bool.not_false, ite_true] at hmode
    rw [← hyN]
    by_contra hlt
    have h3 : (2 * C (a, y) + 2) * (n a + 1) ≤ 2 * C (a, x) * (n a + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 := hammingDiff_le x y
    nlinarith
  | true =>
    exfalso
    simp only [ite_true, Bool.not_true, Bool.false_eq_true, ite_false] at hmode
    by_cases hxy : x = y
    · subst hxy
      have h4 := hammingDiff_le x (N (a, x))
      nlinarith
    · obtain ⟨j, hj, hd⟩ := exists_getD_ne (hx.trans hy.symm) hxy
      have h := hopt j (by omega)
      rw [flipBit_append_left x _ hj, flipCost_append n N C true hx hy,
        flipCost_append n N C true ((length_flipBit x j).trans hx) hy] at h
      have := hammingDiff_flipBit_lt hj hd
      simp only [ite_true] at h
      omega

/-- A local optimum of the flip gadget has, as its first block, a local optimum of the family. -/
theorem localOptRel_of_flipOptRel_flipCost {n : α → ℕ} {N : α × List Bool → List Bool}
    {C : α × List Bool → ℕ} (hlen : PreservesWidth n N) {a : α} {s : List Bool}
    (h : flipOptRel (fun a => 2 * n a + 1) (flipCost n N C) a s) :
    localOptRel n N C a (s.take (n a)) := by
  obtain ⟨hs, hopt⟩ := h
  replace hs : s.length = 2 * n a + 1 := hs
  replace hopt : ∀ i < 2 * n a + 1, flipCost n N C (a, s) ≤ flipCost n N C (a, flipBit s i) := hopt
  have hx : (s.take (n a)).length = n a := by simp [hs]; omega
  have hy : ((s.drop (n a)).take (n a)).length = n a := by simp [hs]; omega
  have hlast : (s.drop (n a)).drop (n a) = [s.getD (2 * n a) false] := by
    have h2 : 2 * n a < s.length := by omega
    rw [List.drop_drop, ← two_mul, List.drop_eq_getElem_cons h2, List.drop_of_length_le (by omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  have hdecomp : s = s.take (n a) ++ ((s.drop (n a)).take (n a) ++ [s.getD (2 * n a) false]) := by
    rw [← hlast, List.take_append_drop, List.take_append_drop]
  rw [hdecomp] at hopt
  exact ⟨hx, le_of_flipCost_le hlen hx hy hopt⟩

/-- A uniform polynomial-time local-search family reduces to circuit `Flip`: the instance is the
compiled cost circuit of the flip gadget on `2 * n a + 1` bits, and the solution is the first
`n a` bits of a local optimum. -/
theorem localOptRel_searchReducible_Flip {n : α → ℕ} {N : α × List Bool → List Bool}
    {C : α × List Bool → ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (hN : ComputableInPolyTime N (encPair enc encBits) encBits)
    (hC : ComputableInPolyTime C (encPair enc encBits) encNat) (hlen : PreservesWidth n N) :
    SearchReducible enc encFlip (localOptRel n N C) Flip := by
  have hn' : ComputableInPolyTime (fun a => 2 * n a + 1) enc encUnary := by fun_prop
  obtain ⟨code, hcode, hsem⟩ := exists_costCodes hn' (flipCost_polyTime hn hN hC)
  refine SearchReducible.of_isTotalSearch isTotalSearch_Flip
    (f := fun a => ⟨2 * n a + 1, code a⟩) (g := fun p => p.2.take (n p.1)) (by fun_prop)
    (by fun_prop) fun a s hw => ?_
  obtain ⟨hs, hopt⟩ := hw
  refine localOptRel_of_flipOptRel_flipCost hlen ⟨hs, fun i hi => ?_⟩
  simpa only [hsem a s hs, hsem a _ ((length_flipBit s i).trans hs)] using hopt i hi

/-- **Circuit `Flip` is complete for `PLS`** under polynomial-time search reductions
[JohnsonPapadimitriouYannakakis1988]. -/
theorem Flip_searchComplete : SearchComplete @PLS encFlip Flip := by
  refine ⟨Flip_mem_PLS, fun _ enc R hR => ?_⟩
  obtain ⟨-, n, N, C, hn, hN, hC, hlen, hred⟩ := mem_PLS.mp hR
  exact hred.trans (localOptRel_searchReducible_Flip hn hN hC hlen)

end Cslib.Complexity
