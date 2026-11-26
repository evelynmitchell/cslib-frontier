/-
Copyright (c) 2026 Evelyn Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Fable 5.2
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.MaxCut
public import CslibFrontier.GameTheory.Congestion.PLS
import CslibFrontier.Foundations.Data.List.Blocks
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Local Max-Cut and its reduction to congestion games

Local Max-Cut with the flip neighbourhood asks, given a weighted multigraph, for a cut whose
weight no single vertex move increases. It reduces to finding a pure Nash equilibrium of a
congestion game ([Roughgarden2013CS364A], Lecture #19, Theorem 3.1, after
[FabrikantPapadimitriouTalwar2004]): one player per vertex and two resources per edge, each
costing `0` to a single user and the edge weight to each of two users. A player chooses the first
resource of all its incident edges or the second of all of them, so an edge is charged exactly
when its endpoints make the same choice. Rosenthal's potential is then the total weight of the
non-loop edges that do not cross the cut (`potential_toCongestion_add_cutValue`), and since the
potential is exact, the equilibria are the local maxima (`pureNash_toCongestion_iff`).

## Main definitions

* `Cslib.Complexity.LocalMaxCutInstance`, `Cslib.Complexity.encLocalMaxCut`: a vertex count in
  unary and a list of `MaxCut.WeightedEdge` with binary endpoints and weights. The vertices are
  `0, …, vertices - 1`.
* `Cslib.Complexity.LocalMaxCut`: the search problem. Solutions are bit strings with one bit per
  vertex.
* `Cslib.Complexity.LocalMaxCut.toCongestion`: the congestion game of an instance. Position `j`
  of the valid edge list owns resources `2 * j` and `2 * j + 1`, so parallel edges get separate
  resources.
* `Cslib.Complexity.LocalMaxCut.cutOf`: the cut read from a profile string.

## Main statements

* `Cslib.Complexity.LocalMaxCut.potential_toCongestion_add_cutValue`: potential plus cut weight
  is the total weight of the non-loop edges.
* `Cslib.Complexity.LocalMaxCut.pureNash_toCongestion_iff`: equilibria are local maxima.
* `Cslib.Complexity.LocalMaxCut.searchReducible_pureNash`: the search reduction.
* `Cslib.Complexity.LocalMaxCut.mem_PLS`, `Cslib.Complexity.LocalMaxCut.isTotalSearch`: local
  Max-Cut is a total search problem in `PLS`.
* `Cslib.Complexity.LocalMaxCut.pureNash_searchComplete_of_searchHard`: a conditional step, not
  the completeness theorem: if local Max-Cut is `PLS`-hard ([SchafferYannakakis1991], not
  formalized), finding a pure Nash equilibrium of a congestion game is `PLS`-complete.

## Implementation notes

The vertex count is in unary because a solution has one bit per vertex: with binary endpoints and
an implicit vertex set `0, …, max endpoint`, solutions would be exponentially long in the
instance. An edge with an endpoint outside `0, …, vertices - 1` is ignored
(`LocalMaxCutInstance.validEdges`), as `CongestionCode` ignores out-of-range resource indices, so
every instance describes a graph. A self-loop never crosses a cut; in the congestion game it has
one user on one of its two resources and costs nothing.

Membership in `PLS` is obtained from the reduction and `CongestionCode.pureNash_mem_PLS`, not
from a direct local-search family for the flip neighbourhood.

## References

* [FabrikantPapadimitriouTalwar2004]
* [Roughgarden2013CS364A]
* [SchafferYannakakis1991]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime Cslib.GameTheory MaxCut

/-- An instance of **local Max-Cut**: a weighted multigraph on the vertices
`0, …, vertices - 1`. -/
structure LocalMaxCutInstance where
  /-- The number of vertices. -/
  vertices : ℕ
  /-- The weighted edges of the multigraph. -/
  edges : List WeightedEdge
  deriving DecidableEq, Repr

/-- Instances of `LocalMaxCut` are encoded as the vertex count in unary followed by the list of
weighted edges, with endpoints and weights in binary. -/
enc_structure encLocalMaxCut : LocalMaxCutInstance where
  vertices : encUnary, edges : (encList encWeightedEdge)

attribute [fun_prop] encLocalMaxCut_vertices_polyTime encLocalMaxCut_edges_polyTime
  encLocalMaxCut_mk_polyTime

namespace LocalMaxCutInstance

/-- The edges both of whose endpoints are vertices; the other edges are ignored. -/
@[expose] def validEdges (G : LocalMaxCutInstance) : List WeightedEdge :=
  G.edges.filter fun e => decide (e.u < G.vertices) && decide (e.v < G.vertices)

end LocalMaxCutInstance

namespace LocalMaxCut

/-- The side assignment of a bit string; vertices beyond its length are on side `false`. -/
@[expose] def side (w : List Bool) (v : ℕ) : Bool := w.getD v false

/-- The bit string `w` with bit `v` flipped. -/
@[expose] def flip (w : List Bool) (v : ℕ) : List Bool :=
  (List.range w.length).map fun j => if j = v then !w.getD j false else w.getD j false

/-- The weight of the cut `w` of `G`: the total weight of the valid edges whose endpoints are on
different sides. -/
@[expose] def cutValue (G : LocalMaxCutInstance) (w : List Bool) : ℕ :=
  cutWeight G.validEdges (side w)

/-- The resources player `v` uses on side `b`: resource `2 * j + b.toNat` for each position `j`
of an edge of `E` incident to `v`. -/
@[expose] def strategyOf (E : List WeightedEdge) (v : ℕ) (b : Bool) : List ℕ :=
  ((List.range E.length).filter fun j =>
    decide ((E.getD j ⟨0, 0, 0⟩).u = v) || decide ((E.getD j ⟨0, 0, 0⟩).v = v)).map
      fun j => 2 * j + b.toNat

/-- The congestion game of a local Max-Cut instance: player `v` has the strategies
`strategyOf G.validEdges v false` (index `0`) and `strategyOf G.validEdges v true` (index `1`),
and both resources of an edge of weight `w` have cost table `[0, w]`. -/
@[expose] def toCongestion (G : LocalMaxCutInstance) : CongestionCode where
  playerStrategies := (List.range G.vertices).map fun v =>
    [strategyOf G.validEdges v false, strategyOf G.validEdges v true]
  costTables := G.validEdges.flatMap fun e => [[0, e.weight], [0, e.weight]]

/-- The cut of a profile string: vertex `v` is on side `true` when player `v` plays strategy
`1`. -/
@[expose] def cutOf (G : LocalMaxCutInstance) (u : List Bool) : List Bool :=
  ((toCongestion G).decodeList u).map fun k => decide (k = 1)

/-- The verifier for `LocalMaxCut`: the string has one bit per vertex and no flip increases the
weight of the cut. -/
@[expose] def check (G : LocalMaxCutInstance) (w : List Bool) : Bool :=
  decide (w.length = G.vertices) &&
    (List.range G.vertices).all fun v => decide (cutValue G (flip w v) ≤ cutValue G w)

/-! ### Polynomial-time bounds -/

section Mixed

variable {γ : Type} {encIn : γ ↪ List Bool} {e n : γ → ℕ}

@[fun_prop]
private theorem decide_binary_lt_unary (he : ComputableInPolyTime e encIn encNat)
    (hn : ComputableInPolyTime n encIn encUnary) :
    ComputableInPolyTime (fun x => decide (e x < n x)) encIn encBool :=
  binary_lt' he (unary_to_binary.comp hn)

@[fun_prop]
private theorem decide_binary_eq_unary (he : ComputableInPolyTime e encIn encNat)
    (hn : ComputableInPolyTime n encIn encUnary) :
    ComputableInPolyTime (fun x => decide (e x = n x)) encIn encBool :=
  decide_eq' he (unary_to_binary.comp hn)

end Mixed

section PolyTime

variable {γ : Type} {encIn : γ ↪ List Bool} {G : γ → LocalMaxCutInstance} {w : γ → List Bool}
  {v : γ → ℕ}

/-- The valid edges are computable in polynomial time. -/
@[fun_prop]
theorem validEdges_polyTime (hG : ComputableInPolyTime G encIn encLocalMaxCut) :
    ComputableInPolyTime (fun x => (G x).validEdges) encIn (encList encWeightedEdge) := by
  unfold LocalMaxCutInstance.validEdges
  fun_prop

@[fun_prop]
private theorem flip_polyTime (hw : ComputableInPolyTime w encIn encBits)
    (hv : ComputableInPolyTime v encIn encUnary) :
    ComputableInPolyTime (fun x => flip (w x) (v x)) encIn encBits := by
  unfold flip
  fun_prop

private theorem side_eq_getD_min (w : List Bool) (v : ℕ) :
    side w v = w.getD (min w.length v) false := by
  unfold side
  rcases Nat.lt_or_ge v w.length with h | h
  · rw [min_eq_right h.le]
  · rw [min_eq_left h]
    simp [List.getD_eq_getElem?_getD, h]

@[fun_prop]
private theorem cutValue_polyTime (hG : ComputableInPolyTime G encIn encLocalMaxCut)
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime (fun x => cutValue (G x) (w x)) encIn encNat := by
  have h : (fun x => cutValue (G x) (w x)) = fun x => (((G x).validEdges.filter fun e =>
      (w x).getD (min (w x).length e.u) false != (w x).getD (min (w x).length e.v) false).map
        WeightedEdge.weight).sum := by
    funext x
    simp only [cutValue, cutWeight, crosses, side_eq_getD_min]
  rw [h]
  fun_prop

/-- The congestion game of an instance is computable in polynomial time. -/
@[fun_prop]
theorem toCongestion_polyTime (hG : ComputableInPolyTime G encIn encLocalMaxCut) :
    ComputableInPolyTime (fun x => toCongestion (G x)) encIn encCongestion := by
  unfold toCongestion strategyOf
  fun_prop

end PolyTime

/-- The verifier is computable in polynomial time. -/
theorem check_polyTime :
    ComputableInPolyTime (fun x : LocalMaxCutInstance × List Bool => check x.1 x.2)
      (encPair encLocalMaxCut encBits) encBool := by
  unfold check
  fun_prop

/-- The cut of a profile string is computable in polynomial time. -/
theorem cutOf_polyTime :
    ComputableInPolyTime (fun x : LocalMaxCutInstance × List Bool => cutOf x.1 x.2)
      (encPair encLocalMaxCut encBits) encBits := by
  unfold cutOf
  fun_prop

/-! ### The potential of a cut -/

/-- The profile, as strategy indices, of a cut: side `true` is strategy `1`. -/
@[expose] def profileOf (w : List Bool) : List ℕ := w.map Bool.toNat

/-- The total weight of the non-loop edges, the only ones a cut can separate. -/
@[expose] def nonLoopWeight (E : List WeightedEdge) : ℕ :=
  ((E.filter fun e => decide (e.u ≠ e.v)).map WeightedEdge.weight).sum

/-- Flipping a bit preserves the length. -/
theorem length_flip (w : List Bool) (v : ℕ) : (flip w v).length = w.length := by
  simp [flip]

/-- The congestion game has one player per vertex. -/
theorem players_toCongestion (G : LocalMaxCutInstance) :
    (toCongestion G).players = G.vertices := by
  simp [CongestionCode.players, toCongestion]

/-- Every player of the congestion game has two strategies. -/
theorem numStrategies_toCongestion (G : LocalMaxCutInstance) {v : ℕ} (hv : v < G.vertices) :
    (toCongestion G).numStrategies v = 2 := by
  simp [CongestionCode.numStrategies, CongestionCode.strategies, toCongestion, hv]

private theorem sum_map_range_two_mul (f : ℕ → ℕ) (m : ℕ) :
    ((List.range (2 * m)).map f).sum =
      ((List.range m).map fun j => f (2 * j) + f (2 * j + 1)).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, List.range_succ, List.range_succ,
      List.range_succ (n := m)]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, ih]
    omega

private theorem getElem?_flatMap_pair {α β : Type} (f : α → β) (l : List α) (j b : ℕ)
    (hb : b < 2) : (l.flatMap fun e => [f e, f e])[2 * j + b]? = l[j]?.map f := by
  induction l generalizing j with
  | nil => simp
  | cons a l ih =>
    cases j with
    | zero => interval_cases b <;> simp
    | succ j =>
      rw [show 2 * (j + 1) + b = 2 * j + b + 1 + 1 by omega]
      simpa using ih j

private theorem sum_map_filter_eq (P : WeightedEdge → Bool) (E : List WeightedEdge) :
    ((E.filter P).map WeightedEdge.weight).sum =
      ((List.range E.length).map fun j =>
        if P (E.getD j ⟨0, 0, 0⟩) then (E.getD j ⟨0, 0, 0⟩).weight else 0).sum := by
  have h : ∀ l : List WeightedEdge, ((l.filter P).map WeightedEdge.weight).sum =
      (l.map fun e => if P e then e.weight else 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => by_cases ha : P a <;> simp [ha, ih]
  rw [h]
  conv_lhs => rw [← List.map_getD_range E ⟨0, 0, 0⟩]
  rw [List.map_map]
  rfl

private theorem mem_strategyOf {E : List WeightedEdge} {v j : ℕ} {b b' : Bool} :
    2 * j + b'.toNat ∈ strategyOf E v b ↔
      j < E.length ∧ ((E.getD j ⟨0, 0, 0⟩).u = v ∨ (E.getD j ⟨0, 0, 0⟩).v = v) ∧ b' = b := by
  simp only [strategyOf, List.mem_map, List.mem_filter, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨a, ⟨ha, h⟩, heq⟩
    have hb : a = j ∧ b' = b := by
      cases b <;> cases b' <;> simp only [Bool.toNat_true, Bool.toNat_false] at heq <;>
        first | exact ⟨by omega, rfl⟩ | (exfalso; omega)
    obtain ⟨rfl, rfl⟩ := hb
    exact ⟨ha, h, rfl⟩
  · rintro ⟨ha, h, rfl⟩
    exact ⟨j, ⟨ha, h⟩, rfl⟩

private theorem countP_range_endpoints (u v n : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    (List.range n).countP (fun i => decide ((u = i ∨ v = i) ∧ Q i)) =
      (if u < n ∧ Q u then 1 else 0) + (if v < n ∧ u ≠ v ∧ Q v then 1 else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, List.countP_singleton]
    simp only [Nat.lt_succ_iff_lt_or_eq]
    by_cases hu : u = n
    · subst hu
      by_cases hv : v = u
      · subst hv
        by_cases hQ : Q v <;> simp [hQ]
      · by_cases hQu : Q u <;> by_cases hQv : Q v <;> simp [hQu, hQv, hv, Ne.symm hv, add_comm]
    · by_cases hv : v = n
      · subst hv
        by_cases hQu : Q u <;> by_cases hQv : Q v <;> simp [hQu, hQv, hu]
      · simp [hu, hv]

private theorem getD_profileOf (w : List Bool) (i : ℕ) :
    (profileOf w).getD i 0 = (side w i).toNat := by
  simp only [profileOf, side, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> rfl

private theorem load_toCongestion (G : LocalMaxCutInstance) (w : List Bool) {j : ℕ}
    (hj : j < G.validEdges.length) (b : Bool) :
    (toCongestion G).load (profileOf w) (2 * j + b.toNat) =
      (if side w (G.validEdges.getD j ⟨0, 0, 0⟩).u = b then 1 else 0) +
        (if (G.validEdges.getD j ⟨0, 0, 0⟩).u ≠ (G.validEdges.getD j ⟨0, 0, 0⟩).v ∧
          side w (G.validEdges.getD j ⟨0, 0, 0⟩).v = b then 1 else 0) := by
  have hmem : G.validEdges.getD j ⟨0, 0, 0⟩ ∈ G.validEdges := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  obtain ⟨hu, hv⟩ : (G.validEdges.getD j ⟨0, 0, 0⟩).u < G.vertices ∧
      (G.validEdges.getD j ⟨0, 0, 0⟩).v < G.vertices := by
    simpa [LocalMaxCutInstance.validEdges] using (List.mem_filter.1 hmem).2
  unfold CongestionCode.load
  rw [players_toCongestion]
  have hcongr : ∀ i ∈ List.range G.vertices,
      (decide (2 * j + b.toNat ∈ (toCongestion G).strategy i ((profileOf w).getD i 0)) = true ↔
        decide (((G.validEdges.getD j ⟨0, 0, 0⟩).u = i ∨ (G.validEdges.getD j ⟨0, 0, 0⟩).v = i) ∧
          side w i = b) = true) := by
    intro i hi
    have hi' : i < G.vertices := List.mem_range.1 hi
    have hs : (toCongestion G).strategy i ((profileOf w).getD i 0) =
        strategyOf G.validEdges i (side w i) := by
      rw [getD_profileOf]
      cases side w i <;>
        simp [CongestionCode.strategy, CongestionCode.strategies, toCongestion, hi']
    rw [hs, decide_eq_true_eq, decide_eq_true_eq, mem_strategyOf]
    simp only [hj, true_and, eq_comm]
  rw [List.countP_congr hcongr, countP_range_endpoints]
  simp only [hu, hv, true_and]

private theorem costs_toCongestion (G : LocalMaxCutInstance) {j : ℕ}
    (hj : j < G.validEdges.length) (b : Bool) :
    (toCongestion G).costs (2 * j + b.toNat) = [0, (G.validEdges.getD j ⟨0, 0, 0⟩).weight] := by
  have hb : b.toNat < 2 := by cases b <;> simp
  simp only [CongestionCode.costs, toCongestion, List.getD_eq_getElem?_getD]
  rw [getElem?_flatMap_pair (fun e : WeightedEdge => [0, e.weight]) _ _ _ hb]
  simp [List.getElem?_eq_getElem hj]

private theorem edge_identity (s : ℕ → Bool) (u v wt : ℕ) :
    ((([0, wt] : List ℕ).take ((if s u = false then 1 else 0) +
        (if u ≠ v ∧ s v = false then 1 else 0))).sum +
      (([0, wt] : List ℕ).take ((if s u = true then 1 else 0) +
        (if u ≠ v ∧ s v = true then 1 else 0))).sum) +
      (if (s u != s v) = true then wt else 0) = if decide (u ≠ v) = true then wt else 0 := by
  by_cases h : u = v
  · subst h
    cases s u <;> simp
  · cases hu : s u <;> cases hv : s v <;> simp [h]

/-- **Rosenthal's potential counts the uncut edges**: the potential of the profile of a cut plus
the weight of the cut is the total weight of the non-loop edges. -/
theorem potential_toCongestion_add_cutValue (G : LocalMaxCutInstance) (w : List Bool) :
    (toCongestion G).potential (profileOf w) + cutValue G w = nonLoopWeight G.validEdges := by
  have hres : (toCongestion G).resources = 2 * G.validEdges.length := by
    simp [CongestionCode.resources, toCongestion, List.length_flatMap, Nat.mul_comm]
  unfold CongestionCode.potential cutValue cutWeight nonLoopWeight
  rw [hres, sum_map_range_two_mul, sum_map_filter_eq, sum_map_filter_eq, ← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have hj' : j < G.validEdges.length := List.mem_range.1 hj
  have h0 := load_toCongestion G w hj' false
  have h1 := load_toCongestion G w hj' true
  have c0 := costs_toCongestion G hj' false
  have c1 := costs_toCongestion G hj' true
  simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero] at h0 h1 c0 c1
  rw [h0, h1, c0, c1]
  exact edge_identity (side w) _ _ _

private theorem updateProfile_flip (w : List Bool) (i : ℕ) :
    CongestionCode.updateProfile (profileOf w) i (!side w i).toNat = profileOf (flip w i) := by
  apply List.ext_getElem
  · simp [CongestionCode.updateProfile, profileOf, flip]
  · intro j h1 h2
    have hj : j < w.length := by simpa [CongestionCode.updateProfile, profileOf] using h1
    by_cases hji : j = i
    · subst hji
      simp [CongestionCode.updateProfile, profileOf, flip, side]
    · simp [CongestionCode.updateProfile, profileOf, flip, hji, hj, List.getD_eq_getElem?_getD]

private theorem updateProfile_self (p : List ℕ) (i : ℕ) :
    CongestionCode.updateProfile p i (p.getD i 0) = p := by
  apply List.ext_getElem
  · simp [CongestionCode.updateProfile]
  · intro j h1 h2
    by_cases hji : j = i
    · subst hji
      simp [CongestionCode.updateProfile, List.getD_eq_getElem?_getD, h2]
    · simp [CongestionCode.updateProfile, hji, List.getD_eq_getElem?_getD, h2]

/-- The cut of a profile string has one bit per vertex. -/
theorem length_cutOf (G : LocalMaxCutInstance) (u : List Bool) :
    (cutOf G u).length = G.vertices := by
  simp [cutOf, CongestionCode.decodeList, players_toCongestion]

/-- The cut read from a profile string has the decoded profile as its profile. -/
theorem profileOf_cutOf (G : LocalMaxCutInstance) (u : List Bool) :
    profileOf (cutOf G u) = (toCongestion G).decodeList u := by
  have hlt : ∀ k ∈ (toCongestion G).decodeList u, k < 2 := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
    rw [List.mem_range, players_toCongestion] at hi
    exact (numStrategies_toCongestion G hi) ▸ (toCongestion G).clampStrategy_lt i _
  unfold profileOf cutOf
  rw [List.map_map]
  conv_rhs => rw [← List.map_id ((toCongestion G).decodeList u)]
  refine List.map_congr_left fun k hk => ?_
  have := hlt k hk
  interval_cases k <;> rfl

end LocalMaxCut

/-- **Local Max-Cut** with the flip neighbourhood: `w` assigns a side to each of the vertices
`0, …, G.vertices - 1`, and moving any single vertex to the other side does not increase the
weight of the cut. -/
@[expose] def LocalMaxCut (G : LocalMaxCutInstance) (w : List Bool) : Prop :=
  w.length = G.vertices ∧
    ∀ v < G.vertices, LocalMaxCut.cutValue G (LocalMaxCut.flip w v) ≤ LocalMaxCut.cutValue G w

namespace LocalMaxCut

/-- A profile string of the congestion game of `G` is a pure Nash equilibrium exactly when it has
the right length and the cut it decodes to is a local maximum. -/
theorem pureNash_toCongestion_iff (G : LocalMaxCutInstance) (u : List Bool) :
    CongestionCode.PureNash (toCongestion G) u ↔
      u.length = (toCongestion G).vertexLength ∧ LocalMaxCut G (cutOf G u) := by
  have key : ∀ v, (toCongestion G).potential (profileOf (cutOf G u)) ≤
      (toCongestion G).potential (profileOf (flip (cutOf G u) v)) ↔
        cutValue G (flip (cutOf G u) v) ≤ cutValue G (cutOf G u) := by
    intro v
    have h1 := potential_toCongestion_add_cutValue G (cutOf G u)
    have h2 := potential_toCongestion_add_cutValue G (flip (cutOf G u) v)
    omega
  rw [CongestionCode.pureNash_iff, ← profileOf_cutOf, players_toCongestion]
  refine and_congr_right fun _ => ⟨fun h => ⟨length_cutOf G u, fun v hv => (key v).1 ?_⟩,
    fun h i hi k hk => ?_⟩
  · rw [← updateProfile_flip]
    exact h v hv _ (by rw [numStrategies_toCongestion G hv]; cases side (cutOf G u) v <;> simp)
  · rw [numStrategies_toCongestion G hi] at hk
    have hk' : k = (profileOf (cutOf G u)).getD i 0 ∨ k = (!side (cutOf G u) i).toNat := by
      rw [getD_profileOf]
      cases side (cutOf G u) i <;> simp <;> omega
    rcases hk' with rfl | rfl
    · rw [updateProfile_self]
    · rw [updateProfile_flip]
      exact (key i).2 (h.2 i hi)

/-- Local Max-Cut is a total search problem: a pure Nash equilibrium of the congestion game
decodes to a local maximum. -/
theorem isTotalSearch : IsTotalSearch LocalMaxCut := fun G =>
  let ⟨u, hu⟩ := CongestionCode.pureNash_mem_TFNP.2 (toCongestion G)
  ⟨cutOf G u, ((pureNash_toCongestion_iff G u).1 hu).2⟩

/-- Local Max-Cut is in `FNP`: solutions have one bit per vertex and `check` verifies them. -/
theorem mem_FNP : LocalMaxCut ∈ FNP encLocalMaxCut := by
  have hn : ComputableInPolyTime (fun G : LocalMaxCutInstance => G.vertices) encLocalMaxCut
      encUnary := by fun_prop
  obtain ⟨p, hp⟩ := (polyBounded hn).exists_polynomial
  refine ⟨⟨p, fun G w h => h.1 ▸ hp G⟩, fun x => check x.1 x.2, check_polyTime, fun G w => ?_⟩
  simp [LocalMaxCut, check]

/-- **Local Max-Cut reduces to pure Nash equilibria of congestion games**
([Roughgarden2013CS364A], Lecture #19, Theorem 3.1, after [FabrikantPapadimitriouTalwar2004]):
the instance map is `toCongestion` and the solution map is `cutOf`. -/
theorem searchReducible_pureNash :
    SearchReducible encLocalMaxCut encCongestion LocalMaxCut CongestionCode.PureNash :=
  .of_isTotalSearch CongestionCode.pureNash_mem_TFNP.2 (f := toCongestion)
    (g := fun x => cutOf x.1 x.2) (by fun_prop) cutOf_polyTime
    fun G u h => ((pureNash_toCongestion_iff G u).1 h).2

/-- Local Max-Cut is in `PLS`, through the reduction to congestion games. -/
theorem mem_PLS : LocalMaxCut ∈ PLS encLocalMaxCut :=
  searchReducible_pureNash.mem_PLS mem_FNP CongestionCode.pureNash_mem_PLS

/-- This is not the `PLS`-completeness theorem of [FabrikantPapadimitriouTalwar2004]: it assumes
that local Max-Cut is `PLS`-hard, which is the theorem of [SchafferYannakakis1991] and is not
formalized. Under that hypothesis, finding a pure Nash equilibrium of a congestion game is
`PLS`-complete. -/
theorem pureNash_searchComplete_of_searchHard
    (h : SearchHard @PLS encLocalMaxCut LocalMaxCut) :
    SearchComplete @PLS encCongestion CongestionCode.PureNash :=
  ⟨CongestionCode.pureNash_mem_PLS, h.trans searchReducible_pureNash⟩

end LocalMaxCut

end Cslib.Complexity
