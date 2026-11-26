/-
Copyright (c) 2026 Evelyn Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Fable 5.2
-/

import CslibFrontier.Computability.Complexity.Problems.LocalMaxCut

/-!
# Local Max-Cut and its congestion game

A triangle on the vertices `0, 1, 2` with edge weights `3` (between `0` and `1`), `2` (between
`1` and `2`) and `1` (between `0` and `2`). The cut `{0, 2} | {1}` has weight `5` and is a local
maximum; the cut `{0} | {1, 2}` has weight `4` and is not, because moving vertex `2` gains `1`.
In the congestion game of the triangle the first is a pure Nash equilibrium and the second is
not, and Rosenthal's potential is the weight of the uncut edges.

A second instance checks the model boundaries: a self-loop never crosses a cut, parallel edges
add their weights and get separate resources, and an edge with an endpoint that is not a vertex
is ignored.
-/

namespace CslibFrontierTests.LocalMaxCut

open Cslib.Complexity Cslib.Complexity.LocalMaxCut Cslib.GameTheory Cslib.GameTheory.CongestionCode

/-- The weighted triangle. -/
def triangle : LocalMaxCutInstance := ⟨3, [⟨0, 1, 3⟩, ⟨1, 2, 2⟩, ⟨0, 2, 1⟩]⟩

example : cutValue triangle [true, false, true] = 5 := by decide
example : cutValue triangle [true, false, false] = 4 := by decide

-- `{0, 2} | {1}` is a local maximum; `{0} | {1, 2}` is not.
example : LocalMaxCut triangle [true, false, true] := by unfold LocalMaxCut; decide
example : ¬LocalMaxCut triangle [true, false, false] := by unfold LocalMaxCut; decide

-- A string of the wrong length is never a solution.
example : ¬LocalMaxCut triangle [true, false] := by unfold LocalMaxCut; decide

-- Edge `j` owns resources `2 * j` and `2 * j + 1`; player `v` picks one of them on each incident
-- edge, the same one everywhere.
example : toCongestion triangle =
    ⟨[[[0, 4], [1, 5]], [[0, 2], [1, 3]], [[2, 4], [3, 5]]],
      [[0, 3], [0, 3], [0, 2], [0, 2], [0, 1], [0, 1]]⟩ := by decide

-- Rosenthal's potential is the weight of the uncut edges: `6 - 5` and `6 - 4`.
example : (toCongestion triangle).potential (profileOf [true, false, true]) = 1 := by decide
example : (toCongestion triangle).potential (profileOf [true, false, false]) = 2 := by decide

-- The local maximum is a pure Nash equilibrium and its profile string decodes back to it.
example : (toCongestion triangle).PureNash ((toCongestion triangle).encode [1, 0, 1]) := by
  rw [pureNash_iff]; decide
example : cutOf triangle ((toCongestion triangle).encode [1, 0, 1]) = [true, false, true] := by
  decide

-- The other cut is not an equilibrium: player `2` gains by switching.
example : ¬(toCongestion triangle).PureNash ((toCongestion triangle).encode [1, 0, 0]) := by
  rw [pureNash_iff]; decide

/-- Two vertices with a self-loop, two parallel edges and an edge to the non-vertex `7`. -/
def boundary : LocalMaxCutInstance := ⟨2, [⟨0, 0, 9⟩, ⟨0, 1, 2⟩, ⟨1, 0, 3⟩, ⟨1, 7, 5⟩]⟩

example : boundary.validEdges = [⟨0, 0, 9⟩, ⟨0, 1, 2⟩, ⟨1, 0, 3⟩] := by decide
example : nonLoopWeight boundary.validEdges = 5 := by decide

-- Separating the two vertices cuts both parallel edges and nothing else.
example : cutValue boundary [true, false] = 5 := by decide
example : cutValue boundary [true, true] = 0 := by decide
example : LocalMaxCut boundary [true, false] := by unfold LocalMaxCut; decide
example : ¬LocalMaxCut boundary [true, true] := by unfold LocalMaxCut; decide

-- The self-loop has one user on one of its resources and costs nothing.
example : (toCongestion boundary).potential (profileOf [true, false]) = 0 := by decide
example : (toCongestion boundary).potential (profileOf [true, true]) = 5 := by decide

end CslibFrontierTests.LocalMaxCut
