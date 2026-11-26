/-
Copyright (c) 2026 Evelyn Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Fable 5.2
-/

import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.Flip

/-!
# The flip neighbourhood and the flip gadget

`flipBit` flips one position and ignores positions outside the string. For the cost "number of
`true` bits" on three bits, the all-`false` string is the only flip-optimum.

The gadget is checked on the two-vertex family with one bit, neighbor "set the bit to `false`"
and cost "the bit": vertex `[false]` is its local optimum. On gadget states `[x, y, b]`, the
state `[false, false, false]` is a flip-optimum; `[true, false, false]`, where the neighbor is
cheaper, and `[false, false, true]`, where the mode bit must flip back, are not.
-/

namespace CslibFrontierTests.Flip

open Cslib.Complexity

example : flipBit [true, false, true] 1 = [true, true, true] := by decide
example : flipBit [true, false, true] 3 = [true, false, true] := by decide

example : hammingDiff [true, false, true] [true, true, false] = 2 := by decide

/-- The number of `true` bits. -/
def ones (p : Unit × List Bool) : ℕ := p.2.count true

example : flipOptRel (fun _ : Unit => 3) ones () [false, false, false] := by
  unfold flipOptRel; decide
example : ¬flipOptRel (fun _ : Unit => 3) ones () [false, true, false] := by
  unfold flipOptRel; decide
-- A string of the wrong length is never a solution.
example : ¬flipOptRel (fun _ : Unit => 3) ones () [false, false] := by
  unfold flipOptRel; decide

/-- One-bit family: the neighbor of every vertex is `[false]`. -/
def toFalse (_ : Unit × List Bool) : List Bool := [false]

/-- One-bit family: the cost of a vertex is its bit. -/
def bitCost (p : Unit × List Bool) : ℕ := (p.2.getD 0 false).toNat

/-- The gadget cost of the one-bit family. -/
def gadget : Unit × List Bool → ℕ := flipCost (fun _ => 1) toFalse bitCost

example : gadget ((), [false, false, false]) = 0 := by decide
example : gadget ((), [true, false, false]) = 4 := by decide
example : gadget ((), [true, false, true]) = 3 := by decide
example : gadget ((), [false, false, true]) = 2 := by decide

example : flipOptRel (fun _ : Unit => 3) gadget () [false, false, false] := by
  unfold flipOptRel; decide
example : ¬flipOptRel (fun _ : Unit => 3) gadget () [true, false, false] := by
  unfold flipOptRel; decide
example : ¬flipOptRel (fun _ : Unit => 3) gadget () [false, false, true] := by
  unfold flipOptRel; decide

end CslibFrontierTests.Flip
