/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation.FiniteEncoding.Defs

/-!
# Arithmetic coordinates of compact neighborhood values

The fixed finite encoding used by the neighborhood evaluator has a simple
numeric layout:

* state one-hot bits occupy the first `|Q|` coordinates;
* head-remainder one-hot bits occupy the next `blockLength` coordinates;
* cell-symbol one-hot bits occupy the final `4 * blockLength` coordinates.

This module states that layout as a total natural-indexed Boolean function.
It is the semantic target of the fixed-register local-transition code: the
runtime can scan numeric coordinates without evaluating an input-dependent
equivalence.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace CompactValueCodeSemantics

open NeighborhoodExecutableEvaluation

/-- Numeric code of a fixed source state under the hardwired state order. -/
def stateCode
    (order : FiniteEncoding.StateOrder tm) (state : tm.Q) : ℕ :=
  (order.state state).val

/-- Numeric alphabet order `zero, one, blank, start`. -/
def gammaCode (symbol : Γ) : ℕ :=
  (FiniteEncoding.gammaEquiv symbol).val

/-- Total arithmetic Boolean coordinate of one compact value.

Coordinates beyond the payload width are false. In the cell branch, the
proof that the decoded offset lies below `blockLength` follows from the
checked upper payload bound.
-/
def coordinateBit
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (blockLength coordinate : ℕ)
    (value :
      ComputationGraph.CompactContent.Content blockLength tm.Q) : Bool :=
  let stateCount := Fintype.card tm.Q
  if coordinate < stateCount then
    decide (coordinate = stateCode order value.state)
  else if coordinate < stateCount + blockLength then
    decide
      (coordinate - stateCount = value.headRemainder.val)
  else if hcell :
      stateCount + blockLength ≤ coordinate ∧
        coordinate < stateCount + blockLength + blockLength * 4 then
    let cellCode := coordinate - (stateCount + blockLength)
    let offset : Fin blockLength :=
      ⟨cellCode / 4, by omega⟩
    decide (cellCode % 4 = gammaCode (value.cells offset))
  else
    false

end CompactValueCodeSemantics
end Runtime
end TimeSpaceSimulation
end Complexity
