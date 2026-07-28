/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComplexityBridge.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodEvaluation.Defs

/-!
# Balanced semantic time-to-space simulation

For a source time bound `T`, this module chooses the standard positive
square-root-logarithmic block length and a horizon of one more than the
quotient by that block length. The resulting two-root grouped evaluation is
the semantic output of the Williams simulation.

This is an evaluator-level definition, not yet a concrete Turing machine.

## Main definition

- `candidateSnapshot` -- two-root evaluation for one explicit trial time
- `balancedSnapshot` -- two-root evaluation at the balanced covered horizon
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodSimulation

/-- Two-root neighborhood evaluation for one explicit trial time, using the
standard balanced block length and a horizon covering that trial. -/
noncomputable def candidateSnapshot
    (tm : TM workTapeCount) (x : List Bool) (time : ℕ) :
    NeighborhoodGraph.DecisionRecovery.Snapshot tm.Q :=
  let blockLength :=
    ComplexityBridge.balancedBlockLength time
  NeighborhoodEvaluation.evaluatedDecisionSnapshot
    tm x blockLength
      (by
        unfold blockLength
        unfold ComplexityBridge.balancedBlockLength
        simp [ComplexityBridge.positiveCeilSqrt])
      (ComplexityBridge.timeBlockCount time)

/-- Specialize the explicit-trial evaluator to a supplied source time bound. -/
noncomputable def balancedSnapshot
    (tm : TM workTapeCount) (x : List Bool)
    (timeBound : ℕ → ℕ) :
    NeighborhoodGraph.DecisionRecovery.Snapshot tm.Q :=
  candidateSnapshot tm x (timeBound x.length)

end NeighborhoodSimulation

end TimeSpaceSimulation

end Complexity
