/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Unroll.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Unroll.Internal

/-!
# Implicit computation-graph tree instances

The executable predecessor oracle defines a semantic tree-evaluation instance
of fan-in exactly `2 * (workTapeCount + 2)`. Unrolling preserves recursive
node evaluation, and a computation node at time block `i` produces a tree of
height at most `i + 1`.

The `unroll` term is not the simulator's representation. It certifies the
mathematical tree while the eventual Turing machine traverses predecessor
paths on demand.

## Main theorems

- `value_unroll` -- tree evaluation agrees with recursive graph semantics
- `height_unroll_le_rank` -- tree height is at most node rank
- `height_unroll_computation_le` -- a time-block `i` root has height at most
  `i + 1`
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

variable {workTapeCount : ℕ} {V : Type*}

/-- Evaluating the unrolled tree agrees with recursive computation-graph
semantics. -/
theorem value_unroll
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → ℕ →
      (Fin (2 * (workTapeCount + 2)) → V) → V)
    (node : Node workTapeCount) :
    (unroll tm x blockLength sourceValue combine node).value =
      nodeValue tm x blockLength sourceValue combine node :=
  Internal.value_unroll_internal
    tm x blockLength sourceValue combine node

/-- The unrolled tree's height is bounded by its root node's rank. -/
theorem height_unroll_le_rank
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → ℕ →
      (Fin (2 * (workTapeCount + 2)) → V) → V)
    (node : Node workTapeCount) :
    (unroll tm x blockLength sourceValue combine node).height ≤
      node.rank :=
  Internal.height_unroll_le_rank_internal
    tm x blockLength sourceValue combine node

/-- A tree rooted at computation time block `i` has height at most `i + 1`. -/
theorem height_unroll_computation_le
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → ℕ →
      (Fin (2 * (workTapeCount + 2)) → V) → V)
    (tape : TapeIndex workTapeCount) (timeBlock : ℕ) :
    (unroll tm x blockLength sourceValue combine
      (.computation tape timeBlock)).height ≤ timeBlock + 1 :=
  height_unroll_le_rank
    tm x blockLength sourceValue combine
      (.computation tape timeBlock)

end ComputationGraph

end TimeSpaceSimulation

end Complexity
