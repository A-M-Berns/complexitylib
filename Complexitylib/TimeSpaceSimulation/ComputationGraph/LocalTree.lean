/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LocalTree.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LocalTree.Internal

/-!
# Correct Tree Evaluation reduction for block-respecting runs

The fixed-arity tree `localTree` recursively follows Williams's content and
chronological computation-graph edges. Every internal function genuinely
reconstructs its local start configuration and runs the simulated machine for
one time block. On a block-respecting run, evaluating this tree returns the
rich semantic value of its root node exactly.

The tree has fan-in `2 * (workTapeCount + 2)` and height at most the root's
time-block rank. It is a semantic object only; the computation-graph oracle
allows an implementation to traverse it without materializing the
exponentially large unrolling.

## Main theorems

- `localNodeValue_eq_nodeContent` -- recursive graph evaluation is semantic
- `localTree_value` -- the Tree Evaluation root has the correct rich value
- `localTree_height_le_rank` -- height is bounded by time-block rank
- `localTree_computation_height_le` -- explicit computation-root bound
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace LocalTree

/-- Recursive evaluation of the genuine local node functions returns each
node's rich semantic value. -/
theorem localNodeValue_eq_nodeContent
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength)
    (node : Node workTapeCount) :
    localNodeValue tm x blockLength node =
      nodeContent tm x blockLength node :=
  Internal.localNodeValue_eq_nodeContent_internal
    tm x blockLength h node

/-- Evaluating the fixed-arity unrolled Tree Evaluation instance returns the
rich semantic value of its root. -/
theorem localTree_value
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength)
    (node : Node workTapeCount) :
    (localTree tm x blockLength node).value =
      nodeContent tm x blockLength node :=
  Internal.localTree_value_internal
    tm x blockLength h node

/-- The local Tree Evaluation instance's height is bounded by its root
node's rank. -/
theorem localTree_height_le_rank
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (node : Node workTapeCount) :
    (localTree tm x blockLength node).height ≤ node.rank :=
  Internal.localTree_height_le_rank_internal
    tm x blockLength node

/-- A local tree rooted at time block `i` has height at most `i + 1`. -/
theorem localTree_computation_height_le
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (tape : TapeIndex workTapeCount)
    (timeBlock : ℕ) :
    (localTree tm x blockLength
      (.computation tape timeBlock)).height ≤ timeBlock + 1 :=
  localTree_height_le_rank
    tm x blockLength (.computation tape timeBlock)

end LocalTree

end ComputationGraph

end TimeSpaceSimulation

end Complexity
