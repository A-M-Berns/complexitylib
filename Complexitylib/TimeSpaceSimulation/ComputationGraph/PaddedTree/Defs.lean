/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.BooleanTree.Defs
import Complexitylib.TreeEvaluation.BooleanPadding.Defs

/-!
# Fan-in-padded Boolean computation trees

The grouped interpolation layer uses a single chunk whose width must dominate
the tree fan-in. This file appends `fanIn + 1` false bits to every compact
Boolean value. The padding is semantic slack only; prefix recovery returns
the original encoding exactly.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace PaddedTree

/-- Fixed arity of the computation-graph tree. -/
def fanIn (workTapeCount : ℕ) : ℕ :=
  2 * (workTapeCount + 2)

/-- Width of a compact Boolean value after fan-in padding. -/
def width (tm : TM workTapeCount) (blockLength : ℕ) : ℕ :=
  TreeEval.BooleanPadding.paddedWidth
    (fanIn workTapeCount)
    (CompactEncoding.width blockLength tm.Q)

/-- Fan-in-padded Boolean tree for one computation-graph node. -/
noncomputable def tree
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    TreeEval.Tree (fanIn workTapeCount)
      (Fin (width tm blockLength) → Bool) := by
  simpa [fanIn, width] using
    TreeEval.BooleanPadding.padTree
      (BooleanTree.tree tm x blockLength hpositive node)

end PaddedTree

end ComputationGraph

end TimeSpaceSimulation

end Complexity
