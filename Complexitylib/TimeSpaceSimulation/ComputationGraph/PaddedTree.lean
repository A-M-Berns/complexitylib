/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.PaddedTree.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.PaddedTree.Internal

/-!
# Correct fan-in-padded Boolean computation trees

The padded width is positive. Evaluation returns the padded one-hot encoding
of the compact semantic node value, and height remains bounded by graph rank.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace PaddedTree

/-- Every padded compact-value width is positive. -/
theorem width_pos
    (tm : TM workTapeCount) (blockLength : ℕ) :
    0 < width tm blockLength :=
  Internal.width_pos_internal tm blockLength

/-- A block-respecting padded tree evaluates to the padded compact semantic
root value. -/
theorem tree_value
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (h : tm.BlockRespectingOnInput x blockLength)
    (node : Node workTapeCount) :
    (tree tm x blockLength hpositive node).value =
      TreeEval.BooleanPadding.padBits (fanIn workTapeCount)
        (CompactEncoding.encode
          (CompactContent.nodeContent
            tm x blockLength hpositive node)) :=
  Internal.tree_value_internal
    tm x blockLength hpositive h node

/-- Fan-in padding preserves the graph-rank height bound. -/
theorem tree_height_le_rank
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    (tree tm x blockLength hpositive node).height ≤ node.rank :=
  Internal.tree_height_le_rank_internal
    tm x blockLength hpositive node

end PaddedTree

end ComputationGraph

end TimeSpaceSimulation

end Complexity
