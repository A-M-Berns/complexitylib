/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.BooleanTree
import Complexitylib.TimeSpaceSimulation.ComputationGraph.PaddedTree.Defs
import Complexitylib.TreeEvaluation.BooleanPadding

/-!
# Correctness of fan-in-padded computation trees
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace PaddedTree

namespace Internal

theorem width_pos_internal
    (tm : TM workTapeCount) (blockLength : ℕ) :
    0 < width tm blockLength := by
  unfold width
  exact TreeEval.BooleanPadding.paddedWidth_pos _ _

theorem tree_value_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (h : tm.BlockRespectingOnInput x blockLength)
    (node : Node workTapeCount) :
    (tree tm x blockLength hpositive node).value =
      TreeEval.BooleanPadding.padBits (fanIn workTapeCount)
        (CompactEncoding.encode
          (CompactContent.nodeContent
            tm x blockLength hpositive node)) := by
  rw [tree]
  change
    (TreeEval.BooleanPadding.padTree
      (BooleanTree.tree
        tm x blockLength hpositive node)).value = _
  rw [TreeEval.BooleanPadding.padTree_value]
  congr 1
  exact BooleanTree.tree_value
    tm x blockLength hpositive h node

theorem tree_height_le_rank_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    (tree tm x blockLength hpositive node).height ≤ node.rank := by
  rw [tree]
  change
    (TreeEval.BooleanPadding.padTree
      (BooleanTree.tree
        tm x blockLength hpositive node)).height ≤ _
  rw [TreeEval.BooleanPadding.padTree_height]
  exact BooleanTree.tree_height_le_rank
    tm x blockLength hpositive node

end Internal

end PaddedTree

end ComputationGraph

end TimeSpaceSimulation

end Complexity
