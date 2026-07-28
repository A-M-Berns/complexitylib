/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.BooleanTree.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.BooleanTree.Internal

/-!
# Correct fixed-width Boolean computation trees

The Boolean transport preserves a compact tree's exact height and evaluates
to the one-hot encoding of its semantic compact root value.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace BooleanTree

/-- Encoding a compact tree commutes with tree evaluation. -/
theorem encodeTree_value
    [Fintype Q] [DecidableEq Q]
    (defaultState : Q) (hpositive : 0 < blockLength)
    (compactTree :
      TreeEval.Tree d (CompactContent.Content blockLength Q)) :
    (encodeTree defaultState hpositive compactTree).value =
      CompactEncoding.encode compactTree.value :=
  Internal.encodeTree_value_internal
    defaultState hpositive compactTree

/-- Boolean encoding preserves the tree's height exactly. -/
theorem encodeTree_height
    [Fintype Q] [DecidableEq Q]
    (defaultState : Q) (hpositive : 0 < blockLength)
    (compactTree :
      TreeEval.Tree d (CompactContent.Content blockLength Q)) :
    (encodeTree defaultState hpositive compactTree).height =
      compactTree.height :=
  Internal.encodeTree_height_internal
    defaultState hpositive compactTree

/-- A block-respecting computation tree evaluates to the Boolean encoding of
its semantic compact root value. -/
theorem tree_value
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (h : tm.BlockRespectingOnInput x blockLength)
    (node : Node workTapeCount) :
    (tree tm x blockLength hpositive node).value =
      CompactEncoding.encode
        (CompactContent.nodeContent
          tm x blockLength hpositive node) :=
  Internal.tree_value_internal
    tm x blockLength hpositive h node

/-- The encoded Boolean tree's height is at most its root graph rank. -/
theorem tree_height_le_rank
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    (tree tm x blockLength hpositive node).height ≤ node.rank :=
  Internal.tree_height_le_rank_internal
    tm x blockLength hpositive node

/-- A computation node at time block `i` yields a Boolean tree of height at
most `i + 1`. -/
theorem tree_computation_height_le
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (timeBlock : ℕ) :
    (tree tm x blockLength hpositive
      (.computation tape timeBlock)).height ≤ timeBlock + 1 :=
  tree_height_le_rank
    tm x blockLength hpositive (.computation tape timeBlock)

end BooleanTree

end ComputationGraph

end TimeSpaceSimulation

end Complexity
