/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactTree.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactTree.Internal

/-!
# Correct compact tree evaluation

The compact local transition computes the semantic value of every node in a
block-respecting computation. Its fixed-arity unrolling has height at most
the graph rank.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace CompactTree

/-- Recursive compact graph evaluation returns the semantic compact value. -/
theorem nodeValue_eq_nodeContent
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (h : tm.BlockRespectingOnInput x blockLength)
    (node : Node workTapeCount) :
    nodeValue tm x blockLength hpositive node =
      CompactContent.nodeContent
        tm x blockLength hpositive node :=
  Internal.nodeValue_eq_nodeContent_internal
    tm x blockLength hpositive h node

/-- The value of the compact unrolled tree is the semantic compact value. -/
theorem tree_value
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (h : tm.BlockRespectingOnInput x blockLength)
    (node : Node workTapeCount) :
    (tree tm x blockLength hpositive node).value =
      CompactContent.nodeContent
        tm x blockLength hpositive node :=
  Internal.tree_value_internal
    tm x blockLength hpositive h node

/-- The compact unrolled tree's height is at most its root graph rank. -/
theorem tree_height_le_rank
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    (tree tm x blockLength hpositive node).height ≤ node.rank :=
  Internal.tree_height_le_rank_internal
    tm x blockLength hpositive node

/-- A computation node at time block `i` gives a tree of height at most
`i + 1`. -/
theorem tree_computation_height_le
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (timeBlock : ℕ) :
    (tree tm x blockLength hpositive
      (.computation tape timeBlock)).height ≤ timeBlock + 1 :=
  tree_height_le_rank
    tm x blockLength hpositive (.computation tape timeBlock)

end CompactTree

end ComputationGraph

end TimeSpaceSimulation

end Complexity
