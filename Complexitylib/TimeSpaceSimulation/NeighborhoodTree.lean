/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodTree.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodTree.Internal

/-!
# Correct compact and Boolean neighborhood trees

The recursive compact evaluator and its unrolled tree compute the actual
semantic neighborhood-node value for every arbitrary deterministic machine.
The exact one-hot Boolean transport preserves both that value and tree
height.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodTree

open NeighborhoodGraph

/-- Recursive compact graph evaluation equals the actual node value. -/
theorem compactNodeValue_eq_nodeContent
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    compactNodeValue tm x blockLength hpositive node =
      NeighborhoodContent.nodeContent
        tm x blockLength hpositive node :=
  Internal.compactNodeValue_eq_nodeContent_internal
    tm x blockLength hpositive node

/-- The compact unrolled tree evaluates to the actual node value. -/
theorem compactTree_value
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    (compactTree tm x blockLength hpositive node).value =
      NeighborhoodContent.nodeContent
        tm x blockLength hpositive node :=
  Internal.compactTree_value_internal
    tm x blockLength hpositive node

/-- Compact unrolling has height at most the root graph rank. -/
theorem compactTree_height_le_rank
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    (compactTree tm x blockLength hpositive node).height ≤
      node.rank :=
  Internal.compactTree_height_le_rank_internal
    tm x blockLength hpositive node

/-- The Boolean tree evaluates to the exact one-hot encoding of the actual
compact node value. -/
theorem booleanTree_value
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    (booleanTree tm x blockLength hpositive node).value =
      ComputationGraph.CompactEncoding.encode
        (NeighborhoodContent.nodeContent
          tm x blockLength hpositive node) :=
  Internal.booleanTree_value_internal
    tm x blockLength hpositive node

/-- Boolean encoding preserves the root-rank height bound. -/
theorem booleanTree_height_le_rank
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    (booleanTree tm x blockLength hpositive node).height ≤
      node.rank :=
  Internal.booleanTree_height_le_rank_internal
    tm x blockLength hpositive node

/-- A computation node at interval `i` yields a Boolean tree of height at most
`i + 1`. -/
theorem booleanTree_computation_height_le
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    (timeBlock : ℕ) :
    (booleanTree tm x blockLength hpositive
      (.computation tape slot timeBlock)).height ≤
        timeBlock + 1 :=
  booleanTree_height_le_rank
    tm x blockLength hpositive
      (.computation tape slot timeBlock)

end NeighborhoodTree

end TimeSpaceSimulation

end Complexity
