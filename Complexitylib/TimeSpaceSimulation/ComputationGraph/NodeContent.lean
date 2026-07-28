/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.NodeContent.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.NodeContent.Internal

/-!
# Rich semantic values for computation-graph nodes

This module exposes the complete per-tape value needed by the local
time-block simulation: node identity, the carried tape block, machine state,
named-tape head position, and block cells.

The content predecessor supplies exactly the active block's cells at the
target time block's start. Independently, the chronological predecessor
supplies exactly the target-start machine state and the requested named-tape
head. The latter statements include time block zero, where the predecessor is
an initial source.

## Main theorems

* `nodeContent_cells` -- compatibility with `nodeBlockContents`
* `nodeContent_contentPredecessor_cells` -- content-edge soundness
* `nodeContent_chronologicalPredecessor_state` -- target-start state
* `nodeContent_chronologicalPredecessor_head` -- target-start named head
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

/-- Packaging preserves the requested node identity. -/
@[simp] theorem nodeContent_node
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (node : Node workTapeCount) :
    (nodeContent tm x blockLength node).node = node :=
  Internal.nodeContent_node_internal tm x blockLength node

/-- Packaging records exactly the node's semantic tape block. -/
@[simp] theorem nodeContent_block
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (node : Node workTapeCount) :
    (nodeContent tm x blockLength node).block =
      nodeBlock tm x blockLength node :=
  Internal.nodeContent_block_internal tm x blockLength node

/-- The rich node value's cell projection is the existing semantic
`nodeBlockContents` value. -/
theorem nodeContent_cells
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (node : Node workTapeCount) :
    (nodeContent tm x blockLength node).cells =
      nodeBlockContents tm x blockLength node :=
  Internal.nodeContent_cells_internal tm x blockLength node

/-- The content predecessor supplies exactly the active tape-block contents
at the start of the target time block. -/
theorem nodeContent_contentPredecessor_cells
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount)
    (h : tm.BlockRespectingOnInput x blockLength) :
    (nodeContent tm x blockLength
        (contentPredecessor tm x blockLength timeBlock tape)).cells =
      startBlockContents tm x blockLength tape timeBlock :=
  Internal.nodeContent_contentPredecessor_cells_internal
    tm x blockLength timeBlock tape h

/-- The chronological predecessor supplies the machine state at the target
time block's start, including at time block zero. -/
theorem nodeContent_chronologicalPredecessor_state
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) :
    (nodeContent tm x blockLength
        (chronologicalPredecessor tm x blockLength timeBlock tape)).state =
      (tm.configurationAt x
        (timeBlockStart blockLength timeBlock)).state :=
  Internal.nodeContent_chronologicalPredecessor_state_internal
    tm x blockLength timeBlock tape

/-- The chronological predecessor supplies the requested named tape's head
position at the target time block's start, including at time block zero. -/
theorem nodeContent_chronologicalPredecessor_head
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) :
    (nodeContent tm x blockLength
        (chronologicalPredecessor tm x blockLength timeBlock tape)).head =
      (tapeAt
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock))
        tape).head :=
  Internal.nodeContent_chronologicalPredecessor_head_internal
    tm x blockLength timeBlock tape

end ComputationGraph

end TimeSpaceSimulation

end Complexity
