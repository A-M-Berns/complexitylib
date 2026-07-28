/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Contents
import Complexitylib.TimeSpaceSimulation.ComputationGraph.NodeContent.Defs

/-!
# Rich computation-graph node-content internals

This file relates the packaged semantic value to the existing tape-block
content semantics and proves that the two predecessor roles provide the exact
inputs needed at the start of a target time block.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace Internal

theorem nodeContent_node_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (node : Node workTapeCount) :
    (nodeContent tm x blockLength node).node = node := by
  rfl

theorem nodeContent_block_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (node : Node workTapeCount) :
    (nodeContent tm x blockLength node).block =
      nodeBlock tm x blockLength node := by
  rfl

theorem nodeContent_cells_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (node : Node workTapeCount) :
    (nodeContent tm x blockLength node).cells =
      nodeBlockContents tm x blockLength node := by
  cases node <;> rfl

theorem nodeContent_contentPredecessor_cells_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount)
    (h : tm.BlockRespectingOnInput x blockLength) :
    (nodeContent tm x blockLength
        (contentPredecessor tm x blockLength timeBlock tape)).cells =
      startBlockContents tm x blockLength tape timeBlock := by
  rw [nodeContent_cells_internal,
    nodeBlockContents_contentPredecessor tm x blockLength timeBlock tape h]

theorem nodeContent_chronologicalPredecessor_state_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) :
    (nodeContent tm x blockLength
        (chronologicalPredecessor tm x blockLength timeBlock tape)).state =
      (tm.configurationAt x
        (timeBlockStart blockLength timeBlock)).state := by
  cases timeBlock <;>
    simp [chronologicalPredecessor, nodeContent, nodeConfigurationTime,
      timeBlockStart]

theorem nodeContent_chronologicalPredecessor_head_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) :
    (nodeContent tm x blockLength
        (chronologicalPredecessor tm x blockLength timeBlock tape)).head =
      (tapeAt
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock))
        tape).head := by
  cases timeBlock <;>
    simp [chronologicalPredecessor, nodeContent, nodeConfigurationTime,
      timeBlockStart, Node.tape]

end Internal

end ComputationGraph

end TimeSpaceSimulation

end Complexity
