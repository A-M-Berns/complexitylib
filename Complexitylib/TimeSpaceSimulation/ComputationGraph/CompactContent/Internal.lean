/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactContent.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LocalFunction
import Complexitylib.TimeSpaceSimulation.ComputationGraph.NodeContent

/-!
# Correctness of compact computation-graph node values

This file proves that compact predecessor values reconstruct the canonical
localized start configuration and that the compact local node function
computes the actual compact semantic value.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace CompactContent

namespace Internal

theorem predecessorCfg_eq_localizedCfg_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    predecessorCfg tm x blockLength timeBlock
        (predecessorContents tm x blockLength timeBlock
          (h.blockLength_pos tm x blockLength)) =
      LocalFunction.localizedCfg blockLength
        (activeBlocks tm x blockLength timeBlock)
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock)) := by
  have hpositive := h.blockLength_pos tm x blockLength
  have hstate :
      ((predecessorContents tm x blockLength timeBlock hpositive)
        (.chronological, TapeIndex.input workTapeCount)).state =
      (tm.configurationAt x
        (timeBlockStart blockLength timeBlock)).state := by
    exact nodeContent_chronologicalPredecessor_state
      tm x blockLength timeBlock
        (TapeIndex.input workTapeCount)
  have hheads :
      (fun tape =>
        activeBlocks tm x blockLength timeBlock tape * blockLength +
          ((predecessorContents tm x blockLength timeBlock hpositive)
            (.chronological, tape)).headRemainder.val) =
      (fun tape =>
        (tapeAt
          (tm.configurationAt x
            (timeBlockStart blockLength timeBlock))
          tape).head) := by
    funext tape
    have hhead :=
      nodeContent_chronologicalPredecessor_head
        tm x blockLength timeBlock tape
    change (ComputationGraph.nodeContent tm x blockLength
      (chronologicalPredecessor tm x blockLength timeBlock tape)).head =
        _ at hhead
    simp only [predecessorContents, nodeContent, predecessor]
    rw [hhead]
    have hin :=
      h.head_in_activeBlock tm x blockLength timeBlock
        ⟨0, hpositive⟩ tape
    have hblock := blockIndex_eq_of_inBlock hin
    unfold activeBlocks
    unfold headBlock at hblock
    rw [← hblock]
    simpa [blockIndex, Nat.add_comm, Nat.mul_comm] using
      Nat.mod_add_div
        (tapeAt
          (tm.configurationAt x
            (timeBlockStart blockLength timeBlock))
          tape).head
        blockLength
  have hcells :
      (fun tape =>
        ((predecessorContents tm x blockLength timeBlock hpositive)
          (.content, tape)).cells) =
      (fun tape =>
        blockContents
          (tapeAt
            (tm.configurationAt x
              (timeBlockStart blockLength timeBlock))
            tape)
          blockLength
          (activeBlocks tm x blockLength timeBlock tape)) := by
    funext tape
    change (ComputationGraph.nodeContent tm x blockLength
      (contentPredecessor tm x blockLength timeBlock tape)).cells = _
    simpa [startBlockContents, blockContentsAt, activeBlocks] using
      nodeContent_contentPredecessor_cells
        tm x blockLength timeBlock tape h
  unfold predecessorCfg LocalFunction.localizedCfg
  rw [hstate, hheads, hcells]

theorem localNodeFunction_semantic_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (h : tm.BlockRespectingOnInput x blockLength) :
    localNodeFunction tm x blockLength
        (h.blockLength_pos tm x blockLength)
        timeBlock targetTape
        (predecessorContents tm x blockLength timeBlock
          (h.blockLength_pos tm x blockLength)) =
      nodeContent tm x blockLength
        (h.blockLength_pos tm x blockLength)
        (.computation targetTape timeBlock) := by
  have hpositive := h.blockLength_pos tm x blockLength
  have hseed :=
    predecessorCfg_eq_localizedCfg_internal
      tm x blockLength timeBlock h
  have hstart :=
    LocalFunction.cfg_localized_agreement blockLength hpositive
      (activeBlocks tm x blockLength timeBlock)
      (tm.configurationAt x
        (timeBlockStart blockLength timeBlock))
  have hfinal :=
    LocalSimulation.timeBlock_trace_cfgBlockAgreement
      tm x blockLength timeBlock
        (LocalFunction.localizedCfg blockLength
          (activeBlocks tm x blockLength timeBlock)
          (tm.configurationAt x
            (timeBlockStart blockLength timeBlock)))
        h hstart
  have htape :=
    LocalFunction.CfgBlockAgreement.tapeAt hfinal targetTape
  unfold localNodeFunction nodeContent
  simp only [hseed]
  apply Content.ext
  · exact hfinal.state_eq.symm
  · apply Fin.ext
    exact congrArg (fun position => position % blockLength)
      htape.head_eq.symm
  · funext offset
    exact (htape.cells_eq _
      (blockOffset_in_block blockLength
        (activeBlocks tm x blockLength timeBlock targetTape)
        offset)).symm

end Internal

end CompactContent

end ComputationGraph

end TimeSpaceSimulation

end Complexity
