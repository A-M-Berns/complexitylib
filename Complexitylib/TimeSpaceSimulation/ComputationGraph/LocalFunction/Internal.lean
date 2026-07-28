/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LocalFunction.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LocalSimulation
import Complexitylib.TimeSpaceSimulation.ComputationGraph.NodeContent

/-!
# Local computation-graph node function internals

This file proves that reconstructing only the selected blocks gives a locally
agreeing configuration, that the actual predecessor values reconstruct the
target time block's real local start configuration, and that executing the
local node function yields the semantic target node value.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace LocalFunction

namespace Internal

theorem tapeFromBlock_agreement_internal
    (blockLength block : ℕ) (hpositive : 0 < blockLength)
    (tape : Tape) :
    TapeBlockAgreement blockLength block tape
      (tapeFromBlock blockLength block tape.head
        (blockContents tape blockLength block)) := by
  constructor
  · rfl
  · intro position hposition
    unfold tapeFromBlock
    dsimp only
    split
    · rw [if_pos (blockIndex_eq_of_inBlock hposition)]
      symm
      rw [← blockIndex_eq_of_inBlock hposition]
      exact blockContents_ownBlock
        tape blockLength position hpositive
    · contradiction

theorem cfg_localized_agreement_internal
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (blocks : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount Q) :
    CfgBlockAgreement blockLength blocks cfg
      (localizedCfg blockLength blocks cfg) := by
  constructor
  · rfl
  · simpa [localizedCfg, cfgFromBlocks, tapeAt_input] using
      tapeFromBlock_agreement_internal blockLength
        (blocks (TapeIndex.input workTapeCount))
        hpositive cfg.input
  · intro index
    simpa [localizedCfg, cfgFromBlocks, tapeAt_work] using
      tapeFromBlock_agreement_internal blockLength
        (blocks (TapeIndex.work index))
        hpositive (cfg.work index)
  · simpa [localizedCfg, cfgFromBlocks, tapeAt_output] using
      tapeFromBlock_agreement_internal blockLength
        (blocks (TapeIndex.output workTapeCount))
        hpositive cfg.output

theorem cfgBlockAgreement_tapeAt_internal
    {blockLength : ℕ}
    {blocks : TapeIndex workTapeCount → ℕ}
    {left right : Cfg workTapeCount Q}
    (h : CfgBlockAgreement blockLength blocks left right)
    (tape : TapeIndex workTapeCount) :
    TapeBlockAgreement blockLength (blocks tape)
      (tapeAt left tape) (tapeAt right tape) := by
  by_cases hinput : tape.val = 0
  · have htape :
        tape = TapeIndex.input workTapeCount :=
      Fin.ext hinput
    subst tape
    simpa only [tapeAt_input] using h.input
  · by_cases houtput : tape.val = workTapeCount + 1
    · have htape :
          tape = TapeIndex.output workTapeCount :=
        Fin.ext houtput
      subst tape
      simpa only [tapeAt_output] using h.output
    · let index : Fin workTapeCount :=
        ⟨tape.val - 1, by omega⟩
      have htape : tape = TapeIndex.work index := by
        apply Fin.ext
        simp only [TapeIndex.work, index]
        omega
      rw [htape]
      simpa only [tapeAt_work] using h.work index

theorem predecessorCfg_eq_localizedCfg_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    predecessorCfg tm x blockLength timeBlock
        (predecessorNodeContents tm x blockLength timeBlock) =
      localizedCfg blockLength
        (activeBlocks tm x blockLength timeBlock)
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock)) := by
  have hstate :
      ((predecessorNodeContents tm x blockLength timeBlock)
        (.chronological, TapeIndex.input workTapeCount)).state =
      (tm.configurationAt x
        (timeBlockStart blockLength timeBlock)).state :=
    nodeContent_chronologicalPredecessor_state
      tm x blockLength timeBlock
        (TapeIndex.input workTapeCount)
  have hheads :
      (fun tape =>
        ((predecessorNodeContents tm x blockLength timeBlock)
          (.chronological, tape)).head) =
      (fun tape =>
        (tapeAt
          (tm.configurationAt x
            (timeBlockStart blockLength timeBlock))
          tape).head) := by
    funext tape
    exact nodeContent_chronologicalPredecessor_head
      tm x blockLength timeBlock tape
  have hcells :
      (fun tape =>
        ((predecessorNodeContents tm x blockLength timeBlock)
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
    simpa only [predecessorNodeContents, predecessor,
      startBlockContents, blockContentsAt, activeBlocks] using
      nodeContent_contentPredecessor_cells
        tm x blockLength timeBlock tape h
  unfold predecessorCfg localizedCfg
  rw [hstate, hheads, hcells]

theorem localNodeFunction_semantic_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (h : tm.BlockRespectingOnInput x blockLength) :
    localNodeFunction tm x blockLength timeBlock targetTape
        (predecessorNodeContents tm x blockLength timeBlock) =
      nodeContent tm x blockLength
        (.computation targetTape timeBlock) := by
  have hpositive := h.blockLength_pos tm x blockLength
  have hseed :=
    predecessorCfg_eq_localizedCfg_internal
      tm x blockLength timeBlock h
  have hstart :=
    cfg_localized_agreement_internal blockLength hpositive
      (activeBlocks tm x blockLength timeBlock)
      (tm.configurationAt x
        (timeBlockStart blockLength timeBlock))
  have hfinal :=
    LocalSimulation.timeBlock_trace_cfgBlockAgreement
      tm x blockLength timeBlock
        (localizedCfg blockLength
          (activeBlocks tm x blockLength timeBlock)
          (tm.configurationAt x
            (timeBlockStart blockLength timeBlock)))
        h hstart
  have htape :=
    cfgBlockAgreement_tapeAt_internal hfinal targetTape
  unfold localNodeFunction
  rw [hseed]
  apply NodeContent.ext
  · rfl
  · rfl
  · exact hfinal.state_eq.symm
  · exact htape.head_eq.symm
  · funext offset
    exact (htape.cells_eq _
      (blockOffset_in_block blockLength
        (activeBlocks tm x blockLength timeBlock targetTape)
        offset)).symm

end Internal

end LocalFunction

end ComputationGraph

end TimeSpaceSimulation

end Complexity
