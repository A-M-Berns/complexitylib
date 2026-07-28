/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Contents
import Complexitylib.TimeSpaceSimulation.Locality
import Complexitylib.TimeSpaceSimulation.NeighborhoodContent.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph
import Complexitylib.TimeSpaceSimulation.NeighborhoodPersistence

/-!
# Correctness internals for compact neighborhood-graph values
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodContent

open NeighborhoodGraph

namespace Internal

theorem tapeFromNeighborhood_agreement_internal
    (blockLength center : ℕ) (hpositive : 0 < blockLength)
    (tape : Tape) :
    TapeNeighborhoodAgreement blockLength center tape
      (tapeFromNeighborhood blockLength center tape.head
        (fun slot =>
          blockContents tape blockLength
            (neighborBlock center slot))) := by
  constructor
  · rfl
  · intro position hposition
    have hcontains :
        NeighborhoodContains center
          (blockIndex blockLength position) := by
      rw [inThreeBlockNeighborhood_iff_three_blocks] at hposition
      rcases hposition with hlower | hcenter | hupper
      · left
        exact ComputationGraph.blockIndex_eq_of_inBlock hlower
      · right
        left
        exact ComputationGraph.blockIndex_eq_of_inBlock hcenter
      · right
        right
        exact ComputationGraph.blockIndex_eq_of_inBlock hupper
    unfold tapeFromNeighborhood
    dsimp only
    simp only [hpositive, dite_true, hcontains, if_true]
    rw [neighborBlock_matchingSlot hcontains]
    exact (blockContents_ownBlock
      tape blockLength position hpositive).symm

theorem cfg_localized_agreement_internal
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (cfg : Cfg workTapeCount Q) :
    CfgThreeBlockAgreement blockLength cfg
      (localizedCfg blockLength cfg) := by
  constructor
  · rfl
  · simpa [localizedCfg, cfgFromNeighborhoods,
      startingBlocks, tapeAt_input] using
        tapeFromNeighborhood_agreement_internal
          blockLength
          (blockIndex blockLength cfg.input.head)
          hpositive cfg.input
  · intro index
    simpa [localizedCfg, cfgFromNeighborhoods,
      startingBlocks, tapeAt_work] using
        tapeFromNeighborhood_agreement_internal
          blockLength
          (blockIndex blockLength (cfg.work index).head)
          hpositive (cfg.work index)
  · simpa [localizedCfg, cfgFromNeighborhoods,
      startingBlocks, tapeAt_output] using
        tapeFromNeighborhood_agreement_internal
          blockLength
          (blockIndex blockLength cfg.output.head)
          hpositive cfg.output

theorem cfgNeighborhoodAgreement_tapeAt_internal
    {blockLength : ℕ}
    {centers : TapeIndex workTapeCount → ℕ}
    {left right : Cfg workTapeCount Q}
    (h : CfgNeighborhoodAgreement blockLength centers left right)
    (tape : TapeIndex workTapeCount) :
    TapeNeighborhoodAgreement blockLength (centers tape)
      (tapeAt left tape) (tapeAt right tape) := by
  by_cases hinput : tape.val = 0
  · have htape : tape = TapeIndex.input workTapeCount :=
      Fin.ext hinput
    subst tape
    simpa only [tapeAt_input] using h.input
  · by_cases houtput : tape.val = workTapeCount + 1
    · have htape : tape = TapeIndex.output workTapeCount :=
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

theorem nodeConfigurationTime_chronologicalPredecessor_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) :
    nodeConfigurationTime blockLength
        (chronologicalPredecessor
          tm x blockLength timeBlock tape) =
      timeBlockStart blockLength timeBlock := by
  cases timeBlock <;>
    simp [chronologicalPredecessor, nodeConfigurationTime,
      timeBlockStart, Nat.add_mul]

theorem nodeContent_chronologicalPredecessor_state_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) :
    (nodeContent tm x blockLength hpositive
      (chronologicalPredecessor
        tm x blockLength timeBlock tape)).state =
      (tm.configurationAt x
        (timeBlockStart blockLength timeBlock)).state := by
  unfold nodeContent
  dsimp only
  rw [nodeConfigurationTime_chronologicalPredecessor_internal]

theorem nodeContent_chronologicalPredecessor_headRemainder_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) :
    (nodeContent tm x blockLength hpositive
      (chronologicalPredecessor tm x blockLength
        timeBlock tape)).headRemainder.val =
      (tapeAt
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock))
        tape).head % blockLength := by
  unfold nodeContent
  dsimp only
  rw [nodeConfigurationTime_chronologicalPredecessor_internal]
  rw [chronologicalPredecessor_tape]

theorem nodeContent_contentPredecessor_cells_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (slot : Slot) :
    (nodeContent tm x blockLength hpositive
      (contentPredecessor tm x blockLength
        timeBlock tape slot)).cells =
      ComputationGraph.blockContentsAt tm x blockLength
        (timeBlockStart blockLength timeBlock) tape
        (requestedBlock tm x blockLength timeBlock tape slot) := by
  let requested :=
    requestedBlock tm x blockLength timeBlock tape slot
  generalize hprevious :
    previousInterval tm x blockLength tape requested timeBlock =
      result
  cases result with
  | none =>
      have hpredecessor :
          contentPredecessor tm x blockLength
              timeBlock tape slot =
            .source tape requested := by
        simp [contentPredecessor, requested, hprevious]
      rw [hpredecessor]
      change
        ComputationGraph.blockContentsAt tm x blockLength
            0 tape requested =
          ComputationGraph.blockContentsAt tm x blockLength
            (timeBlockStart blockLength timeBlock)
            tape requested
      symm
      have hpersist :=
        NeighborhoodPersistence.inactive_intervals_preserve
          tm x blockLength 0 timeBlock requested tape
            hpositive
      simpa [timeBlockStart] using hpersist (by
        intro offset hoffset hcontains
        have hnone :=
          previousInterval_eq_none_iff.mp hprevious
            ⟨offset, hoffset⟩
        apply hnone
        simpa [NeighborhoodContains,
          NeighborhoodGraph.centerBlock,
          NeighborhoodPersistence.ContainsBlock,
          NeighborhoodPersistence.centerBlock,
          TM.activeBlock, headBlock] using hcontains)
  | some previous =>
      have hpredecessor :
          contentPredecessor tm x blockLength
              timeBlock tape slot =
            .computation tape
              (matchingSlot
                (centerBlock tm x blockLength
                  previous.val tape)
                requested)
              previous.val := by
        simp [contentPredecessor, requested, hprevious]
      rw [hpredecessor]
      change
        ComputationGraph.blockContentsAt tm x blockLength
            (timeBlockStart blockLength (previous.val + 1))
            tape
            (neighborBlock
              (centerBlock tm x blockLength previous.val tape)
              (matchingSlot
                (centerBlock tm x blockLength previous.val tape)
                requested)) =
          ComputationGraph.blockContentsAt tm x blockLength
            (timeBlockStart blockLength timeBlock)
            tape requested
      rw [previousInterval_matchingSlot hprevious]
      let count := timeBlock - (previous.val + 1)
      have hpersist :=
        NeighborhoodPersistence.inactive_intervals_preserve
          tm x blockLength (previous.val + 1) count
            requested tape hpositive
      have hsum : previous.val + 1 + count = timeBlock := by
        dsimp only [count]
        omega
      rw [hsum] at hpersist
      symm
      exact hpersist (by
        intro offset hoffset hcontains
        have hcandidate_lt :
            previous.val + 1 + offset < timeBlock := by
          dsimp only [count] at hoffset
          omega
        have hmaximal :=
          previousInterval_some_maximal hprevious
            ⟨previous.val + 1 + offset, hcandidate_lt⟩
        have hneighborhood :
            NeighborhoodContains
              (centerBlock tm x blockLength
                (previous.val + 1 + offset) tape)
              requested := by
          simpa [NeighborhoodContains,
            NeighborhoodGraph.centerBlock,
            NeighborhoodPersistence.ContainsBlock,
            NeighborhoodPersistence.centerBlock,
            TM.activeBlock, headBlock] using hcontains
        have := hmaximal hneighborhood
        have hle :
            previous.val + 1 + offset ≤ previous.val := by
          exact this
        omega)

theorem predecessorCfg_eq_localizedCfg_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (hpositive : 0 < blockLength) :
    predecessorCfg tm x blockLength timeBlock
        (predecessorContents tm x blockLength
          timeBlock hpositive) =
      localizedCfg blockLength
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock)) := by
  have hstate :
      ((predecessorContents tm x blockLength
          timeBlock hpositive)
        (.chronological,
          TapeIndex.input workTapeCount)).state =
      (tm.configurationAt x
        (timeBlockStart blockLength timeBlock)).state := by
    exact nodeContent_chronologicalPredecessor_state_internal
      tm x blockLength timeBlock hpositive
        (TapeIndex.input workTapeCount)
  have hheads :
      (fun tape =>
        centerBlock tm x blockLength timeBlock tape *
            blockLength +
          ((predecessorContents tm x blockLength
            timeBlock hpositive)
            (.chronological, tape)).headRemainder.val) =
      (fun tape =>
        (tapeAt
          (tm.configurationAt x
            (timeBlockStart blockLength timeBlock))
          tape).head) := by
    funext tape
    change
      centerBlock tm x blockLength timeBlock tape *
          blockLength +
        (nodeContent tm x blockLength hpositive
          (chronologicalPredecessor tm x blockLength
            timeBlock tape)).headRemainder.val =
        _
    rw [nodeContent_chronologicalPredecessor_headRemainder_internal]
    unfold centerBlock TM.activeBlock headBlock blockIndex
    simpa [Nat.add_comm, Nat.mul_comm] using
      Nat.mod_add_div
        (tapeAt
          (tm.configurationAt x
            (timeBlockStart blockLength timeBlock))
          tape).head
        blockLength
  have hcells :
      (fun tape slot =>
        ((predecessorContents tm x blockLength
          timeBlock hpositive)
          (.content slot, tape)).cells) =
      (fun tape slot =>
        blockContents
          (tapeAt
            (tm.configurationAt x
              (timeBlockStart blockLength timeBlock))
            tape)
          blockLength
          (neighborBlock
            (startingBlocks blockLength
              (tm.configurationAt x
                (timeBlockStart blockLength timeBlock))
              tape)
            slot)) := by
    funext tape slot
    change
      (nodeContent tm x blockLength hpositive
        (contentPredecessor tm x blockLength
          timeBlock tape slot)).cells = _
    simpa [ComputationGraph.blockContentsAt,
      requestedBlock, centerBlock, TM.activeBlock,
      headBlock, startingBlocks] using
        nodeContent_contentPredecessor_cells_internal
          tm x blockLength timeBlock hpositive tape slot
  have hcenters :
      centerBlock tm x blockLength timeBlock =
        startingBlocks blockLength
          (tm.configurationAt x
            (timeBlockStart blockLength timeBlock)) := by
    funext tape
    rfl
  unfold predecessorCfg localizedCfg
  rw [hstate, hheads, hcells, hcenters]

theorem configurationAt_add_internal
    (tm : TM workTapeCount) (x : List Bool)
    (start steps : ℕ) :
    tm.configurationAt x (start + steps) =
      tm.toNTM.trace steps (fun _ => false)
        (tm.configurationAt x start) := by
  unfold TM.configurationAt
  simpa using tm.toNTM.trace_add_fun start steps
    (fun _ => false) (tm.initCfg x)

theorem localNodeFunction_semantic_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (hpositive : 0 < blockLength)
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot) :
    localNodeFunction tm x blockLength hpositive
        timeBlock targetTape targetSlot
        (predecessorContents tm x blockLength
          timeBlock hpositive) =
      nodeContent tm x blockLength hpositive
        (.computation targetTape targetSlot timeBlock) := by
  have hseed :=
    predecessorCfg_eq_localizedCfg_internal
      tm x blockLength timeBlock hpositive
  have hstart :=
    cfg_localized_agreement_internal blockLength hpositive
      (tm.configurationAt x
        (timeBlockStart blockLength timeBlock))
  have hfinal :=
    tm.configurationAt_threeBlock_noninterference
      x blockLength
        (timeBlockStart blockLength timeBlock)
        blockLength
        (localizedCfg blockLength
          (tm.configurationAt x
            (timeBlockStart blockLength timeBlock)))
        hpositive le_rfl hstart
  have htape :=
    cfgNeighborhoodAgreement_tapeAt_internal
      hfinal targetTape
  unfold localNodeFunction nodeContent
  simp only [hseed]
  apply ComputationGraph.CompactContent.Content.ext
  · simpa [nodeConfigurationTime, timeBlockStart,
      Nat.add_mul] using hfinal.state_eq.symm
  · apply Fin.ext
    simpa [nodeConfigurationTime, timeBlockStart,
      Nat.add_mul] using
        congrArg (fun position => position % blockLength)
          htape.head_eq.symm
  · funext offset
    have hblock :
        InBlock blockLength
          (requestedBlock tm x blockLength timeBlock
            targetTape targetSlot)
          ((requestedBlock tm x blockLength timeBlock
              targetTape targetSlot) *
              blockLength + offset.val) :=
      ComputationGraph.blockOffset_in_block
        blockLength
        (requestedBlock tm x blockLength timeBlock
          targetTape targetSlot)
        offset
    have hneighborhood :
        InThreeBlockNeighborhood blockLength
          (startingBlocks blockLength
            (tm.configurationAt x
              (timeBlockStart blockLength timeBlock))
            targetTape)
          ((requestedBlock tm x blockLength timeBlock
              targetTape targetSlot) *
              blockLength + offset.val) := by
      rw [inThreeBlockNeighborhood_iff_three_blocks]
      cases targetSlot with
      | lower =>
          left
          simpa [requestedBlock, centerBlock, TM.activeBlock,
            headBlock, startingBlocks] using hblock
      | center =>
          right
          left
          simpa [requestedBlock, centerBlock, TM.activeBlock,
            headBlock, startingBlocks] using hblock
      | upper =>
          right
          right
          simpa [requestedBlock, centerBlock, TM.activeBlock,
            headBlock, startingBlocks] using hblock
    simpa [nodeConfigurationTime, blockContents,
      timeBlockStart, Nat.add_mul] using
        (htape.cells_eq _ hneighborhood).symm

end Internal

end NeighborhoodContent

end TimeSpaceSimulation

end Complexity
