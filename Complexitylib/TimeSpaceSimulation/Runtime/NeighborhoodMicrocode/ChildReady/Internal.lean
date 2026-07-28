/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildReady.Defs

/-!
# Regenerating a child node and catalytic target -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ChildReady
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

private theorem copy_runs
    (destination source : ℕ) (store : Store)
    (hne : destination ≠ source) :
    Runs (ControlDecode.copy destination source) store
      (Function.update store destination (store source)) := by
  apply Runs.seq (Runs.basic (.imm destination 0) store)
  simpa [ControlDecode.copy, Basic.exec, Function.update_of_ne,
    hne, Ne.symm hne] using
    Runs.basic
      (.add destination source destination)
      (Basic.exec (.imm destination 0) store)

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} {cmd : Cmd}
    (hwrites : Footprint.CmdWritesWithin small cmd)
    (hsubset : small ⊆ large) :
    Footprint.CmdWritesWithin large cmd := by
  induction cmd with
  | skip =>
      trivial
  | basic op =>
      cases op <;>
        simp only [Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin] at hwrites ⊢
      all_goals
        exact hsubset hwrites
  | seq first second ihFirst ihSecond =>
      exact ⟨ihFirst hwrites.1, ihSecond hwrites.2⟩
  | ifZero test onZero onNonzero ihZero ihNonzero =>
      exact ⟨ihZero hwrites.1, ihNonzero hwrites.2⟩
  | whileNonzero test body ih =>
      exact ih hwrites

private theorem scratchFootprint_subset_internal
    (regs : NeighborhoodTrial.Registers controller) :
    ControlDecode.scratchFootprint regs ⊆ writeFootprint regs := by
  intro address haddress
  simp only [ControlDecode.scratchFootprint, Finset.mem_image,
    Finset.mem_univ, true_and] at haddress
  obtain ⟨slot, rfl⟩ := haddress
  fin_cases slot <;>
    simp [writeFootprint, ChildNode.priorAssemblyFootprint,
      ChildNode.priorFootprint, ChildNode.centerFootprint,
      ChildNode.movementFootprint, ControlDecode.scratchMap,
      ChildNode.movementMap, ChildNode.centerMap, ChildNode.priorMap,
      ChildNode.nodeEncodingFootprint, Layout.nodeCode,
      Layout.codecDigit, regs.injective.eq_iff] <;> decide

private theorem priorAssembly_subset_internal
    (regs : NeighborhoodTrial.Registers controller) :
    ChildNode.priorAssemblyFootprint regs ⊆ writeFootprint regs :=
  Finset.subset_insert _ _

theorem writeFootprint_subset_layout_internal
    (regs : NeighborhoodTrial.Registers controller) :
    writeFootprint regs ⊆ regs.layout.footprint := by
  intro address haddress
  simp only [writeFootprint, Finset.mem_insert] at haddress
  rcases haddress with hsaved | hprior
  · subst address
    exact Layout.index_mem_layout_footprint regs 1
  · exact
      ChildNode.priorAssemblyFootprint_subset_layout regs hprior

private theorem restoreTarget_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (writeFootprint regs) (restoreTarget regs) := by
  simp [restoreTarget, writeFootprint,
    ChildNode.priorAssemblyFootprint, ChildNode.priorFootprint,
    ChildNode.centerFootprint, ChildNode.movementFootprint,
    ChildNode.movementMap, ChildNode.centerMap, ChildNode.priorMap,
    ChildNode.nodeEncodingFootprint, Layout.nodeCode,
    Layout.codecDigit,
    ControlDecode.copy, Dispatcher.selectChildTarget,
    Dispatcher.copy, Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin, Dispatcher.cleanupInverseRegisters,
    Dispatcher.cleanupInverseMap, Layout.out,
    regs.injective.eq_iff]; decide

theorem prepare_writesWithin_internal
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (writeFootprint regs)
      (prepare workTapeCount controller regs) := by
  simp only [prepare, Cmd.seqList, Footprint.CmdWritesWithin]
  refine ⟨?_, ?_, ?_, restoreTarget_writesWithin_internal regs⟩
  · simp [ControlDecode.copy, writeFootprint,
      Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
  · exact cmdWritesWithin_mono
      (ControlDecode.decodeNode_writesWithin regs)
      (scratchFootprint_subset_internal regs)
  · exact cmdWritesWithin_mono
      (ChildNode.regenerateChild_writesWithin
        workTapeCount controller regs)
      (priorAssembly_subset_internal regs)

private theorem savedParentOut_not_mem_prior_internal
    (regs : NeighborhoodTrial.Registers controller) :
    savedParentOut regs ∉ ChildNode.priorAssemblyFootprint regs := by
  simp [savedParentOut, ChildNode.priorAssemblyFootprint,
    ChildNode.priorFootprint, ChildNode.centerFootprint,
    ChildNode.movementFootprint, ChildNode.movementMap,
    ChildNode.centerMap, ChildNode.priorMap,
    ChildNode.nodeEncodingFootprint, Layout.nodeCode,
    Layout.codecDigit, regs.injective.eq_iff]; decide

private theorem savedChild_not_mem_prior_internal
    (regs : NeighborhoodTrial.Registers controller) :
    ChildNode.savedChildIndex regs ∉
      ChildNode.priorAssemblyFootprint regs := by
  simp [ChildNode.savedChildIndex, Layout.codecScratch,
    ChildNode.priorAssemblyFootprint, ChildNode.priorFootprint,
    ChildNode.centerFootprint, ChildNode.movementFootprint,
    ChildNode.movementMap, ChildNode.centerMap, ChildNode.priorMap,
    ChildNode.nodeEncodingFootprint, Layout.nodeCode,
    Layout.codecDigit, regs.injective.eq_iff]; decide

private theorem workspaceIndex_not_mem_scratch_internal
    (regs : NeighborhoodTrial.Registers controller)
    (workspaceSlot : Fin 34)
    (hne :
      ∀ scratchSlot,
        ControlDecode.scratchMap scratchSlot ≠ workspaceSlot) :
    regs.index workspaceSlot ∉
      ControlDecode.scratchFootprint regs := by
  intro hmember
  simp only [ControlDecode.scratchFootprint, Finset.mem_image,
    Finset.mem_univ, true_and] at hmember
  obtain ⟨scratchSlot, heq⟩ := hmember
  exact hne scratchSlot (regs.injective heq)

private theorem savedParentOut_not_mem_scratch_internal
    (regs : NeighborhoodTrial.Registers controller) :
    savedParentOut regs ∉
      ControlDecode.scratchFootprint regs := by
  apply workspaceIndex_not_mem_scratch_internal regs (1 : Fin 34)
  intro slot
  fin_cases slot <;> decide

private theorem savedChild_not_mem_scratch_internal
    (regs : NeighborhoodTrial.Registers controller) :
    ChildNode.savedChildIndex regs ∉
      ControlDecode.scratchFootprint regs := by
  apply workspaceIndex_not_mem_scratch_internal regs (31 : Fin 34)
  intro slot
  fin_cases slot <;> decide

private theorem chunkRadix_not_mem_scratch_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Layout.chunkRadix regs ∉
      ControlDecode.scratchFootprint regs := by
  apply workspaceIndex_not_mem_scratch_internal regs (8 : Fin 34)
  intro slot
  fin_cases slot <;> decide

private theorem retained_not_mem_writeFootprint_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Layout.blockLength regs ∉ writeFootprint regs ∧
    Layout.horizon regs ∉ writeFootprint regs ∧
    Layout.chunkRadix regs ∉ writeFootprint regs ∧
    Layout.bankRadix regs ∉ writeFootprint regs ∧
    Layout.frameRadix regs ∉ writeFootprint regs ∧
    Layout.chunkCount regs ∉ writeFootprint regs ∧
    Layout.bankDigitCount regs ∉ writeFootprint regs ∧
    Layout.modulus regs ∉ writeFootprint regs ∧
    Layout.modulusPred regs ∉ writeFootprint regs ∧
    regs.index 32 ∉ writeFootprint regs ∧
    regs.index 33 ∉ writeFootprint regs := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp [writeFootprint, savedParentOut,
      ChildNode.priorAssemblyFootprint, ChildNode.priorFootprint,
      ChildNode.centerFootprint, ChildNode.movementFootprint,
      ChildNode.movementMap, ChildNode.centerMap, ChildNode.priorMap,
      ChildNode.nodeEncodingFootprint, Layout.blockLength,
      Layout.horizon, Layout.chunkRadix, Layout.bankRadix,
      Layout.frameRadix, Layout.chunkCount, Layout.bankDigitCount,
      Layout.modulus, Layout.modulusPred, Layout.nodeCode,
      Layout.codecDigit, regs.injective.eq_iff]
    decide

theorem parameters_of_readyPost_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store)
    (hparameters :
      Representation.Parameters regs instanceData initial)
    (hpost : ReadyPost regs node target initial final) :
    Representation.Parameters regs instanceData final := by
  rcases retained_not_mem_writeFootprint_internal regs with
    ⟨hblock, hhorizon, hradix, hbankRadix, hframeRadix,
      hchunkCount, hbankCount, hmodulus, hmodulusPred, _, _⟩
  exact
    { blockLength_eq := by
        rw [hpost.eq_outside _ hblock]
        exact hparameters.blockLength_eq
      horizon_eq := by
        rw [hpost.eq_outside _ hhorizon]
        exact hparameters.horizon_eq
      digitBase_eq := by
        rw [hpost.eq_outside _ hradix]
        exact hparameters.digitBase_eq
      bankBase_eq := by
        rw [hpost.eq_outside _ hbankRadix]
        exact hparameters.bankBase_eq
      frameBase_eq := by
        rw [hpost.eq_outside _ hframeRadix]
        exact hparameters.frameBase_eq
      chunkCount_eq := by
        rw [hpost.eq_outside _ hchunkCount]
        exact hparameters.chunkCount_eq
      bankDigitCount_eq := by
        rw [hpost.eq_outside _ hbankCount]
        exact hparameters.bankDigitCount_eq
      modulus_eq := by
        rw [hpost.eq_outside _ hmodulus]
        exact hparameters.modulus_eq
      modulusPred_eq := by
        rw [hpost.eq_outside _ hmodulusPred]
        exact hparameters.modulusPred_eq }

theorem readyPost_stackWord_eq_internal
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hpost : ReadyPost regs node target initial final) :
    final (Layout.frameStackRegisters regs).word =
      initial (Layout.frameStackRegisters regs).word := by
  rcases retained_not_mem_writeFootprint_internal regs with
    ⟨_, _, _, _, _, _, _, _, _, hstack, _⟩
  exact hpost.eq_outside _ hstack

theorem readyPost_bank_eq_internal
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hpost : ReadyPost regs node target initial final) :
    final regs.layout.bank = initial regs.layout.bank := by
  rcases retained_not_mem_writeFootprint_internal regs with
    ⟨_, _, _, _, _, _, _, _, _, _, hbank⟩
  exact hpost.eq_outside _ hbank

private theorem guess_not_mem_scratch_internal
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    controller.guess ∉ ControlDecode.scratchFootprint regs := by
  intro hmember
  simp only [ControlDecode.scratchFootprint, Finset.mem_image,
    Finset.mem_univ, true_and] at hmember
  obtain ⟨slot, hslot⟩ := hmember
  exact regs.index_ne_controller
    (ControlDecode.scratchMap slot) (2 : Fin 17) hslot

theorem prepare_frameChild_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot : NeighborhoodGraph.Slot)
    (kind : NeighborhoodGraph.PredecessorKind)
    (interval : ℕ)
    (hinterval : interval < instanceData.horizon)
    (hactive : Representation.ActiveFrame regs frame store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hbound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame)
    (hchild :
      store (ChildNode.savedChildIndex regs) =
        (NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount (kind, tape)).val)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval)) :
    ∃ final,
      Runs (prepare workTapeCount controller regs) store final ∧
      ReadyPost regs
        (frame.childNode
          (NeighborhoodGraph.predecessorIndexEquiv
            workTapeCount (kind, tape)))
        (frame.childTarget
          (NeighborhoodGraph.predecessorIndexEquiv
            workTapeCount (kind, tape))).val
        store final := by
  let saved :=
    Function.update store (savedParentOut regs)
      (store (Layout.out regs))
  have hsave :
      Runs
        (ControlDecode.copy
          (savedParentOut regs) (Layout.out regs))
        store saved := by
    apply copy_runs
    simp [savedParentOut, Layout.out, regs.injective.eq_iff]
  have hsavePreserves :
      ControlDecode.PreservesABI regs store saved := by
    constructor <;>
      simp [saved, savedParentOut, Function.update_of_ne,
        Layout.fuel, Layout.nodeCode, Layout.scalar, Layout.out,
        Layout.phaseCode, Layout.active, Layout.blockLength,
        Layout.horizon, Layout.chunkCount, Layout.chunkRadix,
        Layout.frameRadix, Layout.bankRadix, Layout.bankDigitCount,
        Layout.modulusPred, Layout.modulus, regs.injective.eq_iff]
  have hactiveSaved :
      Representation.ActiveFrame regs frame saved :=
    Representation.ActiveFrame.of_preservesABI
      regs frame store saved hactive hsavePreserves
  have hparametersSaved :
      Representation.Parameters regs instanceData saved :=
    Representation.Parameters.of_preservesABI
      regs store saved hparameters hsavePreserves
  obtain ⟨decoded, hdecode, hdecoded, _hactiveDecoded,
      _hparametersDecoded⟩ :=
    Representation.ActiveFrame.decodeNode_runs
      regs frame saved hactiveSaved hparametersSaved hbound
  have hdecodedChild :
      decoded (ChildNode.savedChildIndex regs) =
        (NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount (kind, tape)).val := by
    calc
      decoded (ChildNode.savedChildIndex regs) =
          saved (ChildNode.savedChildIndex regs) :=
        Footprint.runs_eq_outside
          (ControlDecode.decodeNode_writesWithin regs)
          hdecode (savedChild_not_mem_scratch_internal regs)
      _ = store (ChildNode.savedChildIndex regs) := by
        simp [saved, savedParentOut, ChildNode.savedChildIndex,
          Layout.codecScratch, regs.injective.eq_iff]
      _ = _ := hchild
  have hdecodedGuess : decoded controller.guess = code.val := by
    calc
      decoded controller.guess = saved controller.guess :=
        Footprint.runs_eq_outside
          (ControlDecode.decodeNode_writesWithin regs)
          hdecode (guess_not_mem_scratch_internal controller regs)
      _ = store controller.guess := by
        simp [saved, savedParentOut,
          (regs.index_ne_controller
            (1 : Fin 34) (2 : Fin 17)).symm]
      _ = code.val := hstoreGuess
  obtain ⟨regenerated, hregenerate, hnodeCode, _hdigit,
      hregenerateOutside⟩ :=
    ChildNode.regenerateChild_frameChild_runs
      code frame controller regs decoded parentTape tape parentSlot
      kind interval hinterval hdecoded hdecodedChild hdecodedGuess
      hguess hnode
  have hregeneratedSavedOut :
      regenerated (savedParentOut regs) =
        store (Layout.out regs) := by
    calc
      regenerated (savedParentOut regs) =
          decoded (savedParentOut regs) :=
        hregenerateOutside _
          (savedParentOut_not_mem_prior_internal regs)
      _ = saved (savedParentOut regs) :=
        Footprint.runs_eq_outside
          (ControlDecode.decodeNode_writesWithin regs)
          hdecode (savedParentOut_not_mem_scratch_internal regs)
      _ = store (Layout.out regs) := by
        simp [saved]
  have hregeneratedChild :
      regenerated (ChildNode.savedChildIndex regs) =
        (NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount (kind, tape)).val := by
    calc
      regenerated (ChildNode.savedChildIndex regs) =
          decoded (ChildNode.savedChildIndex regs) :=
        hregenerateOutside _
          (savedChild_not_mem_prior_internal regs)
      _ = _ := hdecodedChild
  let outRestored :=
    Function.update regenerated (Layout.out regs)
      (regenerated (savedParentOut regs))
  have hrestoreOut :
      Runs
        (ControlDecode.copy
          (Layout.out regs) (savedParentOut regs))
        regenerated outRestored := by
    apply copy_runs
    simp [savedParentOut, Layout.out, regs.injective.eq_iff]
  let childRestored :=
    Function.update outRestored
      (Dispatcher.decodedChild regs)
      (outRestored (ChildNode.savedChildIndex regs))
  have hrestoreChild :
      Runs
        (ControlDecode.copy
          (Dispatcher.decodedChild regs)
          (ChildNode.savedChildIndex regs))
        outRestored childRestored := by
    apply copy_runs
    simp [Dispatcher.decodedChild, ChildNode.savedChildIndex,
      Layout.codecScratch, regs.injective.eq_iff]
  let withOne :=
    Basic.exec
      (.imm (Dispatcher.cleanupInverseRegisters regs).one 1)
      childRestored
  have hone :
      Runs
        (.basic
          (.imm (Dispatcher.cleanupInverseRegisters regs).one 1))
        childRestored withOne :=
    Runs.basic _ _
  have hwithOneValue :
      withOne (Dispatcher.cleanupInverseRegisters regs).one = 1 := by
    simp [withOne, Basic.exec]
  obtain ⟨final, htarget, htargetPost⟩ :=
    Dispatcher.selectChildTarget_runs regs withOne hwithOneValue
  have hbeforeOut :
      withOne (Layout.out regs) = frame.out.val := by
    calc
      withOne (Layout.out regs) =
          childRestored (Layout.out regs) := by
        simp [withOne, Basic.exec, Dispatcher.cleanupInverseRegisters,
          Dispatcher.cleanupInverseMap, Layout.out,
          regs.injective.eq_iff]
      _ = outRestored (Layout.out regs) := by
        simp [childRestored, Dispatcher.decodedChild, Layout.out,
          regs.injective.eq_iff]
      _ = regenerated (savedParentOut regs) := by
        simp [outRestored]
      _ = store (Layout.out regs) := hregeneratedSavedOut
      _ = frame.out.val := hactive.out_eq
  have hbeforeChild :
      withOne (Dispatcher.decodedChild regs) =
        (NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount (kind, tape)).val := by
    calc
      withOne (Dispatcher.decodedChild regs) =
          childRestored (Dispatcher.decodedChild regs) := by
        simp [withOne, Basic.exec, Dispatcher.cleanupInverseRegisters,
          Dispatcher.cleanupInverseMap, Dispatcher.decodedChild,
          regs.injective.eq_iff]
      _ = outRestored (ChildNode.savedChildIndex regs) := by
        simp [childRestored]
      _ = regenerated (ChildNode.savedChildIndex regs) := by
        simp [outRestored, Layout.out, ChildNode.savedChildIndex,
          Layout.codecScratch, regs.injective.eq_iff]
      _ = _ := hregeneratedChild
  let selected :=
    NeighborhoodGraph.predecessorIndexEquiv
      workTapeCount (kind, tape)
  have hout :
      final (Layout.out regs) =
        (frame.childTarget selected).val := by
    rw [htargetPost.out_eq, hbeforeChild, hbeforeOut]
    exact Dispatcher.childTargetValue_eq_succAbove
      frame.out selected
  have hbase :
      decoded (Layout.chunkRadix regs) =
        store (Layout.chunkRadix regs) := by
    calc
      decoded (Layout.chunkRadix regs) =
          saved (Layout.chunkRadix regs) :=
        Footprint.runs_eq_outside
          (ControlDecode.decodeNode_writesWithin regs)
          hdecode (chunkRadix_not_mem_scratch_internal regs)
      _ = store (Layout.chunkRadix regs) := by
        simp [saved, savedParentOut, Layout.chunkRadix,
          regs.injective.eq_iff]
  have hfinalNode :
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (store (Layout.chunkRadix regs))
          (frame.childNode selected) := by
    calc
      final (Layout.nodeCode regs) =
          withOne (Layout.nodeCode regs) :=
        htargetPost.eq_of_ne _ (by
          simp [Layout.nodeCode, Layout.out, regs.injective.eq_iff])
          (by
            simp [Dispatcher.cleanupInverseRegisters,
              Dispatcher.cleanupInverseMap, Layout.nodeCode,
              regs.injective.eq_iff])
      _ = regenerated (Layout.nodeCode regs) := by
        simp [withOne, childRestored, outRestored, Basic.exec,
          Dispatcher.cleanupInverseRegisters,
          Dispatcher.cleanupInverseMap, Dispatcher.decodedChild,
          ChildNode.savedChildIndex, savedParentOut,
          Layout.codecScratch, Layout.nodeCode, Layout.out,
          regs.injective.eq_iff]
      _ = FrameCodec.encodeNode
          (decoded (Layout.chunkRadix regs))
          (frame.childNode selected) := by
        simpa [selected] using hnodeCode
      _ = _ := by rw [hbase]
  have hrun :
      Runs (prepare workTapeCount controller regs) store final := by
    simpa [prepare, restoreTarget, Cmd.seqList] using
      Runs.seq hsave
        (Runs.seq hdecode
          (Runs.seq hregenerate
            (Runs.seq hrestoreOut
              (Runs.seq hrestoreChild (Runs.seq hone htarget)))))
  refine ⟨final, hrun, ?_⟩
  exact
    { nodeCode_eq := by simpa [selected] using hfinalNode
      out_eq := by simpa [selected] using hout
      fuel_eq :=
        Footprint.runs_eq_outside
          (prepare_writesWithin_internal
            workTapeCount controller regs)
          hrun (by
            simp [writeFootprint, ChildNode.priorAssemblyFootprint,
              ChildNode.priorFootprint, ChildNode.centerFootprint,
              ChildNode.movementFootprint, ChildNode.movementMap,
              ChildNode.centerMap, ChildNode.priorMap, Layout.fuel,
              savedParentOut, ChildNode.nodeEncodingFootprint,
              Layout.nodeCode, Layout.codecDigit,
              regs.injective.eq_iff]; decide)
      eq_outside := fun address haddress =>
        Footprint.runs_eq_outside
          (prepare_writesWithin_internal
            workTapeCount controller regs)
          hrun haddress }

end Internal
end ChildReady
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
