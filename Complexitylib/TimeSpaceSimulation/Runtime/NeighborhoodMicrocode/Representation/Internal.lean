/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactEncoding
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ControlDecode
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameBounds
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameTransfer
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.StackDepth
import Complexitylib.Models.RandomAccessMachine.Structured.Switch.Defs

/-!
# Logical representation of neighborhood-scheduler query states -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace Representation
namespace Internal

variable {controller : SearchProgram.Registers}

theorem activeFrame_of_preservesABI_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (initial final : RAM.Structured.Store)
    (hframe : ActiveFrame regs frame initial)
    (hpreserves : ControlDecode.PreservesABI regs initial final) :
    ActiveFrame regs frame final := by
  constructor
  · rw [hpreserves.fuel_eq]
    exact hframe.fuel_eq
  · rw [hpreserves.nodeCode_eq]
    exact hframe.node_eq
  · rw [hpreserves.scalar_eq]
    exact hframe.scalar_eq
  · rw [hpreserves.out_eq]
    exact hframe.out_eq
  · rw [hpreserves.phaseCode_eq]
    exact hframe.phase_eq
  · rw [hpreserves.active_eq]
    exact hframe.active_eq

theorem parameters_of_preservesABI_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : RAM.Structured.Store)
    (hparameters : Parameters regs instanceData initial)
    (hpreserves : ControlDecode.PreservesABI regs initial final) :
    Parameters regs instanceData final := by
  constructor
  · rw [hpreserves.blockLength_eq]
    exact hparameters.blockLength_eq
  · rw [hpreserves.horizon_eq]
    exact hparameters.horizon_eq
  · rw [hpreserves.chunkRadix_eq]
    exact hparameters.digitBase_eq
  · rw [hpreserves.bankRadix_eq]
    exact hparameters.bankBase_eq
  · rw [hpreserves.frameRadix_eq]
    exact hparameters.frameBase_eq
  · rw [hpreserves.chunkCount_eq]
    exact hparameters.chunkCount_eq
  · rw [hpreserves.bankDigitCount_eq]
    exact hparameters.bankDigitCount_eq
  · rw [hpreserves.modulus_eq]
    exact hparameters.modulus_eq
  · rw [hpreserves.modulusPred_eq]
    exact hparameters.modulusPred_eq

theorem parameters_of_popParent_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : RAM.Structured.Store)
    (hparameters : Parameters regs instanceData initial)
    (hrun : RAM.Structured.Runs
      (FrameTransfer.popParent regs) initial final) :
    Parameters regs instanceData final := by
  have preserved (address : ℕ)
      (houtside : address ∉ FrameTransfer.writeFootprint regs) :
      final address = initial address :=
    RAM.Structured.Footprint.runs_eq_outside
      (FrameTransfer.popParent_writesWithin_writeFootprint regs)
      hrun houtside
  constructor
  · rw [preserved (Layout.blockLength regs) (by
      simp [FrameTransfer.writeFootprint, Layout.blockLength,
        regs.injective.eq_iff])]
    exact hparameters.blockLength_eq
  · rw [preserved (Layout.horizon regs) (by
      simp [FrameTransfer.writeFootprint, Layout.horizon,
        regs.injective.eq_iff])]
    exact hparameters.horizon_eq
  · rw [preserved (Layout.chunkRadix regs) (by
      simp [FrameTransfer.writeFootprint, Layout.chunkRadix,
        regs.injective.eq_iff])]
    exact hparameters.digitBase_eq
  · rw [preserved (Layout.bankRadix regs) (by
      simp [FrameTransfer.writeFootprint, Layout.bankRadix,
        regs.injective.eq_iff])]
    exact hparameters.bankBase_eq
  · rw [preserved (Layout.frameRadix regs) (by
      simp [FrameTransfer.writeFootprint, Layout.frameRadix,
        regs.injective.eq_iff])]
    exact hparameters.frameBase_eq
  · rw [preserved (Layout.chunkCount regs) (by
      simp [FrameTransfer.writeFootprint, Layout.chunkCount,
        regs.injective.eq_iff])]
    exact hparameters.chunkCount_eq
  · rw [preserved (Layout.bankDigitCount regs) (by
      simp [FrameTransfer.writeFootprint, Layout.bankDigitCount,
        regs.injective.eq_iff])]
    exact hparameters.bankDigitCount_eq
  · rw [preserved (Layout.modulus regs) (by
      simp [FrameTransfer.writeFootprint, Layout.modulus,
        regs.injective.eq_iff])]
    exact hparameters.modulus_eq
  · rw [preserved (Layout.modulusPred regs) (by
      simp [FrameTransfer.writeFootprint, Layout.modulusPred,
        regs.injective.eq_iff])]
    exact hparameters.modulusPred_eq

theorem parameters_of_pushParent_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : RAM.Structured.Store)
    (hparameters : Parameters regs instanceData initial)
    (hrun : RAM.Structured.Runs
      (FrameTransfer.pushParent regs) initial final) :
    Parameters regs instanceData final := by
  have preserved (address : ℕ)
      (houtside : address ∉ FrameTransfer.writeFootprint regs) :
      final address = initial address :=
    RAM.Structured.Footprint.runs_eq_outside
      (FrameTransfer.pushParent_writesWithin_writeFootprint regs)
      hrun houtside
  constructor
  · rw [preserved (Layout.blockLength regs) (by
      simp [FrameTransfer.writeFootprint, Layout.blockLength,
        regs.injective.eq_iff])]
    exact hparameters.blockLength_eq
  · rw [preserved (Layout.horizon regs) (by
      simp [FrameTransfer.writeFootprint, Layout.horizon,
        regs.injective.eq_iff])]
    exact hparameters.horizon_eq
  · rw [preserved (Layout.chunkRadix regs) (by
      simp [FrameTransfer.writeFootprint, Layout.chunkRadix,
        regs.injective.eq_iff])]
    exact hparameters.digitBase_eq
  · rw [preserved (Layout.bankRadix regs) (by
      simp [FrameTransfer.writeFootprint, Layout.bankRadix,
        regs.injective.eq_iff])]
    exact hparameters.bankBase_eq
  · rw [preserved (Layout.frameRadix regs) (by
      simp [FrameTransfer.writeFootprint, Layout.frameRadix,
        regs.injective.eq_iff])]
    exact hparameters.frameBase_eq
  · rw [preserved (Layout.chunkCount regs) (by
      simp [FrameTransfer.writeFootprint, Layout.chunkCount,
        regs.injective.eq_iff])]
    exact hparameters.chunkCount_eq
  · rw [preserved (Layout.bankDigitCount regs) (by
      simp [FrameTransfer.writeFootprint, Layout.bankDigitCount,
        regs.injective.eq_iff])]
    exact hparameters.bankDigitCount_eq
  · rw [preserved (Layout.modulus regs) (by
      simp [FrameTransfer.writeFootprint, Layout.modulus,
        regs.injective.eq_iff])]
    exact hparameters.modulus_eq
  · rw [preserved (Layout.modulusPred regs) (by
      simp [FrameTransfer.writeFootprint, Layout.modulusPred,
        regs.injective.eq_iff])]
    exact hparameters.modulusPred_eq

theorem pushParent_preservesABI_internal
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : RAM.Structured.Store}
    (hrun : RAM.Structured.Runs
      (FrameTransfer.pushParent regs) initial final) :
    ControlDecode.PreservesABI regs initial final := by
  have preserved (address : ℕ)
      (houtside : address ∉ FrameTransfer.pushWriteFootprint regs) :
      final address = initial address :=
    RAM.Structured.Footprint.runs_eq_outside
      (FrameTransfer.pushParent_writesWithin_pushWriteFootprint regs)
      hrun houtside
  constructor
  · exact preserved (Layout.fuel regs) (by
      simp [FrameTransfer.pushWriteFootprint, Layout.fuel,
        regs.injective.eq_iff])
  · exact preserved (Layout.nodeCode regs) (by
      simp [FrameTransfer.pushWriteFootprint, Layout.nodeCode,
        regs.injective.eq_iff])
  · exact preserved (Layout.scalar regs) (by
      simp [FrameTransfer.pushWriteFootprint, Layout.scalar,
        regs.injective.eq_iff])
  · exact preserved (Layout.out regs) (by
      simp [FrameTransfer.pushWriteFootprint, Layout.out,
        regs.injective.eq_iff])
  · exact preserved (Layout.phaseCode regs) (by
      simp [FrameTransfer.pushWriteFootprint, Layout.phaseCode,
        regs.injective.eq_iff])
  · exact preserved (Layout.active regs) (by
      simp [FrameTransfer.pushWriteFootprint, Layout.active,
        regs.injective.eq_iff])
  · exact preserved (Layout.blockLength regs) (by
      simp [FrameTransfer.pushWriteFootprint, Layout.blockLength,
        regs.injective.eq_iff])
  · exact preserved (Layout.horizon regs) (by
      simp [FrameTransfer.pushWriteFootprint, Layout.horizon,
        regs.injective.eq_iff])
  · exact preserved (Layout.chunkCount regs) (by
      simp [FrameTransfer.pushWriteFootprint, Layout.chunkCount,
        regs.injective.eq_iff])
  · exact preserved (Layout.chunkRadix regs) (by
      simp [FrameTransfer.pushWriteFootprint, Layout.chunkRadix,
        regs.injective.eq_iff])
  · exact preserved (Layout.frameRadix regs) (by
      simp [FrameTransfer.pushWriteFootprint, Layout.frameRadix,
        regs.injective.eq_iff])
  · exact preserved (Layout.bankRadix regs) (by
      simp [FrameTransfer.pushWriteFootprint, Layout.bankRadix,
        regs.injective.eq_iff])
  · exact preserved (Layout.bankDigitCount regs) (by
      simp [FrameTransfer.pushWriteFootprint, Layout.bankDigitCount,
        regs.injective.eq_iff])
  · exact preserved (Layout.modulusPred regs) (by
      simp [FrameTransfer.pushWriteFootprint, Layout.modulusPred,
        regs.injective.eq_iff])
  · exact preserved (Layout.modulus regs) (by
      simp [FrameTransfer.pushWriteFootprint, Layout.modulus,
        regs.injective.eq_iff])

theorem popParent_bank_eq_internal
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : RAM.Structured.Store}
    (hrun : RAM.Structured.Runs
      (FrameTransfer.popParent regs) initial final) :
    final regs.layout.bank = initial regs.layout.bank := by
  apply RAM.Structured.Footprint.runs_eq_outside
    (FrameTransfer.popParent_writesWithin_writeFootprint regs) hrun
  simp [FrameTransfer.writeFootprint, NeighborhoodTrial.Registers.layout,
    regs.injective.eq_iff]

theorem pushParent_bank_eq_internal
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : RAM.Structured.Store}
    (hrun : RAM.Structured.Runs
      (FrameTransfer.pushParent regs) initial final) :
    final regs.layout.bank = initial regs.layout.bank := by
  apply RAM.Structured.Footprint.runs_eq_outside
    (FrameTransfer.pushParent_writesWithin_writeFootprint regs) hrun
  simp [FrameTransfer.writeFootprint, NeighborhoodTrial.Registers.layout,
    regs.injective.eq_iff]

theorem stack_pushParent_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (current : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (store : RAM.Structured.Store)
    (hstack : Stack regs (current :: rest) store)
    (hparameters : Parameters regs instanceData store)
    (hbound : NeighborhoodScheduler.FrameBounds.FrameBound current) :
    ∃ final,
      RAM.Structured.Runs
        (FrameTransfer.pushParent regs) store final ∧
      FrameTransfer.RepresentsStack regs
        (digitBase instanceData) (frameBase instanceData)
        (current :: rest) final ∧
      Parameters regs instanceData final ∧
      final regs.layout.bank = store regs.layout.bank := by
  have hbase :
      0 < digitBase instanceData := by
    have hlarge :=
      CandidateParameters.RadixBounds.one_lt_domainSize
        tm.Q workTapeCount instanceData.candidateTime
    simpa [digitBase] using (show
      0 <
        CandidateParameters.domainSize
          tm.Q workTapeCount instanceData.candidateTime by omega)
  obtain ⟨final, hrun, hrepresented⟩ :=
    FrameTransfer.pushParent_frame_runs
      regs store (digitBase instanceData) (frameBase instanceData)
      current rest hbase
      (FrameBounds.frameBound_scalar_lt current hbound)
      hparameters.digitBase_eq
      (by simpa [fieldBase] using hparameters.bankBase_eq)
      hstack.1.fuel_eq
      hstack.1.node_eq
      hstack.1.scalar_eq
      hstack.1.out_eq
      hstack.1.phase_eq
      (by simpa using hparameters.frameBase_eq)
      hstack.2
  exact
    ⟨final, hrun, hrepresented,
      parameters_of_pushParent_internal
        regs store final hparameters hrun,
      pushParent_bank_eq_internal regs hrun⟩

theorem stack_popParent_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (current : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (store : RAM.Structured.Store)
    (hstack : Stack regs (current :: rest) store)
    (hparameters : Parameters regs instanceData store)
    (hbounds : ∀ frame ∈ rest,
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    ∃ final,
      RAM.Structured.Runs
        (FrameTransfer.popParent regs) store final ∧
      Stack regs rest final ∧
      Parameters regs instanceData final ∧
      final regs.layout.bank = store regs.layout.bank := by
  have hbase :
      0 < digitBase instanceData := by
    have hlarge :=
      CandidateParameters.RadixBounds.one_lt_domainSize
        tm.Q workTapeCount instanceData.candidateTime
    simpa [digitBase] using (show
      0 <
        CandidateParameters.domainSize
          tm.Q workTapeCount instanceData.candidateTime by omega)
  cases rest with
  | nil =>
      obtain ⟨final, hrun, hactive, hrepresented⟩ :=
        FrameTransfer.popParent_empty_runs
          regs store (digitBase instanceData) (frameBase instanceData)
          hstack.2
      exact
        ⟨final, hrun, ⟨hactive, hrepresented⟩,
          parameters_of_popParent_internal
            regs store final hparameters hrun,
          popParent_bank_eq_internal regs hrun⟩
  | cons frame tail =>
      have hbound : NeighborhoodScheduler.FrameBounds.FrameBound frame :=
        hbounds frame (by simp)
      obtain ⟨final, hrun, hloaded, hrepresented, _hframeBase⟩ :=
        FrameTransfer.popParent_frame_runs
          regs store (digitBase instanceData) (frameBase instanceData)
          frame tail hbase
          (FrameBounds.frameBound_frameFits frame hbound)
          (FrameBounds.frameBound_scalar_lt frame hbound)
          (FrameBounds.frameBound_shiftedCode_lt_frameRadix frame hbound)
          hparameters.digitBase_eq
          (by simpa [fieldBase] using hparameters.bankBase_eq)
          (by simpa using hparameters.frameBase_eq)
          hstack.2
      have hactiveFrame : ActiveFrame regs frame final :=
        ⟨hloaded.fuel_eq, hloaded.nodeCode_eq,
          hloaded.scalar_eq, hloaded.out_eq,
          hloaded.phaseCode_eq, hloaded.active_eq⟩
      exact
        ⟨final, hrun, ⟨hactiveFrame, hrepresented⟩,
          parameters_of_popParent_internal
            regs store final hparameters hrun,
          popParent_bank_eq_internal regs hrun⟩

theorem queryState_popParent_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (current : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : RAM.Structured.Store)
    (hquery :
      QueryState regs instanceData
        { stack := current :: rest
          registers := logicalBank }
        store) :
    ∃ final,
      RAM.Structured.Runs
        (FrameTransfer.popParent regs) store final ∧
      QueryState regs instanceData
        { stack := rest
          registers := logicalBank }
        final := by
  have hrestBounds :
      ∀ frame ∈ rest,
        NeighborhoodScheduler.FrameBounds.FrameBound frame := by
    intro frame hframe
    exact hquery.bounds frame (by simp [hframe])
  obtain ⟨final, hrun, hstack, hparameters, hbankEq⟩ :=
    stack_popParent_runs_internal
      regs current rest store hquery.stack hquery.parameters
      hrestBounds
  refine ⟨final, hrun, ?_⟩
  exact
    { parameters := hparameters
      stack := hstack
      bank := by
        rw [hbankEq]
        exact hquery.bank
      bank_lt := by
        rw [hbankEq]
        exact hquery.bank_lt
      bounds := hrestBounds }

theorem activeFrame_decodeNode_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (store : RAM.Structured.Store)
    (hactive : ActiveFrame regs frame store)
    (hparameters : Parameters regs instanceData store)
    (hbound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    ∃ final,
      RAM.Structured.Runs (ControlDecode.decodeNode regs) store final ∧
      ControlDecode.EncodedNodePost regs frame.node final ∧
      ActiveFrame regs frame final ∧
      Parameters regs instanceData final := by
  have hbase :
      0 < digitBase instanceData := by
    have hlarge :=
      CandidateParameters.RadixBounds.one_lt_domainSize
        tm.Q workTapeCount instanceData.candidateTime
    have hpositive :
        0 <
          CandidateParameters.domainSize
            tm.Q workTapeCount instanceData.candidateTime := by
      omega
    simpa [digitBase] using hpositive
  obtain ⟨final, hrun, _hpost, hdecoded, hpreserves⟩ :=
    ControlDecode.decodeNode_encodeNode_runs
      regs store (digitBase instanceData) frame.node hbase
      (FrameBounds.frameBound_nodeDigits_fit frame hbound)
      hactive.node_eq hparameters.digitBase_eq
  exact
    ⟨final, hrun, hdecoded,
      activeFrame_of_preservesABI_internal
        regs frame store final hactive hpreserves,
      parameters_of_preservesABI_internal
        regs store final hparameters hpreserves⟩

theorem activeFrame_decodePhase_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (store : RAM.Structured.Store)
    (hactive : ActiveFrame regs frame store)
    (hparameters : Parameters regs instanceData store)
    (hbound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    ∃ final,
      RAM.Structured.Runs (ControlDecode.decodePhase regs) store final ∧
      ControlDecode.EncodedPhasePost regs frame.phase final ∧
      ActiveFrame regs frame final ∧
      Parameters regs instanceData final := by
  have hbase :
      0 < digitBase instanceData := by
    have hlarge :=
      CandidateParameters.RadixBounds.one_lt_domainSize
        tm.Q workTapeCount instanceData.candidateTime
    have hpositive :
        0 <
          CandidateParameters.domainSize
            tm.Q workTapeCount instanceData.candidateTime := by
      omega
    simpa [digitBase] using hpositive
  obtain ⟨final, hrun, _hpost, hdecoded, hpreserves⟩ :=
    ControlDecode.decodePhase_encodePhase_runs
      regs store (digitBase instanceData) frame.phase hbase
      (FrameBounds.frameBound_phaseDigits_fit frame hbound)
      (FrameBounds.frameBound_phaseResidue_lt frame hbound)
      (FrameBounds.frameBound_phaseResiduesLeft_lt frame hbound)
      hactive.phase_eq hparameters.digitBase_eq (by
        simpa [fieldBase] using hparameters.bankBase_eq)
  exact
    ⟨final, hrun, hdecoded,
      activeFrame_of_preservesABI_internal
        regs frame store final hactive hpreserves,
      parameters_of_preservesABI_internal
        regs store final hparameters hpreserves⟩

private theorem workspaceIndex_not_mem_decodeScratch_internal
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

private theorem frameStackWord_not_mem_decodeScratch_internal
    (regs : NeighborhoodTrial.Registers controller) :
    (Layout.frameStackRegisters regs).word ∉
      ControlDecode.scratchFootprint regs := by
  apply workspaceIndex_not_mem_decodeScratch_internal regs (32 : Fin 34)
  intro slot
  fin_cases slot <;> decide

private theorem bank_not_mem_decodeScratch_internal
    (regs : NeighborhoodTrial.Registers controller) :
    regs.layout.bank ∉ ControlDecode.scratchFootprint regs := by
  apply workspaceIndex_not_mem_decodeScratch_internal regs (33 : Fin 34)
  intro slot
  fin_cases slot <;> decide

theorem queryState_decodeNode_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : RAM.Structured.Store)
    (hquery :
      QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store) :
    ∃ final,
      RAM.Structured.Runs
        (ControlDecode.decodeNode regs) store final ∧
      ControlDecode.EncodedNodePost regs frame.node final ∧
      QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        final := by
  have hbound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame :=
    hquery.bounds frame (by simp)
  obtain ⟨final, hrun, hdecoded, hactive, hparameters⟩ :=
    activeFrame_decodeNode_runs_internal
      regs frame store hquery.stack.1 hquery.parameters hbound
  have hstackWord :
      final (Layout.frameStackRegisters regs).word =
        store (Layout.frameStackRegisters regs).word :=
    RAM.Structured.Footprint.runs_eq_outside
      (ControlDecode.decodeNode_writesWithin regs) hrun
      (frameStackWord_not_mem_decodeScratch_internal regs)
  have htail :
      FrameTransfer.RepresentsStack regs
        (digitBase instanceData) (frameBase instanceData) rest final := by
    unfold FrameTransfer.RepresentsStack at hstackWord ⊢
    exact hstackWord.trans hquery.stack.2
  have hbankWord :
      final regs.layout.bank = store regs.layout.bank :=
    RAM.Structured.Footprint.runs_eq_outside
      (ControlDecode.decodeNode_writesWithin regs) hrun
      (bank_not_mem_decodeScratch_internal regs)
  refine ⟨final, hrun, hdecoded, ?_⟩
  exact
    { parameters := hparameters
      stack := ⟨hactive, htail⟩
      bank := by
        rw [hbankWord]
        exact hquery.bank
      bank_lt := by
        rw [hbankWord]
        exact hquery.bank_lt
      bounds := hquery.bounds }

theorem queryState_decodePhase_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : RAM.Structured.Store)
    (hquery :
      QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store) :
    ∃ final,
      RAM.Structured.Runs
        (ControlDecode.decodePhase regs) store final ∧
      ControlDecode.EncodedPhasePost regs frame.phase final ∧
      QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        final := by
  have hbound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame :=
    hquery.bounds frame (by simp)
  obtain ⟨final, hrun, hdecoded, hactive, hparameters⟩ :=
    activeFrame_decodePhase_runs_internal
      regs frame store hquery.stack.1 hquery.parameters hbound
  have hstackWord :
      final (Layout.frameStackRegisters regs).word =
        store (Layout.frameStackRegisters regs).word :=
    RAM.Structured.Footprint.runs_eq_outside
      (ControlDecode.decodePhase_writesWithin regs) hrun
      (frameStackWord_not_mem_decodeScratch_internal regs)
  have htail :
      FrameTransfer.RepresentsStack regs
        (digitBase instanceData) (frameBase instanceData) rest final := by
    unfold FrameTransfer.RepresentsStack at hstackWord ⊢
    exact hstackWord.trans hquery.stack.2
  have hbankWord :
      final regs.layout.bank = store regs.layout.bank :=
    RAM.Structured.Footprint.runs_eq_outside
      (ControlDecode.decodePhase_writesWithin regs) hrun
      (bank_not_mem_decodeScratch_internal regs)
  refine ⟨final, hrun, hdecoded, ?_⟩
  exact
    { parameters := hparameters
      stack := ⟨hactive, htail⟩
      bank := by
        rw [hbankWord]
        exact hquery.bank
      bank_lt := by
        rw [hbankWord]
        exact hquery.bank_lt
      bounds := hquery.bounds }

theorem queryState_clearedTag_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : RAM.Structured.Store)
    (hquery :
      QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store) :
    QueryState regs instanceData
      { stack := frame :: rest
        registers := logicalBank }
      (RAM.Structured.Switch.cleared store
        (ControlDecode.tag regs)) := by
  let cleared :=
    RAM.Structured.Switch.cleared store
      (ControlDecode.tag regs)
  have hphysical (slot : Fin 34) (hne : slot ≠ 6) :
      cleared (regs.index slot) = store (regs.index slot) := by
    simp [cleared, RAM.Structured.Switch.cleared,
      ControlDecode.tag, regs.injective.eq_iff, hne]
  have hactive :
      ActiveFrame regs frame cleared :=
    { fuel_eq := by
        rw [hphysical (22 : Fin 34) (by decide)]
        exact hquery.stack.1.fuel_eq
      node_eq := by
        rw [hphysical (23 : Fin 34) (by decide)]
        exact hquery.stack.1.node_eq
      scalar_eq := by
        rw [hphysical (25 : Fin 34) (by decide)]
        exact hquery.stack.1.scalar_eq
      out_eq := by
        rw [hphysical (26 : Fin 34) (by decide)]
        exact hquery.stack.1.out_eq
      phase_eq := by
        rw [hphysical (27 : Fin 34) (by decide)]
        exact hquery.stack.1.phase_eq
      active_eq := by
        rw [hphysical (28 : Fin 34) (by decide)]
        exact hquery.stack.1.active_eq }
  have htail :
      FrameTransfer.RepresentsStack regs
        (digitBase instanceData) (frameBase instanceData)
        rest cleared := by
    unfold FrameTransfer.RepresentsStack
    change cleared (regs.index 32) = _
    rw [hphysical (32 : Fin 34) (by decide)]
    exact hquery.stack.2
  have hparameters :
      Parameters regs instanceData cleared :=
    { blockLength_eq := by
        rw [hphysical (2 : Fin 34) (by decide)]
        exact hquery.parameters.blockLength_eq
      horizon_eq := by
        rw [hphysical (3 : Fin 34) (by decide)]
        exact hquery.parameters.horizon_eq
      digitBase_eq := by
        rw [hphysical (8 : Fin 34) (by decide)]
        exact hquery.parameters.digitBase_eq
      bankBase_eq := by
        rw [hphysical (14 : Fin 34) (by decide)]
        exact hquery.parameters.bankBase_eq
      frameBase_eq := by
        rw [hphysical (13 : Fin 34) (by decide)]
        exact hquery.parameters.frameBase_eq
      chunkCount_eq := by
        rw [hphysical (7 : Fin 34) (by decide)]
        exact hquery.parameters.chunkCount_eq
      bankDigitCount_eq := by
        rw [hphysical (15 : Fin 34) (by decide)]
        exact hquery.parameters.bankDigitCount_eq
      modulus_eq := by
        rw [hphysical (24 : Fin 34) (by decide)]
        exact hquery.parameters.modulus_eq
      modulusPred_eq := by
        rw [hphysical (16 : Fin 34) (by decide)]
        exact hquery.parameters.modulusPred_eq }
  have hbank :
      cleared regs.layout.bank = store regs.layout.bank := by
    change cleared (regs.index 33) = store (regs.index 33)
    exact hphysical (33 : Fin 34) (by decide)
  change
    QueryState regs instanceData
      { stack := frame :: rest
        registers := logicalBank }
      cleared
  exact
    { parameters := hparameters
      stack := ⟨hactive, htail⟩
      bank := by
        rw [hbank]
        exact hquery.bank
      bank_lt := by
        rw [hbank]
        exact hquery.bank_lt
      bounds := hquery.bounds }

theorem queryState_of_preservesABI_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (initial final : RAM.Structured.Store)
    (hquery :
      QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        initial)
    (hpreserves :
      ControlDecode.PreservesABI regs initial final)
    (hstack :
      final (Layout.frameStackRegisters regs).word =
        initial (Layout.frameStackRegisters regs).word)
    (hbank :
      final regs.layout.bank = initial regs.layout.bank) :
    QueryState regs instanceData
      { stack := frame :: rest
        registers := logicalBank }
      final := by
  refine
    { parameters :=
        parameters_of_preservesABI_internal
          regs initial final hquery.parameters hpreserves
      stack := ⟨
        activeFrame_of_preservesABI_internal
          regs frame initial final hquery.stack.1 hpreserves, ?_⟩
      bank := ?_
      bank_lt := ?_
      bounds := hquery.bounds }
  · unfold FrameTransfer.RepresentsStack
    exact hstack.trans hquery.stack.2
  · rw [hbank]
    exact hquery.bank
  · rw [hbank]
    exact hquery.bank_lt

theorem payloadWidth_eq_booleanWidth_internal
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    NeighborhoodExecutableEvaluation.payloadWidth
        tm instanceData.blockLength =
      CandidateParameters.booleanWidth
        tm.Q instanceData.candidateTime := by
  rw [NeighborhoodExecutableEvaluation.payloadWidth,
    ComputationGraph.CompactEncoding.width_eq,
    instanceData.blockLength_eq]
  rfl

theorem fieldBase_eq_bankRadix_internal
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    fieldBase instanceData =
      CandidateParameters.bankRadix
        tm.Q workTapeCount instanceData.candidateTime := by
  rw [fieldBase, FrameCodec.scalarDigitCount]
  exact
    (CandidateParameters.RadixBounds.bankRadix_eq_domainSize_sq
      tm.Q workTapeCount instanceData.candidateTime).symm

theorem bankCoordinateCount_eq_internal
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1) *
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) =
      CandidateParameters.bankDigitCount
        tm.Q workTapeCount instanceData.candidateTime := by
  rw [payloadWidth_eq_booleanWidth_internal instanceData]
  rfl

theorem encodeStack_eq_packFrames_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (digitBase frameBase : ℕ)
    (frames : List (NeighborhoodScheduler.Frame tm instanceData)) :
    FrameTransfer.encodeStack digitBase frameBase frames =
      NeighborhoodScheduler.StackDepth.packFrames frameBase
        (fun frame =>
          FrameCodec.encodeFrame digitBase frame + 1)
        frames := by
  induction frames with
  | nil =>
      rfl
  | cons frame rest ih =>
      simp only [FrameTransfer.encodeStack,
        NeighborhoodScheduler.StackDepth.packFrames, ih]

theorem stack_active_zero_iff_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frames : List (NeighborhoodScheduler.Frame tm instanceData))
    (store : RAM.Structured.Store)
    (hstack : Stack regs frames store) :
    store (Layout.active regs) = 0 ↔ frames = [] := by
  cases frames with
  | nil =>
      simp only [Stack] at hstack
      exact ⟨fun _ => rfl, fun _ => hstack.1⟩
  | cons frame rest =>
      simp only [Stack] at hstack
      constructor
      · intro hzero
        have hone := hstack.1.active_eq
        omega
      · intro hempty
        contradiction

theorem stack_represents_tail_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frames : List (NeighborhoodScheduler.Frame tm instanceData))
    (store : RAM.Structured.Store)
    (hstack : Stack regs frames store) :
    FrameTransfer.RepresentsStack regs
      (digitBase instanceData) (frameBase instanceData)
      frames.tail store := by
  cases frames with
  | nil =>
      exact hstack.2
  | cons frame rest =>
      exact hstack.2

theorem queryState_active_zero_iff_terminal_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (state : NeighborhoodScheduler.State tm instanceData)
    (store : RAM.Structured.Store)
    (hrep : QueryState regs instanceData state store) :
    store (Layout.active regs) = 0 ↔ state.Terminal := by
  rw [stack_active_zero_iff_internal
    regs state.stack store hrep.stack]
  simp [NeighborhoodScheduler.State.Terminal]

theorem queryState_head_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (state : NeighborhoodScheduler.State tm instanceData)
    (store : RAM.Structured.Store)
    (hframes : state.stack = frame :: rest)
    (hrep : QueryState regs instanceData state store) :
    ActiveFrame regs frame store ∧
      FrameTransfer.RepresentsStack regs
        (digitBase instanceData) (frameBase instanceData) rest store := by
  have hstack := hrep.stack
  rw [hframes] at hstack
  exact hstack

theorem queryState_empty_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (state : NeighborhoodScheduler.State tm instanceData)
    (store : RAM.Structured.Store)
    (hempty : state.stack = [])
    (hrep : QueryState regs instanceData state store) :
    store (Layout.active regs) = 0 ∧
      FrameTransfer.RepresentsStack regs
        (digitBase instanceData) (frameBase instanceData)
        ([] :
          List (NeighborhoodScheduler.Frame tm instanceData))
        store := by
  have hstack := hrep.stack
  rw [hempty] at hstack
  exact hstack

theorem queryState_stack_lt_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (state : NeighborhoodScheduler.State tm instanceData)
    (store : RAM.Structured.Store)
    (hrep : QueryState regs instanceData state store)
    (hcapacity :
      NeighborhoodScheduler.StackDepth.StackInvariant
        instanceData.horizon state) :
    store regs.layout.stack <
      frameBase instanceData ^ instanceData.horizon := by
  have hbase :
      1 ≤ frameBase instanceData := by
    rw [frameBase,
      CandidateParameters.RadixBounds.frameRadix_eq_domainSize_pow]
    apply Nat.one_le_pow
    have :=
      CandidateParameters.RadixBounds.one_lt_domainSize
        tm.Q workTapeCount instanceData.candidateTime
    omega
  have hdigit :
      ∀ frame ∈ state.stack.tail,
        FrameCodec.encodeFrame (digitBase instanceData) frame + 1 <
          frameBase instanceData := by
    intro frame hframe
    apply FrameBounds.frameBound_shiftedCode_lt_frameRadix
    exact hrep.bounds frame (List.mem_of_mem_tail hframe)
  have hpacked :=
    NeighborhoodScheduler.StackDepth.packSuspended_lt_pow_of_stackInvariant
      (frameBase instanceData)
      (fun frame =>
        FrameCodec.encodeFrame (digitBase instanceData) frame + 1)
      instanceData.horizon state hbase hcapacity hdigit
  have hstack :=
    stack_represents_tail_internal regs state.stack store hrep.stack
  change
    store (Layout.frameStackRegisters regs).word <
      frameBase instanceData ^ instanceData.horizon
  rw [hstack]
  rw [encodeStack_eq_packFrames_internal]
  exact hpacked

theorem queryState_bank_lt_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (state : NeighborhoodScheduler.State tm instanceData)
    (store : RAM.Structured.Store)
    (hrep : QueryState regs instanceData state store) :
    store regs.layout.bank <
      CandidateParameters.bankRadix
          tm.Q workTapeCount instanceData.candidateTime ^
        CandidateParameters.bankDigitCount
          tm.Q workTapeCount instanceData.candidateTime := by
  rw [← fieldBase_eq_bankRadix_internal instanceData,
    ← bankCoordinateCount_eq_internal instanceData]
  exact hrep.bank_lt

theorem queryState_boundedWorkspace_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (state : NeighborhoodScheduler.State tm instanceData)
    (store : RAM.Structured.Store)
    (hrep : QueryState regs instanceData state store)
    (hcapacity :
      NeighborhoodScheduler.StackDepth.StackInvariant
        instanceData.horizon state)
    (hfixed : ∀ index,
      store (regs.layout.fixed index) <
        2 ^ NeighborhoodGraph.WorkspaceAccounting.scratchBits
          tm.Q workTapeCount instanceData.candidateTime) :
    NeighborhoodProgram.BoundedWorkspace
      tm.Q workTapeCount instanceData.candidateTime
      (store regs.layout.stack) (store regs.layout.bank)
      (fun index => store (regs.layout.fixed index)) := by
  constructor
  · have hstack :=
      queryState_stack_lt_internal
        regs state store hrep hcapacity
    rw [instanceData.horizon_eq] at hstack
    exact hstack
  · exact
      queryState_bank_lt_internal
        regs state store hrep
  · exact hfixed

end Internal
end Representation
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
