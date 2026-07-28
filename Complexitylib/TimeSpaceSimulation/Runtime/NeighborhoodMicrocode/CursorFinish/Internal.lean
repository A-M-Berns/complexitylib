/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CursorFinish.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Dispatcher
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation

/-!
# Exhausted scheduler-cursor transitions -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CursorFinish
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} {command : Cmd}
    (hwrites : Footprint.CmdWritesWithin small command)
    (hsubset : small ⊆ large) :
    Footprint.CmdWritesWithin large command := by
  induction command with
  | skip =>
      trivial
  | basic op =>
      cases op <;>
        simp only [Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin] at hwrites ⊢
      all_goals exact hsubset hwrites
  | seq first second ihFirst ihSecond =>
      exact ⟨ihFirst hwrites.1, ihSecond hwrites.2⟩
  | ifZero test onZero onNonzero ihZero ihNonzero =>
      exact ⟨ihZero hwrites.1, ihNonzero hwrites.2⟩
  | whileNonzero test body ih =>
      exact ih hwrites

private theorem phaseWriteFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    phaseWriteFootprint regs ⊆ regs.layout.footprint := by
  intro address haddress
  rw [phaseWriteFootprint, Finset.mem_union] at haddress
  rcases haddress with hdecode | hphase
  · exact ControlDecode.scratchFootprint_subset_layout regs hdecode
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hphase
    rcases hphase with rfl | rfl | rfl
    · exact Layout.index_mem_layout_footprint regs 27
    · simpa [Layout.frameCodecRegisters, Layout.frameCodecMap] using
        Layout.index_mem_layout_footprint regs 4
    · exact Layout.index_mem_layout_footprint regs 30

private theorem decodeScratch_mem_phase
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 7) :
    regs.index (ControlDecode.scratchMap slot) ∈
      phaseWriteFootprint regs := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

private theorem encodePhase_writesWithin_phase
    (regs : NeighborhoodTrial.Registers controller)
    (tag residue residuesLeft child nextChild : ℕ) :
    Footprint.CmdWritesWithin (phaseWriteFootprint regs)
      (Dispatcher.encodePhase regs tag residue residuesLeft
        child nextChild) := by
  simp [Dispatcher.encodePhase, Dispatcher.encodePhaseOps,
    Cmd.basics, Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin, phaseWriteFootprint]

private theorem combineAfterDecode_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (phaseWriteFootprint regs)
      (combineAfterDecode regs) := by
  simp only [combineAfterDecode, Cmd.seqList,
    Footprint.CmdWritesWithin]
  exact
    ⟨by
        simpa [Footprint.BasicWritesWithin,
          ControlDecode.scratchMap] using
            decodeScratch_mem_phase regs (4 : Fin 7),
      by
        simpa [Footprint.BasicWritesWithin,
          ControlDecode.scratchMap] using
            decodeScratch_mem_phase regs (5 : Fin 7),
      encodePhase_writesWithin_phase regs 2
        (Dispatcher.decodedResidue regs)
        (Dispatcher.decodedResiduesLeft regs)
        (Dispatcher.decodedChild regs)
        (Dispatcher.decodedNextChild regs)⟩

theorem nextResidueAfterDecode_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (phaseWriteFootprint regs)
      (nextResidueAfterDecode regs) := by
  simp only [nextResidueAfterDecode, Cmd.seqList,
    Footprint.CmdWritesWithin]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Footprint.BasicWritesWithin, phaseWriteFootprint]
  · simpa [Footprint.BasicWritesWithin,
      ControlDecode.scratchMap] using
        decodeScratch_mem_phase regs (2 : Fin 7)
  · simpa [Footprint.BasicWritesWithin,
      ControlDecode.scratchMap] using
        decodeScratch_mem_phase regs (3 : Fin 7)
  · simpa [Footprint.BasicWritesWithin,
      ControlDecode.scratchMap] using
        decodeScratch_mem_phase regs (4 : Fin 7)
  · simpa [Footprint.BasicWritesWithin,
      ControlDecode.scratchMap] using
        decodeScratch_mem_phase regs (5 : Fin 7)
  · exact
      encodePhase_writesWithin_phase regs 1
        (Dispatcher.decodedResidue regs)
        (Dispatcher.decodedResiduesLeft regs)
        (Dispatcher.decodedChild regs)
        (Dispatcher.decodedNextChild regs)

theorem finishPrepare_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (finishPrepare regs) := by
  simp only [finishPrepare, Footprint.CmdWritesWithin]
  exact
    ⟨ControlDecode.decodePhase_layout_writesWithin regs,
      cmdWritesWithin_mono
        (combineAfterDecode_writesWithin regs)
        (phaseWriteFootprint_subset_layout regs)⟩

theorem finishCleanup_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (finishCleanup regs) := by
  simp only [finishCleanup, Footprint.CmdWritesWithin]
  exact
    ⟨ControlDecode.decodePhase_layout_writesWithin regs,
      ⟨FrameTransfer.popParent_writesWithin regs,
        cmdWritesWithin_mono
          (nextResidueAfterDecode_writesWithin_internal regs)
          (phaseWriteFootprint_subset_layout regs)⟩⟩

private theorem physical_not_mem_decodeScratch
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hslot : ∀ index, ControlDecode.scratchMap index ≠ slot) :
    regs.index slot ∉ ControlDecode.scratchFootprint regs := by
  simp only [ControlDecode.scratchFootprint, Finset.mem_image,
    Finset.mem_univ, true_and, not_exists]
  intro index
  rw [regs.injective.eq_iff]
  exact hslot index

private theorem physical_not_mem_phaseWrite
    (regs : NeighborhoodTrial.Registers controller)
    (slot : Fin 34)
    (hscratch : ∀ index, ControlDecode.scratchMap index ≠ slot)
    (hphase : slot ≠ 27)
    (hquotient : slot ≠ 4)
    (hcodec : slot ≠ 30) :
    regs.index slot ∉ phaseWriteFootprint regs := by
  simp only [phaseWriteFootprint, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  refine
    ⟨physical_not_mem_decodeScratch regs slot hscratch,
      regs.injective.ne hphase, ?_, regs.injective.ne hcodec⟩
  simpa [Layout.frameCodecRegisters, Layout.frameCodecMap] using
    regs.injective.ne hquotient

private theorem decodePhase_queryState_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store) :
    ∃ final,
      Runs (ControlDecode.decodePhase regs) store final ∧
      ControlDecode.EncodedPhasePost regs frame.phase final ∧
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        final := by
  have hframeBound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame :=
    hquery.bounds frame (by simp)
  obtain ⟨final, hrun, hdecoded, hactive, hparameters⟩ :=
    Representation.ActiveFrame.decodePhase_runs
      regs frame store hquery.stack.1 hquery.parameters hframeBound
  have hstackWord :
      final (regs.index 32) = store (regs.index 32) :=
    Footprint.runs_eq_outside
      (ControlDecode.decodePhase_writesWithin regs)
      hrun
      (physical_not_mem_decodeScratch regs 32 (by
        intro index
        fin_cases index <;> decide))
  have hbankWord :
      final regs.layout.bank = store regs.layout.bank := by
    change final (regs.index 33) = store (regs.index 33)
    exact
      Footprint.runs_eq_outside
        (ControlDecode.decodePhase_writesWithin regs)
        hrun
        (physical_not_mem_decodeScratch regs 33 (by
          intro index
          fin_cases index <;> decide))
  refine ⟨final, hrun, hdecoded, ?_⟩
  refine
    { parameters := hparameters
      stack := ?_
      bank := ?_
      bank_lt := ?_
      bounds := hquery.bounds }
  · refine ⟨hactive, ?_⟩
    unfold FrameTransfer.RepresentsStack
    change final (regs.index 32) = _
    exact hstackWord.trans hquery.stack.2
  · rw [hbankWord]
    exact hquery.bank
  · rw [hbankWord]
    exact hquery.bank_lt

private theorem phasePost_retained
    (regs : NeighborhoodTrial.Registers controller)
    {phase : NeighborhoodScheduler.Phase workTapeCount}
    {initial final : Store}
    (hpost : PhaseUpdatePost regs phase initial final) :
    ∀ slot : Fin 16,
      final
          (regs.index
            (![2, 3, 8, 14, 13, 7, 15, 24,
                16, 22, 23, 25, 26, 28, 32, 33] slot)) =
        initial
          (regs.index
            (![2, 3, 8, 14, 13, 7, 15, 24,
                16, 22, 23, 25, 26, 28, 32, 33] slot)) := by
  intro slot
  apply hpost.eq_outside
  apply physical_not_mem_phaseWrite
  · intro index
    fin_cases slot <;> fin_cases index <;> decide
  · fin_cases slot <;> decide
  · fin_cases slot <;> decide
  · fin_cases slot <;> decide

theorem phaseUpdatePost_queryState_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame updated : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (initial final : Store)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        initial)
    (hfields :
      updated.fuel = frame.fuel ∧
      updated.node = frame.node ∧
      updated.scalar = frame.scalar ∧
      updated.out = frame.out)
    (hpost : PhaseUpdatePost regs updated.phase initial final)
    (hbounds :
      NeighborhoodScheduler.FrameBounds.StateBound
        { stack := updated :: rest
          registers := logicalBank }) :
    Representation.QueryState regs instanceData
      { stack := updated :: rest
        registers := logicalBank }
      final := by
  have hretained := phasePost_retained regs hpost
  refine
    { parameters :=
        { blockLength_eq :=
            (hretained (0 : Fin 16)).trans
              hquery.parameters.blockLength_eq
          horizon_eq :=
            (hretained (1 : Fin 16)).trans
              hquery.parameters.horizon_eq
          digitBase_eq :=
            (hretained (2 : Fin 16)).trans
              hquery.parameters.digitBase_eq
          bankBase_eq :=
            (hretained (3 : Fin 16)).trans
              hquery.parameters.bankBase_eq
          frameBase_eq :=
            (hretained (4 : Fin 16)).trans
              hquery.parameters.frameBase_eq
          chunkCount_eq :=
            (hretained (5 : Fin 16)).trans
              hquery.parameters.chunkCount_eq
          bankDigitCount_eq :=
            (hretained (6 : Fin 16)).trans
              hquery.parameters.bankDigitCount_eq
          modulus_eq :=
            (hretained (7 : Fin 16)).trans
              hquery.parameters.modulus_eq
          modulusPred_eq :=
            (hretained (8 : Fin 16)).trans
              hquery.parameters.modulusPred_eq }
      stack := ?_
      bank := ?_
      bank_lt := ?_
      bounds := hbounds }
  · refine ⟨?_, ?_⟩
    · exact
        { fuel_eq :=
            ((hretained (9 : Fin 16)).trans
              hquery.stack.1.fuel_eq).trans hfields.1.symm
          node_eq := by
            calc
              final (Layout.nodeCode regs) =
                  initial (Layout.nodeCode regs) :=
                hretained (10 : Fin 16)
              _ = FrameCodec.encodeNode
                  (Representation.digitBase instanceData) frame.node :=
                hquery.stack.1.node_eq
              _ = FrameCodec.encodeNode
                  (Representation.digitBase instanceData) updated.node := by
                rw [hfields.2.1]
          scalar_eq :=
            ((hretained (11 : Fin 16)).trans
              hquery.stack.1.scalar_eq).trans
                hfields.2.2.1.symm
          out_eq :=
            ((hretained (12 : Fin 16)).trans
              hquery.stack.1.out_eq).trans
                (congrArg Fin.val hfields.2.2.2).symm
          phase_eq := by
            calc
              final (Layout.phaseCode regs) =
                  FrameCodec.encodePhase
                    (initial (Layout.chunkRadix regs))
                    updated.phase :=
                hpost.phaseCode_eq
              _ = FrameCodec.encodePhase
                  (Representation.digitBase instanceData)
                  updated.phase := by
                rw [hquery.parameters.digitBase_eq]
          active_eq :=
            (hretained (13 : Fin 16)).trans
              hquery.stack.1.active_eq }
    · unfold FrameTransfer.RepresentsStack
      change final (regs.index 32) = _
      exact (hretained (14 : Fin 16)).trans hquery.stack.2
  · change
      NeighborhoodProgram.RepresentsResidueBank
        tm instanceData.blockLength
        (Representation.fieldBase instanceData)
        (final (regs.index 33)) logicalBank
    have hbankEq :
        final (regs.index 33) = initial (regs.index 33) := by
      simpa using hretained (15 : Fin 16)
    rw [hbankEq]
    exact hquery.bank
  · change
      final (regs.index 33) <
        Representation.fieldBase instanceData ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm instanceData.blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount))
    have hbankEq :
        final (regs.index 33) = initial (regs.index 33) := by
      simpa using hretained (15 : Fin 16)
    rw [hbankEq]
    exact hquery.bank_lt

private theorem combineAfterDecode_runs
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (base residue residuesLeft : ℕ)
    (hbase : 0 < base)
    (hresidue :
      residue < base ^ FrameCodec.scalarDigitCount)
    (hleft :
      residuesLeft < base ^ FrameCodec.scalarDigitCount)
    (hbaseValue : store (Layout.chunkRadix regs) = base)
    (hbankValue :
      store (Layout.bankRadix regs) =
        base ^ FrameCodec.scalarDigitCount)
    (hdecodedResidue :
      store (Dispatcher.decodedResidue regs) = residue)
    (hdecodedLeft :
      store (Dispatcher.decodedResiduesLeft regs) =
        residuesLeft) :
    ∃ final,
      Runs (combineAfterDecode regs) store final ∧
      PhaseUpdatePost regs
        (.combine residue residuesLeft :
          NeighborhoodScheduler.Phase workTapeCount)
        store final := by
  let childZero :=
    (Basic.imm (Dispatcher.decodedChild regs) 0).exec store
  let nextZero :=
    (Basic.imm (Dispatcher.decodedNextChild regs) 0).exec childZero
  have hchildRun :
      Runs
        (.basic (.imm (Dispatcher.decodedChild regs) 0))
        store childZero :=
    Runs.basic _ _
  have hnextRun :
      Runs
        (.basic (.imm (Dispatcher.decodedNextChild regs) 0))
        childZero nextZero :=
    Runs.basic _ _
  have hnextBase : nextZero (Layout.chunkRadix regs) = base := by
    simp [nextZero, childZero, Basic.exec, regs.injective.eq_iff,
      hbaseValue]
  have hnextBank :
      nextZero (Layout.bankRadix regs) =
        base ^ FrameCodec.scalarDigitCount := by
    simp [nextZero, childZero, Basic.exec, regs.injective.eq_iff,
      hbankValue]
  have hnextResidue :
      nextZero (Dispatcher.decodedResidue regs) = residue := by
    simp [nextZero, childZero, Basic.exec, regs.injective.eq_iff,
      hdecodedResidue]
  have hnextLeft :
      nextZero (Dispatcher.decodedResiduesLeft regs) =
        residuesLeft := by
    simp [nextZero, childZero, Basic.exec, regs.injective.eq_iff,
      hdecodedLeft]
  have hnextChild :
      nextZero (Dispatcher.decodedChild regs) = 0 := by
    simp [nextZero, childZero, Basic.exec, regs.injective.eq_iff]
  have hnextNext :
      nextZero (Dispatcher.decodedNextChild regs) = 0 := by
    simp [nextZero, Basic.exec]
  obtain ⟨final, hencode, hencodePost⟩ :=
    Dispatcher.encodeDecodedPhase_runs regs 2 nextZero
  have hphaseCode :
      final (Layout.phaseCode regs) =
        FrameCodec.encodePhase base
          (.combine residue residuesLeft :
            NeighborhoodScheduler.Phase workTapeCount) := by
    calc
      final (Layout.phaseCode regs) =
          Dispatcher.phaseValue
            (nextZero (Layout.chunkRadix regs))
            (nextZero (Layout.bankRadix regs)) 2
            (nextZero (Dispatcher.decodedResidue regs))
            (nextZero (Dispatcher.decodedResiduesLeft regs))
            (nextZero (Dispatcher.decodedChild regs))
            (nextZero (Dispatcher.decodedNextChild regs)) :=
        hencodePost.phaseCode_eq
      _ = Dispatcher.phaseValue
          base (base ^ FrameCodec.scalarDigitCount)
          2 residue residuesLeft 0 0 := by
        rw [hnextBase, hnextBank, hnextResidue, hnextLeft,
          hnextChild, hnextNext]
      _ = FrameCodec.encodePhase base
          (.combine residue residuesLeft :
            NeighborhoodScheduler.Phase workTapeCount) :=
        Dispatcher.phaseValue_combine hbase hresidue hleft
  have hrun :
      Runs (combineAfterDecode regs) store final := by
    simpa [combineAfterDecode, Cmd.seqList] using
      Runs.seq hchildRun (Runs.seq hnextRun hencode)
  refine ⟨final, hrun, ?_⟩
  exact
    { phaseCode_eq := by
        rw [hbaseValue]
        exact hphaseCode
      eq_outside := fun address haddress =>
        Footprint.runs_eq_outside
          (combineAfterDecode_writesWithin regs)
          hrun haddress }

theorem nextResidueAfterDecode_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (base residue residuesLeft : ℕ)
    (hbase : 0 < base)
    (hresidue :
      residue + 1 < base ^ FrameCodec.scalarDigitCount)
    (hleft :
      residuesLeft < base ^ FrameCodec.scalarDigitCount)
    (hbaseValue : store (Layout.chunkRadix regs) = base)
    (hbankValue :
      store (Layout.bankRadix regs) =
        base ^ FrameCodec.scalarDigitCount)
    (hdecodedResidue :
      store (Dispatcher.decodedResidue regs) = residue)
    (hdecodedLeft :
      store (Dispatcher.decodedResiduesLeft regs) =
        residuesLeft + 1) :
    ∃ final,
      Runs (nextResidueAfterDecode regs) store final ∧
      PhaseUpdatePost regs
        (.prepare (residue + 1) residuesLeft 0 :
          NeighborhoodScheduler.Phase workTapeCount)
        store final := by
  let oneStore :=
    (Basic.imm (Layout.codecDigit regs) 1).exec store
  let residueStore :=
    (Basic.add (Dispatcher.decodedResidue regs)
      (Dispatcher.decodedResidue regs)
      (Layout.codecDigit regs)).exec oneStore
  let leftStore :=
    (Basic.sub (Dispatcher.decodedResiduesLeft regs)
      (Dispatcher.decodedResiduesLeft regs)
      (Layout.codecDigit regs)).exec residueStore
  let childZero :=
    (Basic.imm (Dispatcher.decodedChild regs) 0).exec leftStore
  let nextZero :=
    (Basic.imm (Dispatcher.decodedNextChild regs) 0).exec childZero
  have honeRun :
      Runs (.basic (.imm (Layout.codecDigit regs) 1))
        store oneStore :=
    Runs.basic _ _
  have hresidueRun :
      Runs
        (.basic
          (.add (Dispatcher.decodedResidue regs)
            (Dispatcher.decodedResidue regs)
            (Layout.codecDigit regs)))
        oneStore residueStore :=
    Runs.basic _ _
  have hleftRun :
      Runs
        (.basic
          (.sub (Dispatcher.decodedResiduesLeft regs)
            (Dispatcher.decodedResiduesLeft regs)
            (Layout.codecDigit regs)))
        residueStore leftStore :=
    Runs.basic _ _
  have hchildRun :
      Runs
        (.basic (.imm (Dispatcher.decodedChild regs) 0))
        leftStore childZero :=
    Runs.basic _ _
  have hnextRun :
      Runs
        (.basic (.imm (Dispatcher.decodedNextChild regs) 0))
        childZero nextZero :=
    Runs.basic _ _
  have hnextBase : nextZero (Layout.chunkRadix regs) = base := by
    simp [nextZero, childZero, leftStore, residueStore, oneStore,
      Basic.exec, regs.injective.eq_iff, hbaseValue]
  have hnextBank :
      nextZero (Layout.bankRadix regs) =
        base ^ FrameCodec.scalarDigitCount := by
    simp [nextZero, childZero, leftStore, residueStore, oneStore,
      Basic.exec, regs.injective.eq_iff, hbankValue]
  have hnextResidue :
      nextZero (Dispatcher.decodedResidue regs) = residue + 1 := by
    simp [nextZero, childZero, leftStore, residueStore, oneStore,
      Basic.exec, regs.injective.eq_iff, hdecodedResidue]
  have hnextLeft :
      nextZero (Dispatcher.decodedResiduesLeft regs) =
        residuesLeft := by
    simp [nextZero, childZero, leftStore, residueStore, oneStore,
      Basic.exec, regs.injective.eq_iff, hdecodedLeft]
  have hnextChild :
      nextZero (Dispatcher.decodedChild regs) = 0 := by
    simp [nextZero, childZero, Basic.exec, regs.injective.eq_iff]
  have hnextNext :
      nextZero (Dispatcher.decodedNextChild regs) = 0 := by
    simp [nextZero, Basic.exec]
  obtain ⟨final, hencode, hencodePost⟩ :=
    Dispatcher.encodeDecodedPhase_runs regs 1 nextZero
  have hphaseCode :
      final (Layout.phaseCode regs) =
        FrameCodec.encodePhase base
          (.prepare (residue + 1) residuesLeft 0 :
            NeighborhoodScheduler.Phase workTapeCount) := by
    calc
      final (Layout.phaseCode regs) =
          Dispatcher.phaseValue
            (nextZero (Layout.chunkRadix regs))
            (nextZero (Layout.bankRadix regs)) 1
            (nextZero (Dispatcher.decodedResidue regs))
            (nextZero (Dispatcher.decodedResiduesLeft regs))
            (nextZero (Dispatcher.decodedChild regs))
            (nextZero (Dispatcher.decodedNextChild regs)) :=
        hencodePost.phaseCode_eq
      _ = Dispatcher.phaseValue
          base (base ^ FrameCodec.scalarDigitCount)
          1 (residue + 1) residuesLeft 0 0 := by
        rw [hnextBase, hnextBank, hnextResidue, hnextLeft,
          hnextChild, hnextNext]
      _ = FrameCodec.encodePhase base
          (.prepare (residue + 1) residuesLeft 0 :
            NeighborhoodScheduler.Phase workTapeCount) :=
        Dispatcher.phaseValue_prepare hbase hresidue hleft
  have hrun :
      Runs (nextResidueAfterDecode regs) store final := by
    simpa [nextResidueAfterDecode, Cmd.seqList] using
      Runs.seq honeRun
        (Runs.seq hresidueRun
          (Runs.seq hleftRun
            (Runs.seq hchildRun (Runs.seq hnextRun hencode))))
  refine ⟨final, hrun, ?_⟩
  exact
    { phaseCode_eq := by
        rw [hbaseValue]
        exact hphaseCode
      eq_outside := fun address haddress =>
        Footprint.runs_eq_outside
          (nextResidueAfterDecode_writesWithin_internal regs)
          hrun haddress }

theorem finishPrepare_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (residue residuesLeft childIndex : ℕ)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hphase :
      frame.phase =
        .prepare residue residuesLeft childIndex)
    (hexhausted :
      childIndex =
        NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) :
    ∃ final,
      Runs (finishPrepare regs) store final ∧
      Representation.QueryState regs instanceData
        { stack := combineFrame frame residue residuesLeft :: rest
          registers := logicalBank }
        final := by
  have hframeBound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame :=
    hquery.bounds frame (by simp)
  have hbase :
      0 < Representation.digitBase instanceData := by
    unfold Representation.digitBase CandidateParameters.domainSize
    exact
      TreeEval.CookMertz.PrimeGrouped.Logarithmic.domainSize_pos _ _
  have hresidue :
      residue <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      FrameBounds.frameBound_phaseResidue_lt frame hframeBound
  have hleft :
      residuesLeft <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      FrameBounds.frameBound_phaseResiduesLeft_lt frame hframeBound
  obtain ⟨decoded, hdecode, hdecoded, hqueryDecoded⟩ :=
    decodePhase_queryState_runs
      regs frame rest logicalBank store hquery
  have hdecodedResidue :
      decoded (Dispatcher.decodedResidue regs) = residue := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      hdecoded.residue_eq
  have hdecodedLeft :
      decoded (Dispatcher.decodedResiduesLeft regs) =
        residuesLeft := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      hdecoded.residuesLeft_eq
  obtain ⟨final, hupdate, hpost⟩ :=
    combineAfterDecode_runs
      (workTapeCount := workTapeCount)
      regs decoded (Representation.digitBase instanceData)
      residue residuesLeft hbase hresidue hleft
      hqueryDecoded.parameters.digitBase_eq
      (by
        simpa [Representation.fieldBase] using
          hqueryDecoded.parameters.bankBase_eq)
      hdecodedResidue hdecodedLeft
  have hbounds :
      NeighborhoodScheduler.FrameBounds.StateBound
        { stack := combineFrame frame residue residuesLeft :: rest
          registers := logicalBank } := by
    have hnext :=
      NeighborhoodScheduler.FrameBounds.StateBound.next
        { stack := frame :: rest
          registers := logicalBank }
        hquery.bounds
    simpa [NeighborhoodScheduler.State.next, hphase, hexhausted,
      combineFrame] using hnext
  have hqueryFinal :=
    phaseUpdatePost_queryState_internal
      regs frame (combineFrame frame residue residuesLeft)
      rest logicalBank decoded final hqueryDecoded
      (by simp [combineFrame]) hpost hbounds
  refine ⟨final, ?_, hqueryFinal⟩
  simpa [finishPrepare] using Runs.seq hdecode hupdate

theorem finishCleanup_zero_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (residue childIndex : ℕ)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hphase :
      frame.phase = .cleanupCall residue 0 childIndex)
    (hexhausted :
      childIndex =
        NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) :
    ∃ final,
      Runs (finishCleanup regs) store final ∧
      Representation.QueryState regs instanceData
        { stack := rest
          registers := logicalBank }
        final := by
  obtain ⟨decoded, hdecode, hdecoded, hqueryDecoded⟩ :=
    decodePhase_queryState_runs
      regs frame rest logicalBank store hquery
  have hzero :
      decoded (Dispatcher.decodedResiduesLeft regs) = 0 := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      hdecoded.residuesLeft_eq
  obtain ⟨final, hpop, hqueryFinal⟩ :=
    Representation.QueryState.popParent_runs
      regs frame rest logicalBank decoded hqueryDecoded
  have hbounds :
      NeighborhoodScheduler.FrameBounds.StateBound
        { stack := rest
          registers := logicalBank } := by
    have hnext :=
      NeighborhoodScheduler.FrameBounds.StateBound.next
        { stack := frame :: rest
          registers := logicalBank }
        hquery.bounds
    simpa [NeighborhoodScheduler.State.next, hphase, hexhausted,
      NeighborhoodScheduler.State.finishResidue] using hnext
  refine ⟨final, ?_, { hqueryFinal with bounds := hbounds }⟩
  simpa [finishCleanup] using
    Runs.seq hdecode (Runs.ifZero hzero hpop)

theorem finishCleanup_succ_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (residue residuesLeft childIndex : ℕ)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hphase :
      frame.phase =
        .cleanupCall residue (residuesLeft + 1) childIndex)
    (hexhausted :
      childIndex =
        NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) :
    ∃ final,
      Runs (finishCleanup regs) store final ∧
      Representation.QueryState regs instanceData
        { stack :=
            nextResidueFrame frame residue residuesLeft :: rest
          registers := logicalBank }
        final := by
  have hbase :
      0 < Representation.digitBase instanceData := by
    unfold Representation.digitBase CandidateParameters.domainSize
    exact
      TreeEval.CookMertz.PrimeGrouped.Logarithmic.domainSize_pos _ _
  have hbounds :
      NeighborhoodScheduler.FrameBounds.StateBound
        { stack :=
            nextResidueFrame frame residue residuesLeft :: rest
          registers := logicalBank } := by
    have hnext :=
      NeighborhoodScheduler.FrameBounds.StateBound.next
        { stack := frame :: rest
          registers := logicalBank }
        hquery.bounds
    simpa [NeighborhoodScheduler.State.next, hphase, hexhausted,
      NeighborhoodScheduler.State.finishResidue,
      nextResidueFrame] using hnext
  have hnextFrameBound :
      NeighborhoodScheduler.FrameBounds.FrameBound
        (nextResidueFrame frame residue residuesLeft) :=
    hbounds _ (by simp)
  have hresidue :
      residue + 1 <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount := by
    simpa [nextResidueFrame,
      ControlDecode.expectedPhaseValues] using
      FrameBounds.frameBound_phaseResidue_lt
        (nextResidueFrame frame residue residuesLeft)
        hnextFrameBound
  have hleft :
      residuesLeft <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount := by
    simpa [nextResidueFrame,
      ControlDecode.expectedPhaseValues] using
      FrameBounds.frameBound_phaseResiduesLeft_lt
        (nextResidueFrame frame residue residuesLeft)
        hnextFrameBound
  obtain ⟨decoded, hdecode, hdecoded, hqueryDecoded⟩ :=
    decodePhase_queryState_runs
      regs frame rest logicalBank store hquery
  have hdecodedResidue :
      decoded (Dispatcher.decodedResidue regs) = residue := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      hdecoded.residue_eq
  have hdecodedLeft :
      decoded (Dispatcher.decodedResiduesLeft regs) =
        residuesLeft + 1 := by
    simpa [hphase, ControlDecode.expectedPhaseValues] using
      hdecoded.residuesLeft_eq
  have hnonzero :
      decoded (Dispatcher.decodedResiduesLeft regs) ≠ 0 := by
    rw [hdecodedLeft]
    omega
  obtain ⟨final, hupdate, hpost⟩ :=
    nextResidueAfterDecode_runs_internal
      (workTapeCount := workTapeCount)
      regs decoded (Representation.digitBase instanceData)
      residue residuesLeft hbase hresidue hleft
      hqueryDecoded.parameters.digitBase_eq
      (by
        simpa [Representation.fieldBase] using
          hqueryDecoded.parameters.bankBase_eq)
      hdecodedResidue hdecodedLeft
  have hqueryFinal :=
    phaseUpdatePost_queryState_internal
      regs frame (nextResidueFrame frame residue residuesLeft)
      rest logicalBank decoded final hqueryDecoded
      (by simp [nextResidueFrame]) hpost hbounds
  refine ⟨final, ?_, hqueryFinal⟩
  simpa [finishCleanup] using
    Runs.seq hdecode (Runs.ifNonzero hnonzero hupdate)

end Internal
end CursorFinish
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
