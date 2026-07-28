/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Dispatcher
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ParentPhase.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation

/-!
# Parent-phase advancement before recursive descent -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ParentPhase
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

theorem advancePrepare_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (writeFootprint regs) (advancePrepare regs) := by
  simp [advancePrepare, writeFootprint, ControlDecode.copy,
    Dispatcher.encodePhase, Dispatcher.encodePhaseOps,
    Cmd.basics, Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]

theorem advanceCleanup_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (writeFootprint regs) (advanceCleanup regs) := by
  simp [advanceCleanup, writeFootprint, ControlDecode.copy,
    Dispatcher.encodePhase, Dispatcher.encodePhaseOps,
    Cmd.basics, Cmd.seqList, Footprint.CmdWritesWithin,
    Footprint.BasicWritesWithin]

theorem writeFootprint_subset_layout_internal
    (regs : NeighborhoodTrial.Registers controller) :
    writeFootprint regs ⊆ regs.layout.footprint := by
  intro address haddress
  simp only [writeFootprint, Finset.mem_insert,
    Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl | rfl
  all_goals exact Layout.index_mem_layout_footprint regs _

theorem advancePrepare_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (base residue residuesLeft : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
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
      store (Dispatcher.decodedResiduesLeft regs) = residuesLeft)
    (hdecodedChild :
      store (Dispatcher.decodedChild regs) = child.val)
    (hdecodedNext :
      store (Dispatcher.decodedNextChild regs) = 0) :
    ∃ final,
      Runs (advancePrepare regs) store final ∧
      AdvancePost regs child.val
        (FrameCodec.encodePhase base
          (.prepare residue residuesLeft (child.val + 1) :
            NeighborhoodScheduler.Phase workTapeCount))
        store final := by
  let copied :=
    Function.update store
      (ChildNode.savedChildIndex regs)
      (store (Dispatcher.decodedChild regs))
  let withOne :=
    Basic.exec (.imm (Layout.codecDigit regs) 1) copied
  let advanced :=
    Basic.exec
      (.add (Dispatcher.decodedChild regs)
        (Dispatcher.decodedChild regs) (Layout.codecDigit regs))
      withOne
  have hcopy :
      Runs
        (ControlDecode.copy
          (ChildNode.savedChildIndex regs)
          (Dispatcher.decodedChild regs))
        store copied := by
    apply copy_runs
    simp [ChildNode.savedChildIndex, Layout.codecScratch,
      Dispatcher.decodedChild, regs.injective.eq_iff]
  have hone :
      Runs (.basic (.imm (Layout.codecDigit regs) 1))
        copied withOne :=
    Runs.basic _ _
  have hadvance :
      Runs
        (.basic
          (.add (Dispatcher.decodedChild regs)
            (Dispatcher.decodedChild regs) (Layout.codecDigit regs)))
        withOne advanced :=
    Runs.basic _ _
  obtain ⟨final, hencode, hencodePost⟩ :=
    Dispatcher.encodeDecodedPhase_runs regs 1 advanced
  have hrun : Runs (advancePrepare regs) store final := by
    simpa [advancePrepare, Cmd.seqList] using
      Runs.seq hcopy (Runs.seq hone (Runs.seq hadvance hencode))
  have hsaved :
      final (ChildNode.savedChildIndex regs) = child.val := by
    rw [hencodePost.eq_of_ne
      (ChildNode.savedChildIndex regs) (by
        simp [ChildNode.savedChildIndex, Layout.codecScratch,
          regs.injective.eq_iff]) (by
        simp [ChildNode.savedChildIndex, Layout.codecScratch,
          Layout.frameCodecRegisters, Layout.frameCodecMap,
          regs.injective.eq_iff]) (by
        simp [ChildNode.savedChildIndex, Layout.codecScratch,
          regs.injective.eq_iff])]
    simp [advanced, withOne, copied, Basic.exec,
      hdecodedChild, regs.injective.eq_iff]
  have hphase :
      final (Layout.phaseCode regs) =
        FrameCodec.encodePhase base
          (.prepare residue residuesLeft (child.val + 1) :
            NeighborhoodScheduler.Phase workTapeCount) := by
    rw [hencodePost.phaseCode_eq]
    have hvalue :=
      Dispatcher.phaseValue_prepare
        (workTapeCount := workTapeCount)
        (base := base) (residue := residue)
        (residuesLeft := residuesLeft) (child := child.val + 1)
        hbase hresidue hleft
    simpa [advanced, withOne, copied, Basic.exec,
      hbaseValue, hbankValue, hdecodedResidue, hdecodedLeft,
      hdecodedChild, hdecodedNext, regs.injective.eq_iff] using hvalue
  exact
    ⟨final, hrun,
      ⟨hsaved, hphase, fun address haddress =>
        Footprint.runs_eq_outside
          (advancePrepare_writesWithin_internal regs)
          hrun haddress⟩⟩

theorem advanceCleanup_runs_internal
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (base residue residuesLeft : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
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
      store (Dispatcher.decodedResiduesLeft regs) = residuesLeft)
    (hdecodedChild :
      store (Dispatcher.decodedChild regs) = child.val) :
    ∃ final,
      Runs (advanceCleanup regs) store final ∧
      AdvancePost regs child.val
        (FrameCodec.encodePhase base
          (.cleanupScale residue residuesLeft child (child.val + 1) :
            NeighborhoodScheduler.Phase workTapeCount))
        store final := by
  let saved :=
    Function.update store
      (ChildNode.savedChildIndex regs)
      (store (Dispatcher.decodedChild regs))
  let copied :=
    Function.update saved
      (Dispatcher.decodedNextChild regs)
      (saved (Dispatcher.decodedChild regs))
  let withOne :=
    Basic.exec (.imm (Layout.codecDigit regs) 1) copied
  let advanced :=
    Basic.exec
      (.add (Dispatcher.decodedNextChild regs)
        (Dispatcher.decodedNextChild regs) (Layout.codecDigit regs))
      withOne
  have hsave :
      Runs
        (ControlDecode.copy
          (ChildNode.savedChildIndex regs)
          (Dispatcher.decodedChild regs))
        store saved := by
    apply copy_runs
    simp [ChildNode.savedChildIndex, Layout.codecScratch,
      Dispatcher.decodedChild, regs.injective.eq_iff]
  have hcopy :
      Runs
        (ControlDecode.copy
          (Dispatcher.decodedNextChild regs)
          (Dispatcher.decodedChild regs))
        saved copied := by
    apply copy_runs
    simp [Dispatcher.decodedNextChild, Dispatcher.decodedChild,
      regs.injective.eq_iff]
  have hone :
      Runs (.basic (.imm (Layout.codecDigit regs) 1))
        copied withOne :=
    Runs.basic _ _
  have hadvance :
      Runs
        (.basic
          (.add (Dispatcher.decodedNextChild regs)
            (Dispatcher.decodedNextChild regs) (Layout.codecDigit regs)))
        withOne advanced :=
    Runs.basic _ _
  obtain ⟨final, hencode, hencodePost⟩ :=
    Dispatcher.encodeDecodedPhase_runs regs 4 advanced
  have hrun : Runs (advanceCleanup regs) store final := by
    simpa [advanceCleanup, Cmd.seqList] using
      Runs.seq hsave
        (Runs.seq hcopy (Runs.seq hone (Runs.seq hadvance hencode)))
  have hsaved :
      final (ChildNode.savedChildIndex regs) = child.val := by
    rw [hencodePost.eq_of_ne
      (ChildNode.savedChildIndex regs) (by
        simp [ChildNode.savedChildIndex, Layout.codecScratch,
          regs.injective.eq_iff]) (by
        simp [ChildNode.savedChildIndex, Layout.codecScratch,
          Layout.frameCodecRegisters, Layout.frameCodecMap,
          regs.injective.eq_iff]) (by
        simp [ChildNode.savedChildIndex, Layout.codecScratch,
          regs.injective.eq_iff])]
    simp [advanced, withOne, copied, saved, Basic.exec,
      hdecodedChild, regs.injective.eq_iff]
  have hphase :
      final (Layout.phaseCode regs) =
        FrameCodec.encodePhase base
          (.cleanupScale residue residuesLeft child (child.val + 1) :
            NeighborhoodScheduler.Phase workTapeCount) := by
    rw [hencodePost.phaseCode_eq]
    have hvalue :=
      Dispatcher.phaseValue_cleanupScale
        (base := base) (residue := residue)
        (residuesLeft := residuesLeft)
        (nextChild := child.val + 1) child
        hbase hresidue hleft
    simpa [advanced, withOne, copied, saved, Basic.exec,
      hbaseValue, hbankValue, hdecodedResidue, hdecodedLeft,
      hdecodedChild, regs.injective.eq_iff] using hvalue
  exact
    ⟨final, hrun,
      ⟨hsaved, hphase, fun address haddress =>
        Footprint.runs_eq_outside
          (advanceCleanup_writesWithin_internal regs)
          hrun haddress⟩⟩

private theorem activeFrame_of_advancePost_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame updated : NeighborhoodScheduler.Frame tm instanceData)
    (initial final : Store)
    (hactive : Representation.ActiveFrame regs frame initial)
    (hfields :
      updated.fuel = frame.fuel ∧
      updated.node = frame.node ∧
      updated.scalar = frame.scalar ∧
      updated.out = frame.out)
    (hpost :
      AdvancePost regs child
        (FrameCodec.encodePhase
          (Representation.digitBase instanceData) updated.phase)
        initial final) :
    Representation.ActiveFrame regs updated final := by
  rcases hfields with ⟨hfuel, hnode, hscalar, hout⟩
  constructor
  · rw [hpost.eq_outside (Layout.fuel regs) (by
      simp [writeFootprint, Layout.fuel, regs.injective.eq_iff])]
    simpa [hfuel] using hactive.fuel_eq
  · rw [hpost.eq_outside (Layout.nodeCode regs) (by
      simp [writeFootprint, Layout.nodeCode, regs.injective.eq_iff])]
    simpa [hnode] using hactive.node_eq
  · rw [hpost.eq_outside (Layout.scalar regs) (by
      simp [writeFootprint, Layout.scalar, regs.injective.eq_iff])]
    simpa [hscalar] using hactive.scalar_eq
  · rw [hpost.eq_outside (Layout.out regs) (by
      simp [writeFootprint, Layout.out, regs.injective.eq_iff])]
    simpa [hout] using hactive.out_eq
  · exact hpost.phaseCode_eq
  · rw [hpost.eq_outside (Layout.active regs) (by
      simp [writeFootprint, Layout.active, regs.injective.eq_iff])]
    exact hactive.active_eq

theorem activeFrame_advancePrepare_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (residue residuesLeft : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (initial final : Store)
    (hactive : Representation.ActiveFrame regs frame initial)
    (hpost :
      AdvancePost regs child.val
        (FrameCodec.encodePhase
          (Representation.digitBase instanceData)
          (.prepare residue residuesLeft (child.val + 1) :
            NeighborhoodScheduler.Phase workTapeCount))
        initial final) :
    Representation.ActiveFrame regs
      { frame with
        phase := .prepare residue residuesLeft (child.val + 1) }
      final :=
  activeFrame_of_advancePost_internal regs frame
    { frame with
      phase := .prepare residue residuesLeft (child.val + 1) }
    initial final hactive ⟨rfl, rfl, rfl, rfl⟩ hpost

theorem activeFrame_advanceCleanup_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (residue residuesLeft : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (initial final : Store)
    (hactive : Representation.ActiveFrame regs frame initial)
    (hpost :
      AdvancePost regs child.val
        (FrameCodec.encodePhase
          (Representation.digitBase instanceData)
          (.cleanupScale residue residuesLeft child (child.val + 1) :
            NeighborhoodScheduler.Phase workTapeCount))
        initial final) :
    Representation.ActiveFrame regs
      { frame with
        phase :=
          .cleanupScale residue residuesLeft child (child.val + 1) }
      final :=
  activeFrame_of_advancePost_internal regs frame
    { frame with
      phase :=
        .cleanupScale residue residuesLeft child (child.val + 1) }
    initial final hactive ⟨rfl, rfl, rfl, rfl⟩ hpost

theorem frameBound_advancePrepare_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (residue residuesLeft : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (hphase :
      frame.phase =
        .prepare residue residuesLeft child.val)
    (hbound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    NeighborhoodScheduler.FrameBounds.FrameBound
      { frame with
        phase := .prepare residue residuesLeft (child.val + 1) } := by
  rcases hbound with ⟨hfuel, hnode, hscalar, hphaseBound⟩
  refine ⟨hfuel, hnode, hscalar, ?_⟩
  rw [hphase] at hphaseBound
  have hsum :
      residue + residuesLeft + 1 =
        NeighborhoodScheduler.fieldModulus instanceData := by
    simpa [NeighborhoodScheduler.FrameBounds.PhaseBound] using
      hphaseBound.1
  exact ⟨hsum, child.isLt⟩

theorem frameBound_advanceCleanup_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (residue residuesLeft : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (hphase :
      frame.phase =
        .cleanupCall residue residuesLeft child.val)
    (hbound :
      NeighborhoodScheduler.FrameBounds.FrameBound frame) :
    NeighborhoodScheduler.FrameBounds.FrameBound
      { frame with
        phase :=
          .cleanupScale residue residuesLeft child (child.val + 1) } := by
  rcases hbound with ⟨hfuel, hnode, hscalar, hphaseBound⟩
  refine ⟨hfuel, hnode, hscalar, ?_⟩
  rw [hphase] at hphaseBound
  have hsum :
      residue + residuesLeft + 1 =
        NeighborhoodScheduler.fieldModulus instanceData := by
    simpa [NeighborhoodScheduler.FrameBounds.PhaseBound] using
      hphaseBound.1
  exact ⟨hsum, child.isLt⟩

theorem parameters_of_advancePost_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store)
    (hparameters : Representation.Parameters regs instanceData initial)
    (hpost : AdvancePost regs child phaseCode initial final) :
    Representation.Parameters regs instanceData final := by
  constructor
  · rw [hpost.eq_outside (Layout.blockLength regs) (by
      simp [writeFootprint, Layout.blockLength,
        regs.injective.eq_iff])]
    exact hparameters.blockLength_eq
  · rw [hpost.eq_outside (Layout.horizon regs) (by
      simp [writeFootprint, Layout.horizon,
        regs.injective.eq_iff])]
    exact hparameters.horizon_eq
  · rw [hpost.eq_outside (Layout.chunkRadix regs) (by
      simp [writeFootprint, Layout.chunkRadix,
        regs.injective.eq_iff])]
    exact hparameters.digitBase_eq
  · rw [hpost.eq_outside (Layout.bankRadix regs) (by
      simp [writeFootprint, Layout.bankRadix,
        regs.injective.eq_iff])]
    exact hparameters.bankBase_eq
  · rw [hpost.eq_outside (Layout.frameRadix regs) (by
      simp [writeFootprint, Layout.frameRadix,
        regs.injective.eq_iff])]
    exact hparameters.frameBase_eq
  · rw [hpost.eq_outside (Layout.chunkCount regs) (by
      simp [writeFootprint, Layout.chunkCount,
        regs.injective.eq_iff])]
    exact hparameters.chunkCount_eq
  · rw [hpost.eq_outside (Layout.bankDigitCount regs) (by
      simp [writeFootprint, Layout.bankDigitCount,
        regs.injective.eq_iff])]
    exact hparameters.bankDigitCount_eq
  · rw [hpost.eq_outside (Layout.modulus regs) (by
      simp [writeFootprint, Layout.modulus,
        regs.injective.eq_iff])]
    exact hparameters.modulus_eq
  · rw [hpost.eq_outside (Layout.modulusPred regs) (by
      simp [writeFootprint, Layout.modulusPred,
        regs.injective.eq_iff])]
    exact hparameters.modulusPred_eq

theorem advancePost_bank_eq_internal
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hpost : AdvancePost regs child phaseCode initial final) :
    final regs.layout.bank = initial regs.layout.bank :=
  hpost.eq_outside regs.layout.bank (by
    simp [writeFootprint, NeighborhoodTrial.Registers.layout,
      regs.injective.eq_iff])

private theorem representsStack_of_advancePost_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frames : List (NeighborhoodScheduler.Frame tm instanceData))
    (initial final : Store)
    (hpost : AdvancePost regs child phaseCode initial final)
    (hstack :
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData)
        frames initial) :
    FrameTransfer.RepresentsStack regs
      (Representation.digitBase instanceData)
      (Representation.frameBase instanceData)
      frames final := by
  unfold FrameTransfer.RepresentsStack at hstack ⊢
  rw [hpost.eq_outside
    (Layout.frameStackRegisters regs).word (by
      simp [writeFootprint, Layout.frameStackRegisters,
        Layout.frameStackMap, regs.injective.eq_iff])]
  exact hstack

theorem stack_advancePrepare_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (residue residuesLeft : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (initial final : Store)
    (hstack : Representation.Stack regs (frame :: rest) initial)
    (hpost :
      AdvancePost regs child.val
        (FrameCodec.encodePhase
          (Representation.digitBase instanceData)
          (.prepare residue residuesLeft (child.val + 1) :
            NeighborhoodScheduler.Phase workTapeCount))
        initial final) :
    Representation.Stack regs
      ({ frame with
          phase := .prepare residue residuesLeft (child.val + 1) } ::
        rest)
      final :=
  ⟨activeFrame_advancePrepare_internal
      regs frame residue residuesLeft child initial final
      hstack.1 hpost,
    representsStack_of_advancePost_internal
      regs rest initial final hpost hstack.2⟩

theorem stack_advanceCleanup_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (residue residuesLeft : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (initial final : Store)
    (hstack : Representation.Stack regs (frame :: rest) initial)
    (hpost :
      AdvancePost regs child.val
        (FrameCodec.encodePhase
          (Representation.digitBase instanceData)
          (.cleanupScale residue residuesLeft child (child.val + 1) :
            NeighborhoodScheduler.Phase workTapeCount))
        initial final) :
    Representation.Stack regs
      ({ frame with
          phase :=
            .cleanupScale residue residuesLeft child (child.val + 1) } ::
        rest)
      final :=
  ⟨activeFrame_advanceCleanup_internal
      regs frame residue residuesLeft child initial final
      hstack.1 hpost,
    representsStack_of_advancePost_internal
      regs rest initial final hpost hstack.2⟩

theorem suspendPrepare_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      regs.layout.footprint (suspendPrepare regs) := by
  simp only [suspendPrepare, Footprint.CmdWritesWithin]
  exact
    ⟨cmdWritesWithin_mono
        (advancePrepare_writesWithin_internal regs)
        (writeFootprint_subset_layout_internal regs),
      FrameTransfer.pushParent_writesWithin regs⟩

theorem suspendCleanup_writesWithin_internal
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      regs.layout.footprint (suspendCleanup regs) := by
  simp only [suspendCleanup, Footprint.CmdWritesWithin]
  exact
    ⟨cmdWritesWithin_mono
        (advanceCleanup_writesWithin_internal regs)
        (writeFootprint_subset_layout_internal regs),
      FrameTransfer.pushParent_writesWithin regs⟩

private theorem savedChild_eq_of_pushParent_internal
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hrun : Runs (FrameTransfer.pushParent regs) initial final) :
    final (ChildNode.savedChildIndex regs) =
      initial (ChildNode.savedChildIndex regs) := by
  apply Footprint.runs_eq_outside
    (FrameTransfer.pushParent_writesWithin_writeFootprint regs)
    hrun
  simp [FrameTransfer.writeFootprint, ChildNode.savedChildIndex,
    Layout.codecScratch, regs.injective.eq_iff]

theorem suspendPrepare_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (store : Store)
    (residue residuesLeft : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (hstack : Representation.Stack regs (frame :: rest) store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hbase : 0 < Representation.digitBase instanceData)
    (hresidue :
      residue <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount)
    (hleft :
      residuesLeft <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount)
    (hdecodedResidue :
      store (Dispatcher.decodedResidue regs) = residue)
    (hdecodedLeft :
      store (Dispatcher.decodedResiduesLeft regs) = residuesLeft)
    (hdecodedChild :
      store (Dispatcher.decodedChild regs) = child.val)
    (hdecodedNext :
      store (Dispatcher.decodedNextChild regs) = 0)
    (hupdatedBound :
      NeighborhoodScheduler.FrameBounds.FrameBound
        { frame with
          phase := .prepare residue residuesLeft (child.val + 1) }) :
    ∃ final,
      Runs (suspendPrepare regs) store final ∧
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData)
        ({ frame with
            phase := .prepare residue residuesLeft (child.val + 1) } ::
          rest)
        final ∧
      Representation.Parameters regs instanceData final ∧
      final regs.layout.bank = store regs.layout.bank ∧
      final (ChildNode.savedChildIndex regs) = child.val ∧
      Representation.ActiveFrame regs
        { frame with
          phase := .prepare residue residuesLeft (child.val + 1) }
        final := by
  obtain ⟨middle, hadvance, hpost⟩ :=
    advancePrepare_runs_internal
      regs store (Representation.digitBase instanceData)
      residue residuesLeft child hbase hresidue hleft
      hparameters.digitBase_eq
      (by simpa [Representation.fieldBase] using
        hparameters.bankBase_eq)
      hdecodedResidue hdecodedLeft hdecodedChild hdecodedNext
  let updated : NeighborhoodScheduler.Frame tm instanceData :=
    { frame with
      phase := .prepare residue residuesLeft (child.val + 1) }
  have hstackMiddle :
      Representation.Stack regs (updated :: rest) middle := by
    simpa [updated] using
      stack_advancePrepare_internal
        regs frame rest residue residuesLeft child store middle
        hstack hpost
  have hparametersMiddle :
      Representation.Parameters regs instanceData middle :=
    parameters_of_advancePost_internal
      regs store middle hparameters hpost
  obtain ⟨final, hpush, hrepresented, hparametersFinal, hbank⟩ :=
    Representation.Stack.pushParent_runs
      regs updated rest middle hstackMiddle hparametersMiddle
      (by simpa [updated] using hupdatedBound)
  have hactiveFinal :
      Representation.ActiveFrame regs updated final :=
    Representation.ActiveFrame.of_preservesABI
      regs updated middle final hstackMiddle.1
      (Representation.pushParent_preservesABI regs hpush)
  refine ⟨final, ?_, ?_, hparametersFinal, ?_, ?_, ?_⟩
  · simpa [suspendPrepare] using Runs.seq hadvance hpush
  · simpa [updated] using hrepresented
  · exact hbank.trans (advancePost_bank_eq_internal regs hpost)
  · exact (savedChild_eq_of_pushParent_internal regs hpush).trans
      hpost.savedChild_eq
  · simpa [updated] using hactiveFinal

theorem suspendCleanup_runs_internal
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (store : Store)
    (residue residuesLeft : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (hstack : Representation.Stack regs (frame :: rest) store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hbase : 0 < Representation.digitBase instanceData)
    (hresidue :
      residue <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount)
    (hleft :
      residuesLeft <
        Representation.digitBase instanceData ^
          FrameCodec.scalarDigitCount)
    (hdecodedResidue :
      store (Dispatcher.decodedResidue regs) = residue)
    (hdecodedLeft :
      store (Dispatcher.decodedResiduesLeft regs) = residuesLeft)
    (hdecodedChild :
      store (Dispatcher.decodedChild regs) = child.val)
    (hupdatedBound :
      NeighborhoodScheduler.FrameBounds.FrameBound
        { frame with
          phase :=
            .cleanupScale residue residuesLeft child (child.val + 1) }) :
    ∃ final,
      Runs (suspendCleanup regs) store final ∧
      FrameTransfer.RepresentsStack regs
        (Representation.digitBase instanceData)
        (Representation.frameBase instanceData)
        ({ frame with
            phase :=
              .cleanupScale residue residuesLeft child
                (child.val + 1) } ::
          rest)
        final ∧
      Representation.Parameters regs instanceData final ∧
      final regs.layout.bank = store regs.layout.bank ∧
      final (ChildNode.savedChildIndex regs) = child.val ∧
      Representation.ActiveFrame regs
        { frame with
          phase :=
            .cleanupScale residue residuesLeft child (child.val + 1) }
        final := by
  obtain ⟨middle, hadvance, hpost⟩ :=
    advanceCleanup_runs_internal
      regs store (Representation.digitBase instanceData)
      residue residuesLeft child hbase hresidue hleft
      hparameters.digitBase_eq
      (by simpa [Representation.fieldBase] using
        hparameters.bankBase_eq)
      hdecodedResidue hdecodedLeft hdecodedChild
  let updated : NeighborhoodScheduler.Frame tm instanceData :=
    { frame with
      phase :=
        .cleanupScale residue residuesLeft child (child.val + 1) }
  have hstackMiddle :
      Representation.Stack regs (updated :: rest) middle := by
    simpa [updated] using
      stack_advanceCleanup_internal
        regs frame rest residue residuesLeft child store middle
        hstack hpost
  have hparametersMiddle :
      Representation.Parameters regs instanceData middle :=
    parameters_of_advancePost_internal
      regs store middle hparameters hpost
  obtain ⟨final, hpush, hrepresented, hparametersFinal, hbank⟩ :=
    Representation.Stack.pushParent_runs
      regs updated rest middle hstackMiddle hparametersMiddle
      (by simpa [updated] using hupdatedBound)
  have hactiveFinal :
      Representation.ActiveFrame regs updated final :=
    Representation.ActiveFrame.of_preservesABI
      regs updated middle final hstackMiddle.1
      (Representation.pushParent_preservesABI regs hpush)
  refine ⟨final, ?_, ?_, hparametersFinal, ?_, ?_, ?_⟩
  · simpa [suspendCleanup] using Runs.seq hadvance hpush
  · simpa [updated] using hrepresented
  · exact hbank.trans (advancePost_bank_eq_internal regs hpost)
  · exact (savedChild_eq_of_pushParent_internal regs hpush).trans
      hpost.savedChild_eq
  · simpa [updated] using hactiveFinal

end Internal
end ParentPhase
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
