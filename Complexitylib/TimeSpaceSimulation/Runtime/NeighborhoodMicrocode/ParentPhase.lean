/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ParentPhase.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ParentPhase.Internal

/-!
# Parent-phase advancement before recursive descent
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ParentPhase

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Prepare-parent advancement writes only its fixed five-cell footprint. -/
theorem advancePrepare_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (writeFootprint regs) (advancePrepare regs) :=
  Internal.advancePrepare_writesWithin_internal regs

/-- Cleanup-parent advancement writes only its fixed five-cell footprint. -/
theorem advanceCleanup_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (writeFootprint regs) (advanceCleanup regs) :=
  Internal.advanceCleanup_writesWithin_internal regs

/-- Every parent-advancement destination belongs to the evaluator layout. -/
theorem writeFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    writeFootprint regs ⊆ regs.layout.footprint :=
  Internal.writeFootprint_subset_layout_internal regs

/-- The prepare branch saves its current child and commits the exact
successor prepare phase. -/
theorem advancePrepare_runs
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
        store final :=
  Internal.advancePrepare_runs_internal
    regs store base residue residuesLeft child hbase hresidue hleft
    hbaseValue hbankValue hdecodedResidue hdecodedLeft
    hdecodedChild hdecodedNext

/-- The cleanup-call branch saves its current child and commits the exact
cleanup-scale continuation. -/
theorem advanceCleanup_runs
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
        store final :=
  Internal.advanceCleanup_runs_internal
    regs store base residue residuesLeft child hbase hresidue hleft
    hbaseValue hbankValue hdecodedResidue hdecodedLeft hdecodedChild

/-- Prepare-parent advancement transports the exact active-frame
representation to the semantic successor parent. -/
theorem ActiveFrame.of_advancePrepare
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
  Internal.activeFrame_advancePrepare_internal
    regs frame residue residuesLeft child initial final hactive hpost

/-- Cleanup-parent advancement transports the exact active-frame
representation to the semantic cleanup-scale continuation. -/
theorem ActiveFrame.of_advanceCleanup
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
  Internal.activeFrame_advanceCleanup_internal
    regs frame residue residuesLeft child initial final hactive hpost

/-- A bounded prepare parent remains bounded after advancing its child
cursor. -/
theorem frameBound_advancePrepare
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
        phase := .prepare residue residuesLeft (child.val + 1) } :=
  Internal.frameBound_advancePrepare_internal
    frame residue residuesLeft child hphase hbound

/-- A bounded cleanup parent remains bounded after committing its
cleanup-scale continuation. -/
theorem frameBound_advanceCleanup
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
          .cleanupScale residue residuesLeft child (child.val + 1) } :=
  Internal.frameBound_advanceCleanup_internal
    frame residue residuesLeft child hphase hbound

/-- Parent-phase advancement preserves every retained runtime parameter. -/
theorem Parameters.of_advancePost
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store)
    (hparameters : Representation.Parameters regs instanceData initial)
    (hpost : AdvancePost regs child phaseCode initial final) :
    Representation.Parameters regs instanceData final :=
  Internal.parameters_of_advancePost_internal
    regs initial final hparameters hpost

/-- Parent-phase advancement never changes the catalytic bank. -/
theorem AdvancePost.bank_eq
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hpost : AdvancePost regs child phaseCode initial final) :
    final regs.layout.bank = initial regs.layout.bank :=
  Internal.advancePost_bank_eq_internal regs hpost

/-- Advancing a prepare parent preserves its represented suspended tail. -/
theorem Stack.of_advancePrepare
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
  Internal.stack_advancePrepare_internal
    regs frame rest residue residuesLeft child initial final
    hstack hpost

/-- Advancing a cleanup parent preserves its represented suspended tail. -/
theorem Stack.of_advanceCleanup
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
  Internal.stack_advanceCleanup_internal
    regs frame rest residue residuesLeft child initial final
    hstack hpost

/-- Advancing and suspending a prepare parent stays inside the shared
evaluator layout. -/
theorem suspendPrepare_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      regs.layout.footprint (suspendPrepare regs) :=
  Internal.suspendPrepare_writesWithin_internal regs

/-- Advancing and suspending a cleanup parent stays inside the shared
evaluator layout. -/
theorem suspendCleanup_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      regs.layout.footprint (suspendCleanup regs) :=
  Internal.suspendCleanup_writesWithin_internal regs

/-- The concrete prepare-parent command commits the successor continuation,
packs it, and retains the original child cursor for regeneration. -/
theorem suspendPrepare_runs
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
        final :=
  Internal.suspendPrepare_runs_internal
    regs frame rest store residue residuesLeft child hstack
    hparameters hbase hresidue hleft hdecodedResidue
    hdecodedLeft hdecodedChild hdecodedNext hupdatedBound

/-- The concrete cleanup-parent command commits the cleanup-scale
continuation, packs it, and retains the original child cursor. -/
theorem suspendCleanup_runs
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
        final :=
  Internal.suspendCleanup_runs_internal
    regs frame rest store residue residuesLeft child hstack
    hparameters hbase hresidue hleft hdecodedResidue
    hdecodedLeft hdecodedChild hupdatedBound

end ParentPhase
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
