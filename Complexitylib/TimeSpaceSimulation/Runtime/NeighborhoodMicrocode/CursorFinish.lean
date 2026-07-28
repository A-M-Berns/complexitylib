/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CursorFinish.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CursorFinish.Internal

/-!
# Exhausted scheduler-cursor transitions
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CursorFinish

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Closing an exhausted prepare cursor writes only inside the evaluator
layout. -/
theorem finishPrepare_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (finishPrepare regs) :=
  Internal.finishPrepare_writesWithin_internal regs

/-- Closing an exhausted cleanup cursor writes only inside the evaluator
layout. -/
theorem finishCleanup_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (finishCleanup regs) :=
  Internal.finishCleanup_writesWithin_internal regs

/-- Advancing to the next residue after phase decoding writes only the exact
phase-rebuilding scratch footprint. -/
theorem nextResidueAfterDecode_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (phaseWriteFootprint regs)
      (nextResidueAfterDecode regs) :=
  Internal.nextResidueAfterDecode_writesWithin_internal regs

/-- Advancing decoded residue cursors increments the residue, decrements
the positive remainder, clears both child cursors, and encodes the exact
prepare phase. -/
theorem nextResidueAfterDecode_runs
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
        store final :=
  Internal.nextResidueAfterDecode_runs_internal
    (workTapeCount := workTapeCount)
    regs store base residue residuesLeft hbase hresidue hleft
    hbaseValue hbankValue hdecodedResidue hdecodedLeft

/-- An exact phase-only update transports a represented nonempty query
state to the corresponding updated active frame. -/
theorem PhaseUpdatePost.queryState
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
      final :=
  Internal.phaseUpdatePost_queryState_internal
    regs frame updated rest logicalBank initial final hquery hfields
    hpost hbounds

/-- An exhausted prepare cursor changes exactly the active phase from
`prepare` to `combine`. -/
theorem finishPrepare_runs
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
        final :=
  Internal.finishPrepare_runs_internal
    regs frame rest logicalBank store residue residuesLeft childIndex
    hquery hphase hexhausted

/-- Exhausting cleanup on the final residue pops the active frame and
preserves the catalytic bank. -/
theorem finishCleanup_zero_runs
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
        final :=
  Internal.finishCleanup_zero_runs_internal
    regs frame rest logicalBank store residue childIndex
    hquery hphase hexhausted

/-- Exhausting cleanup with another residue remaining increments the
residue, decrements the remainder, and resets the prepare cursor to zero. -/
theorem finishCleanup_succ_runs
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
        final :=
  Internal.finishCleanup_succ_runs_internal
    regs frame rest logicalBank store residue residuesLeft childIndex
    hquery hphase hexhausted

end CursorFinish
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
