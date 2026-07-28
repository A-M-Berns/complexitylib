/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Dispatcher.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation.Defs

/-!
# Exhausted scheduler-cursor transitions

These commands close the two child folds whose cursor has reached the graph
fan-in.  They decode the active phase themselves, so no stale decoder scratch
is trusted at entry.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CursorFinish

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The active parent after exhausting its prepare-child cursor. -/
def combineFrame
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (residue residuesLeft : ℕ) :
    NeighborhoodScheduler.Frame tm instanceData :=
  { frame with phase := .combine residue residuesLeft }

/-- The active parent after finishing a nonfinal residue. -/
def nextResidueFrame
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (residue residuesLeft : ℕ) :
    NeighborhoodScheduler.Frame tm instanceData :=
  { frame with phase := .prepare (residue + 1) residuesLeft 0 }

/-- Exact scratch footprint of phase decoding and phase rebuilding. -/
def phaseWriteFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  ControlDecode.scratchFootprint regs ∪
    {Layout.phaseCode regs,
      (Layout.frameCodecRegisters regs).quotient,
      Layout.codecDigit regs}

/-- Rebuild the combine phase after phase decoding has recovered its two
residue fields. -/
def combineAfterDecode
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [.basic (.imm (Dispatcher.decodedChild regs) 0),
      .basic (.imm (Dispatcher.decodedNextChild regs) 0),
      Dispatcher.encodePhase regs 2
        (Dispatcher.decodedResidue regs)
        (Dispatcher.decodedResiduesLeft regs)
        (Dispatcher.decodedChild regs)
        (Dispatcher.decodedNextChild regs)]

/-- Increment the residue, decrement the positive remaining-residue count,
clear both child cursors, and rebuild the prepare phase. -/
def nextResidueAfterDecode
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [.basic (.imm (Layout.codecDigit regs) 1),
      .basic
        (.add (Dispatcher.decodedResidue regs)
          (Dispatcher.decodedResidue regs) (Layout.codecDigit regs)),
      .basic
        (.sub (Dispatcher.decodedResiduesLeft regs)
          (Dispatcher.decodedResiduesLeft regs)
          (Layout.codecDigit regs)),
      .basic (.imm (Dispatcher.decodedChild regs) 0),
      .basic (.imm (Dispatcher.decodedNextChild regs) 0),
      Dispatcher.encodePhase regs 1
        (Dispatcher.decodedResidue regs)
        (Dispatcher.decodedResiduesLeft regs)
        (Dispatcher.decodedChild regs)
        (Dispatcher.decodedNextChild regs)]

/-- Decode and close an exhausted prepare cursor. -/
def finishPrepare
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq (ControlDecode.decodePhase regs) (combineAfterDecode regs)

/-- Decode and close an exhausted cleanup cursor.  A final residue pops the
active frame; otherwise execution advances to the next residue. -/
def finishCleanup
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (ControlDecode.decodePhase regs)
    (.ifZero (Dispatcher.decodedResiduesLeft regs)
      (FrameTransfer.popParent regs)
      (nextResidueAfterDecode regs))

/-- Exact result of rebuilding one active phase. -/
structure PhaseUpdatePost
    (regs : NeighborhoodTrial.Registers controller)
    (phase : NeighborhoodScheduler.Phase workTapeCount)
    (initial final : Store) : Prop where
  /-- The active phase has the exact semantic encoding. -/
  phaseCode_eq :
    final (Layout.phaseCode regs) =
      FrameCodec.encodePhase
        (initial (Layout.chunkRadix regs)) phase
  /-- Every cell outside phase scratch is preserved. -/
  eq_outside :
    ∀ address, address ∉ phaseWriteFootprint regs →
      final address = initial address

end CursorFinish
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
