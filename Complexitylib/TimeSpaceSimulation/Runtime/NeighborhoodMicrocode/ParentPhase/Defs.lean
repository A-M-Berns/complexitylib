/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildNode.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Dispatcher.Defs

/-!
# Parent-phase advancement before recursive descent

Before an active frame is suspended, its child cursor must advance to the
continuation phase that will resume after the child returns. These fragments
save the current child cursor for node regeneration and rebuild the exact
prepare or cleanup-scale parent phase.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ParentPhase

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Exact mutable footprint of both parent-phase advancement fragments. -/
def writeFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  {ChildNode.savedChildIndex regs,
    Dispatcher.decodedChild regs,
    Dispatcher.decodedNextChild regs,
    Layout.phaseCode regs,
    Layout.codecDigit regs}

/-- Save the current prepare child and commit the successor prepare cursor. -/
def advancePrepare
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [ControlDecode.copy
      (ChildNode.savedChildIndex regs)
      (Dispatcher.decodedChild regs),
      .basic (.imm (Layout.codecDigit regs) 1),
      .basic
        (.add (Dispatcher.decodedChild regs)
          (Dispatcher.decodedChild regs) (Layout.codecDigit regs)),
      Dispatcher.encodePhase regs 1
        (Dispatcher.decodedResidue regs)
        (Dispatcher.decodedResiduesLeft regs)
        (Dispatcher.decodedChild regs)
        (Dispatcher.decodedNextChild regs)]

/-- Save the current cleanup child and commit its cleanup-scale continuation. -/
def advanceCleanup
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [ControlDecode.copy
      (ChildNode.savedChildIndex regs)
      (Dispatcher.decodedChild regs),
      ControlDecode.copy
        (Dispatcher.decodedNextChild regs)
        (Dispatcher.decodedChild regs),
      .basic (.imm (Layout.codecDigit regs) 1),
      .basic
        (.add (Dispatcher.decodedNextChild regs)
          (Dispatcher.decodedNextChild regs) (Layout.codecDigit regs)),
      Dispatcher.encodePhase regs 4
        (Dispatcher.decodedResidue regs)
        (Dispatcher.decodedResiduesLeft regs)
        (Dispatcher.decodedChild regs)
        (Dispatcher.decodedNextChild regs)]

/-- Advance and pack a prepare parent in one concrete command. -/
def suspendPrepare
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq (advancePrepare regs) (FrameTransfer.pushParent regs)

/-- Advance and pack a cleanup parent in one concrete command. -/
def suspendCleanup
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq (advanceCleanup regs) (FrameTransfer.pushParent regs)

/-- Observable result of advancing either parent cursor. -/
structure AdvancePost
    (regs : NeighborhoodTrial.Registers controller)
    (child phaseCode : ℕ) (initial final : Store) : Prop where
  /-- The original child cursor is retained across stack transfer. -/
  savedChild_eq :
    final (ChildNode.savedChildIndex regs) = child
  /-- The parent phase is rebuilt exactly. -/
  phaseCode_eq : final (Layout.phaseCode regs) = phaseCode
  /-- Every cell outside the exact advancement footprint is preserved. -/
  eq_outside :
    ∀ address, address ∉ writeFootprint regs →
      final address = initial address

end ParentPhase
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
