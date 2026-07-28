/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildReady.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ChildReady.Internal

/-!
# Regenerating a child node and catalytic target
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ChildReady

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Child preparation writes only its exact fixed physical footprint. -/
theorem prepare_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (writeFootprint regs)
      (prepare workTapeCount controller regs) :=
  Internal.prepare_writesWithin_internal
    workTapeCount controller regs

/-- Every child-preparation destination belongs to the shared evaluator
layout. -/
theorem writeFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    writeFootprint regs ⊆ regs.layout.footprint :=
  Internal.writeFootprint_subset_layout_internal regs

/-- Child preparation preserves every retained runtime parameter. -/
theorem Parameters.of_readyPost
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store)
    (hparameters : Representation.Parameters regs instanceData initial)
    (hpost : ReadyPost regs node target initial final) :
    Representation.Parameters regs instanceData final :=
  Internal.parameters_of_readyPost_internal
    regs initial final hparameters hpost

/-- Child preparation leaves the packed suspended-stack word unchanged. -/
theorem ReadyPost.stackWord_eq
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hpost : ReadyPost regs node target initial final) :
    final (Layout.frameStackRegisters regs).word =
      initial (Layout.frameStackRegisters regs).word :=
  Internal.readyPost_stackWord_eq_internal regs hpost

/-- Child preparation leaves the packed catalytic-bank word unchanged. -/
theorem ReadyPost.bank_eq
    (regs : NeighborhoodTrial.Registers controller)
    {initial final : Store}
    (hpost : ReadyPost regs node target initial final) :
    final regs.layout.bank = initial regs.layout.bank :=
  Internal.readyPost_bank_eq_internal regs hpost

/-- Decode a suspended computation parent, regenerate one saved
role-major predecessor, and install its exact catalytic target. -/
theorem prepare_frameChild_runs
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
        store final :=
  Internal.prepare_frameChild_runs_internal
    code frame controller regs store parentTape tape parentSlot kind
    interval hinterval hactive hparameters hbound hchild hstoreGuess
    hguess hnode

end ChildReady
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
