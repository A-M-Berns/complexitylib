/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PrepareDescent.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PrepareDescent.Internal

/-!
# Concrete prepare-child descent
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PrepareDescent

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Prepare descent writes entirely within the shared evaluator layout. -/
theorem descendChild_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (descendChild workTapeCount controller regs) :=
  Internal.descendChild_writesWithin_internal
    workTapeCount controller regs

/-- A represented computation prepare call scales the selected catalytic
target, advances and suspends its parent, regenerates the selected
predecessor node, and installs the exact prepare-child successor state. -/
theorem descendChild_computation_runs
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (parentTape tape : TapeIndex workTapeCount)
    (parentSlot : NeighborhoodGraph.Slot)
    (kind : NeighborhoodGraph.PredecessorKind)
    (interval residue residuesLeft : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (hselected :
      child =
        NeighborhoodGraph.predecessorIndexEquiv
          workTapeCount (kind, tape))
    (hinterval : interval < instanceData.horizon)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hphase :
      frame.phase =
        .prepare residue residuesLeft child.val)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval))
    (hdecodedResidue :
      store (Dispatcher.decodedResidue regs) = residue)
    (hdecodedChild :
      store (Dispatcher.decodedChild regs) = child.val)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code) :
    ∃ final,
      Runs
        (descendChild workTapeCount controller regs)
        store final ∧
      Representation.QueryState regs instanceData
        { stack :=
            frame.prepareChild child ::
              advancedParent frame residue residuesLeft child ::
              rest
          registers :=
            NeighborhoodExecutableEvaluation.Residue.scaleAt
              tm instanceData.blockLength residue logicalBank
              (frame.childTarget child) }
        final :=
  Internal.descendChild_computation_runs_internal
    code frame rest logicalBank controller regs store parentTape tape
    parentSlot kind interval residue residuesLeft child hselected
    hinterval hquery hphase hnode hdecodedResidue hdecodedChild
    hstoreGuess hguess

end PrepareDescent
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
