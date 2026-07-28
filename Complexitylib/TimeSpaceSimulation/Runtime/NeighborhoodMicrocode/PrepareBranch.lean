/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PrepareBranch.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PrepareBranch.Internal

/-!
# Concrete prepare-phase branch
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PrepareBranch

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The complete prepare branch writes only inside the evaluator layout. -/
theorem step_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (step workTapeCount controller regs) :=
  Internal.step_writesWithin_internal
    workTapeCount controller regs

/-- Runtime child-bound selection executes exactly one pure prepare
scheduler step. -/
theorem step_runs
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
    (parentTape : TapeIndex workTapeCount)
    (parentSlot : NeighborhoodGraph.Slot)
    (interval residue residuesLeft childIndex : ℕ)
    (hquery :
      Representation.QueryState regs instanceData
        { stack := frame :: rest
          registers := logicalBank }
        store)
    (hphase :
      frame.phase =
        .prepare residue residuesLeft childIndex)
    (hnode :
      frame.node =
        .graph (.computation parentTape parentSlot interval))
    (hinterval : interval < instanceData.horizon)
    (hdecodedResidue :
      store (Dispatcher.decodedResidue regs) = residue)
    (hdecodedChild :
      store (Dispatcher.decodedChild regs) = childIndex)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code) :
    ∃ final,
      Runs (step workTapeCount controller regs) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.next
          { stack := frame :: rest
            registers := logicalBank })
        final :=
  Internal.step_runs_internal
    code frame rest logicalBank controller regs store parentTape
    parentSlot interval residue residuesLeft childIndex hquery
    hphase hnode hinterval hdecodedResidue hdecodedChild
    hstoreGuess hguess

end PrepareBranch
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
