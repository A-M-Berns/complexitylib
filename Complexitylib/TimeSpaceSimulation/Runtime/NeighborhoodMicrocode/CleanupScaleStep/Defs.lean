/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Dispatcher
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation

/-!
# Concrete cleanup-scale scheduler step
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CleanupScaleStep

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The parent phase after undoing one prepare-child scaling operation. -/
def resumedParent
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (residue residuesLeft nextChild : ℕ) :
    NeighborhoodScheduler.Frame tm instanceData :=
  { frame with
    phase := .cleanupCall residue residuesLeft nextChild }

/-- The logical bank after undoing one prepare-child scaling operation. -/
def scaledBank
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (residue : ℕ)
    (child :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))
    (bank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    NeighborhoodExecutableEvaluation.Residue.Registers
      tm instanceData.blockLength :=
  NeighborhoodExecutableEvaluation.Residue.scaleAt
    tm instanceData.blockLength
    (TreeEval.CookMertz.PrimeField.Runtime.inverse
      (NeighborhoodScheduler.fieldModulus instanceData) residue)
    bank (frame.childTarget child)

/-- Initialize the local constant and execute the complete inverse-scaling
fragment. -/
def step
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (.basic
      (.imm (Dispatcher.cleanupInverseRegisters regs).one 1))
    (Dispatcher.cleanupScale regs)

end CleanupScaleStep
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
