/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedComputationKernel.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedComputationKernel.Internal

/-!
# Fixed packed computation-factor kernel

This surface exposes the exact source footprint and semantic refinement of
the fixed command that initializes, traces, and reads one packed local
configuration before restoring its caller's range state.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedComputationKernel

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The complete fixed packed computation-factor command writes only its
declared packed-step footprint. -/
theorem command_writesWithin
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (command tm order controller regs) :=
  Internal.command_writesWithin_internal tm order controller regs

/-- Under the exact active-frame, movement-guess, and output-cursor
representation, the fixed command computes the requested packed Boolean
factor and restores the surrounding range state and representation. -/
theorem command_spec
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : Fin instanceData.horizon)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (outputChunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (hencoding :
      instanceData.encoding =
        NeighborhoodExecutableEvaluation.FiniteEncoding.ofStateOrder
          order instanceData.blockLength)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code) :
    SpecAt order regs instanceData frame tape slot interval logicalBank code
      outputChunk :=
  Internal.command_spec_internal order regs instanceData frame tape slot
    interval logicalBank code outputChunk hencoding hguess

end PackedComputationKernel
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
