/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ComputationChunkKernel.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ComputationChunkKernel.Internal

/-!
# Fixed computation-chunk provider

This surface exposes the complete fixed-source computation-chunk command,
its exact guessed-local evaluation semantics, and its finite write footprint.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ComputationChunkKernel

open RAM Structured

/-- The complete provider writes only combine scratch and the controller
constant cell used for reversible catalytic-bank preservation. -/
theorem command_writesWithin
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (footprint controller regs)
      (command tm order controller regs) :=
  Internal.command_writesWithin_internal tm order controller regs

/-- The fixed provider computes one exact grouped output coordinate while
restoring the continuation, catalytic bank, cursor, controller constant, and
active-frame ABI. -/
theorem command_specAt
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
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
    SpecAt order controller regs instanceData frame tape slot interval
      logicalBank code outputChunk :=
  Internal.command_specAt_internal order controller regs instanceData frame
    tape slot interval logicalBank code outputChunk hencoding hguess

end ComputationChunkKernel
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
