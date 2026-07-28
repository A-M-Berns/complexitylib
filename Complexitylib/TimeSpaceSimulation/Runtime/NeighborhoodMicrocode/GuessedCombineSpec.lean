/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.GuessedCombineSpec.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.GuessedCombineSpec.Internal

/-!
# Prefix-relative packed computation kernels
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace GuessedCombineSpec

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- A uniform packed kernel driven by guessed centers implements the original
certificate callback at every computation node whose movement prefix is
correct. -/
theorem packedKernelSpecAt_of_prefix
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : Fin instanceData.horizon)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (outputChunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (kernel : Cmd)
    (hprefix :
      ∀ boundary : Fin (instanceData.horizon + 1),
        boundary.val ≤ interval.val →
          ∀ namedTape : TapeIndex workTapeCount,
            instanceData.guess.derivedCenter
                namedTape boundary.val =
              some
                (NeighborhoodGraph.Guess.actualCenterTrajectory
                  tm instanceData.x instanceData.blockLength
                    namedTape boundary.val))
    (hspec :
      PackedKernelSpecAt regs instanceData frame tape slot interval
        logicalBank outputChunk kernel) :
    CombineTerm.ComputationPackedKernelSpecAt
      regs instanceData frame tape slot interval.val logicalBank
        outputChunk kernel :=
  Internal.packedKernelSpecAt_of_prefix_internal
    regs instanceData frame tape slot interval logicalBank
      outputChunk kernel hprefix hspec

end GuessedCombineSpec
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
