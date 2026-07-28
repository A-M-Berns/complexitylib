/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.GuessedLocalEvaluation
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.GuessedCombineSpec.Defs

/-!
# Prefix-relative packed computation kernels -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace GuessedCombineSpec
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

theorem packedKernelSpecAt_of_prefix_internal
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
        outputChunk kernel := by
  have hcenters :
      ∀ namedTape : TapeIndex workTapeCount,
        instanceData.guess.derivedCenter namedTape interval.val =
          some
            (NeighborhoodGraph.centerBlock
              tm instanceData.x instanceData.blockLength
                interval.val namedTape) := by
    intro namedTape
    simpa only
      [NeighborhoodGraph.Guess.actualCenterTrajectory] using
        hprefix interval.castSucc (Nat.le_refl _) namedTape
  have hcombine :=
    GuessedLocalEvaluation.booleanCombineAtGuess_eq
      tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.guess interval hcenters tape slot
  unfold PackedKernelSpecAt at hspec
  unfold CombineTerm.ComputationPackedKernelSpecAt
  simpa only [hcombine] using hspec

end Internal
end GuessedCombineSpec
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
