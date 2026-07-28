/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.GuessedLocalEvaluation.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm.Defs

/-!
# Prefix-relative packed computation kernels

The uniform packed kernel reads centers from the movement guess. Its exact
specification is therefore phrased against `booleanCombineAtGuess`; on a
correct prefix the surface theorem transports it to the certificate-level
`ComputationPackedKernelSpecAt`.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace GuessedCombineSpec

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Packed-factor kernel contract at the current streamed movement centers.
The source command remains independent of the runtime candidate, interval,
assignment, and output chunk. -/
def PackedKernelSpecAt
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
    (kernel : Cmd) : Prop :=
  CombineTerm.PackedKernelSpecAtContext regs kernel
    (NeighborhoodScheduler.fieldModulus instanceData)
    (CombineTerm.packedAssignmentValue
      (NeighborhoodExecutableEvaluation.payloadWidth
        tm instanceData.blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
      (GuessedLocalEvaluation.booleanCombineAtGuess
        tm instanceData.blockLength instanceData.encoding
        instanceData.positive instanceData.guess interval tape slot)
      outputChunk)
    (CombineTerm.ComputationFrameContext regs instanceData frame tape slot
      interval.val logicalBank)

end GuessedCombineSpec
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
