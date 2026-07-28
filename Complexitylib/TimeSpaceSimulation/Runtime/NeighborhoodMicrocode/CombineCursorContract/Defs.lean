/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm.Defs

/-!
# Runtime-cursor contracts for computation-node factors

The combine driver temporarily stores the selected grouped output coordinate
in `Layout.active`. A uniform packed-factor command must therefore receive an
explicit equation between that runtime cursor and the semantic output chunk.
The frame context alone does not supply this equation.

This module records the strengthened context used by the final computation
chunk provider. Both packed and basis factors preserve it, so the output
coordinate remains synchronized throughout the complete assignment range.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CombineCursorContract

open RAM Structured
open TreeEval CookMertz

variable {controller : SearchProgram.Registers}

/-- A represented computation frame together with its selected runtime
grouped-output cursor. -/
structure Context
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (store : Store) : Prop where
  /-- Stable computation-frame and packed-bank representation. -/
  frameContext :
    CombineTerm.ComputationFrameContext regs instanceData frame tape slot
      interval logicalBank store
  /-- The temporary active cell is the selected grouped output coordinate. -/
  cursor_eq : store (Layout.active regs) = outputChunk.val

/-- Correct runtime-cursor contract for the packed Boolean-node factor. -/
def PackedKernelSpecAt
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
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
      (NeighborhoodExecutableEvaluation.booleanCombine
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive tape slot interval)
      outputChunk)
    (Context regs instanceData frame tape slot interval logicalBank
      outputChunk)

/-- Correct runtime-cursor contract for the tensor-basis factor. -/
def BasisKernelSpecAt
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (kernel : Cmd) : Prop :=
  CombineTerm.BasisKernelSpecAtContext regs kernel
    (NeighborhoodScheduler.fieldModulus instanceData)
    (CombineTerm.basisAssignmentValue
      (NeighborhoodExecutableEvaluation.payloadWidth
        tm instanceData.blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
      (CombineTerm.computationArguments frame logicalBank))
    (Context regs instanceData frame tape slot interval logicalBank
      outputChunk)

end CombineCursorContract
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
