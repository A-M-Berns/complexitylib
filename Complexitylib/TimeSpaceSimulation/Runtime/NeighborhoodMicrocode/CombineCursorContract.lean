/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineCursorContract.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineCursorContract.Internal

/-!
# Runtime-cursor contracts for computation-node factors

This surface exposes the strengthened computation context that explicitly
ties the combine driver's temporary active cell to the semantic grouped
output chunk.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CombineCursorContract

open RAM Structured
open TreeEval CookMertz

variable {controller : SearchProgram.Registers}

/-- ABI-preserving commands that restore the packed catalytic bank preserve
the exact runtime-cursor computation context. -/
theorem context_transport
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
    {initial final : Store}
    (hcontext :
      Context regs instanceData frame tape slot interval logicalBank
        outputChunk initial)
    (habi : ControlDecode.PreservesABI regs initial final)
    (hbank :
      final regs.layout.bank = initial regs.layout.bank) :
    Context regs instanceData frame tape slot interval logicalBank
      outputChunk final :=
  Internal.context_transport_internal
    regs instanceData frame tape slot interval logicalBank outputChunk
    hcontext habi hbank

/-- The range driver's accumulator, test, countdown, and one cells are
disjoint from the stable frame, bank, and runtime output cursor. -/
theorem context_stableUnderDriverWrites
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
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))) :
    CombineValue.StableUnderDriverWrites
      (CombineValue.rangeRegisters regs)
      (Context regs instanceData frame tape slot interval logicalBank
        outputChunk) :=
  Internal.context_stableUnderDriverWrites_internal
    regs instanceData frame tape slot interval logicalBank outputChunk

end CombineCursorContract
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
