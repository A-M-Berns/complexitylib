/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineCursorContract.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineTerm.Internal

/-!
# Runtime-cursor contracts for computation-node factors -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CombineCursorContract
namespace Internal

open RAM Structured
open TreeEval CookMertz

variable {controller : SearchProgram.Registers}

theorem context_transport_internal
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
      outputChunk final := by
  exact
    { frameContext :=
        CombineTerm.Internal.computationFrameContext_transport_internal
          regs instanceData frame tape slot interval logicalBank
          hcontext.frameContext habi hbank
      cursor_eq := habi.active_eq.trans hcontext.cursor_eq }

theorem context_stableUnderDriverWrites_internal
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
        outputChunk) := by
  intro initial final hcontext houtside
  exact
    { frameContext :=
        CombineTerm.Internal.computationFrameContext_stableUnderDriverWrites_internal
          regs instanceData frame tape slot interval logicalBank
          hcontext.frameContext houtside
      cursor_eq :=
        (houtside (Layout.active regs) (by
          simp [CombineValue.RangeRegisters.driverWriteFootprint,
            CombineValue.rangeRegisters, Layout.active,
            regs.injective.eq_iff])).trans hcontext.cursor_eq }

end Internal
end CombineCursorContract
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
