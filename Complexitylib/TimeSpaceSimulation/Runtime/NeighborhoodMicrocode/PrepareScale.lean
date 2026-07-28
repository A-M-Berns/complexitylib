/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PrepareScale.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PrepareScale.Internal

/-!
# Prepare-fold catalytic-bank scaling

This surface exposes the fixed-footprint RAM fragment and its exact logical
catalytic-bank semantics.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PrepareScale

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Prepare-child scaling writes only within its exact declared footprint. -/
theorem scaleChildTarget_writesWithin
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (writeFootprint regs)
      (scaleChildTarget regs) :=
  Internal.scaleChildTarget_writesWithin_internal regs

/-- The prepare-child scaling footprint lies inside the shared evaluator
layout. -/
theorem writeFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    writeFootprint regs ⊆ regs.layout.footprint :=
  Internal.writeFootprint_subset_layout_internal regs

/-- Prepare-child scaling terminates, restores the active parent ABI, and
updates exactly the selected catalytic child coordinate. -/
theorem scaleChildTarget_runs
    {workTapeCount : ℕ} (tm : TM workTapeCount)
    (blockLength parentScalar residue base word : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (out :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (child :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount))
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store)
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hword :
      store
          (Layout.residueScaleRegisters regs).bank.bank.word =
        word)
    (hrep :
      NeighborhoodProgram.RepresentsResidueBank
        tm blockLength base word original)
    (hwordLt :
      word <
        base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)))
    (hbaseValue :
      store
          (Layout.residueScaleRegisters regs).bank.bank.base =
        base)
    (hmodulusValue :
      store (Layout.residueScaleRegisters regs).bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store (Layout.residueScaleRegisters regs).bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hone :
      store (Dispatcher.cleanupInverseRegisters regs).one = 1)
    (hscalar : store (Layout.scalar regs) = parentScalar)
    (hout : store (Layout.out regs) = out.val)
    (hchunkCount :
      store (Layout.chunkCount regs) =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))
    (hdecodedResidue :
      store (Dispatcher.decodedResidue regs) = residue)
    (hdecodedChild :
      store (Dispatcher.decodedChild regs) = child.val) :
    ∃ final finalWord,
      Runs (scaleChildTarget regs) store final ∧
      ScalePost tm blockLength parentScalar residue base finalWord
        original out child regs store final :=
  Internal.scaleChildTarget_runs_internal
    tm blockLength parentScalar residue base word original out child
    regs store hbase hmodulus hmodulusBase hword hrep hwordLt
    hbaseValue hmodulusValue hmodulusPred hone hscalar hout
    hchunkCount hdecodedResidue hdecodedChild

end PrepareScale
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
