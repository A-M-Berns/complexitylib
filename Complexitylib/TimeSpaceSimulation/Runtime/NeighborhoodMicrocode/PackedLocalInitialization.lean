/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalInitialization.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalInitialization.Internal

/-!
# Fixed-source initialization of a packed local configuration

This surface exposes both the fixed write-footprint guarantees and the exact
semantic refinement theorem for the uniform assignment decoder.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalInitialization

open RAM Structured
open NeighborhoodGraph

variable {controller : SearchProgram.Registers}

/-- Packed initialization writes only its fixed combine-scratch footprint. -/
theorem build_writesWithin
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (build tm order controller regs) :=
  Internal.build_writesWithin_internal tm order controller regs

/-- Compiling packed initialization preserves its fixed source footprint. -/
theorem build_compiledWritesWithin
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (build tm order controller regs).compile
      (footprint regs) :=
  Internal.build_compiledWritesWithin_internal
    tm order controller regs

/-- Packed initialization builds the exact local start configuration while
preserving the surrounding range fold, catalytic bank, and runtime ABI. -/
theorem build_runs
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : Fin instanceData.horizon)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (guessCode :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (assignment suffix : ℕ)
    (store : Store)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph
                (.computation nodeTape slot interval.val)),
        digit < Representation.digitBase instanceData)
    (hcomputation :
      CombineTerm.ComputationContext regs instanceData nodeTape slot
        interval.val logicalBank store)
    (hstoreGuess :
      store controller.guess = guessCode.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess guessCode)
    (hassignment :
      store (CombineValue.rangeRegisters regs).remaining =
        assignment)
    (hword : store (packedWord regs) = suffix)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1) :
    ∃ final,
      Runs (build tm order controller regs) store final ∧
      Post tm order instanceData.blockLength instanceData.positive
        instanceData.guess interval assignment suffix regs
        store final :=
  Internal.build_runs_internal order regs instanceData nodeTape slot
    interval logicalBank guessCode assignment suffix store hfits
    hcomputation hstoreGuess hguess hassignment hword hone

end PackedLocalInitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
