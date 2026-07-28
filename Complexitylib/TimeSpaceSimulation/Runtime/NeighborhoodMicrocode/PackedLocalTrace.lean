/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalTrace.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalTrace.Internal

/-!
# Runtime-length traces on packed local configurations

The command exposed here has fixed syntax for a fixed source machine. Runtime
block length, local centers, assignment, interval, and trace length remain
store data.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalTrace

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The packed local trace writes only the packed-step footprint. -/
theorem trace_writesWithin
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (PackedLocalStep.footprint regs)
      (trace tm order controller regs) :=
  Internal.trace_writesWithin_internal tm order controller regs

/-- Compiling the packed local trace preserves its fixed source footprint. -/
theorem trace_compiledWritesWithin
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (trace tm order controller regs).compile
      (PackedLocalStep.footprint regs) :=
  Internal.trace_compiledWritesWithin_internal
    tm order controller regs

/-- Starting from the canonical packed assignment configuration and a count
equal to the runtime block length, the loop performs exactly the frozen local
trace. The represented continuation suffix and all live caller state other
than the consumed counter are preserved. -/
theorem trace_runs
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
    (hcontext :
      CombineTerm.ComputationContext regs instanceData nodeTape slot
        interval.val logicalBank store)
    (hstoreGuess : store controller.guess = guessCode.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess guessCode)
    (hword :
      store (PackedLocalStep.bankRegisters regs).word =
        PackedLocalConfiguration.assignmentStartWord
          tm order instanceData.blockLength instanceData.positive
          instanceData.guess interval assignment suffix)
    (hassignment :
      store (CombineValue.rangeRegisters regs).remaining =
        assignment)
    (hcount :
      store (CombineValue.rangeRegisters regs).count =
        instanceData.blockLength)
    (hone :
      store (CombineValue.rangeRegisters regs).one = 1) :
    ∃ final,
      Runs (trace tm order controller regs) store final ∧
      Post tm order instanceData.blockLength
        (NeighborhoodGraph.Guess.Consistency.guessedCenters
          instanceData.guess interval.val)
        (GuessedLocalEvaluation.localTraceAtCenters
          tm instanceData.blockLength
          (NeighborhoodGraph.Guess.Consistency.guessedCenters
            instanceData.guess interval.val)
          (LocalAssignmentSemantics.assignmentInputs
            tm order instanceData.blockLength instanceData.positive
            assignment))
        suffix regs store final :=
  Internal.trace_runs_internal order regs instanceData nodeTape slot
    interval logicalBank guessCode assignment suffix store hfits
    hcontext hstoreGuess hguess hword hassignment hcount hone

end PackedLocalTrace
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
