/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalStep.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalStep.Internal

/-!
# Fixed-source transition on a packed local configuration

This surface exposes the exact refinement theorem for one deterministic
source-machine transition. The generated command is uniform in runtime
data: only the fixed source machine, its state order, and its named-tape
count are embedded in the command syntax.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalStep

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- One packed local step writes only its fixed direct-register footprint. -/
theorem step_writesWithin
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (footprint regs)
      (step tm order controller regs) :=
  Internal.step_writesWithin_internal tm order controller regs

/-- Compiling one packed local step preserves its fixed source write
footprint. -/
theorem step_compiledWritesWithin
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (step tm order controller regs).compile (footprint regs) :=
  Internal.step_compiledWritesWithin_internal
    tm order controller regs

/-- The fixed-source microcode performs exactly one deterministic source
transition, or leaves an already halted configuration frozen. The represented
high suffix, live caller context, and every address outside the fixed
footprint are preserved. -/
theorem step_runs
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (nodeTape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (store : Store)
    (hfits :
      ∀ digit ∈
          FrameCodec.nodeDigits
            (show
              NeighborhoodEvaluator.QueryNode
                workTapeCount instanceData.horizon
              from .graph (.computation nodeTape slot interval)),
        digit < Representation.digitBase instanceData)
    (hcontext :
      CombineTerm.ComputationContext regs instanceData nodeTape slot
        interval logicalBank store)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hinterval : interval ≤ instanceData.horizon)
    (hcenters :
      centers =
        NeighborhoodGraph.Guess.Consistency.guessedCenters
          instanceData.guess interval)
    (hrep :
      PackedLocalRepresentation.Represents tm order
        instanceData.blockLength centers cfg suffix word)
    (hheads :
      HeadsInWindow instanceData.blockLength centers cfg)
    (hnextHeads :
      HeadsInWindow instanceData.blockLength centers
        ((tm.step cfg).getD cfg))
    (hword : store (bankRegisters regs).word = word)
    (hrangeOne :
      store (CombineValue.rangeRegisters regs).one = 1) :
    ∃ final,
      Runs (step tm order controller regs) store final ∧
      Post tm order instanceData.blockLength centers
        ((tm.step cfg).getD cfg) suffix regs store final :=
  Internal.step_runs_internal order regs instanceData nodeTape slot
    interval logicalBank code centers cfg suffix word store hfits
    hcontext hstoreGuess hguess hinterval hcenters hrep hheads
    hnextHeads hword hrangeOne

end PackedLocalStep
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
