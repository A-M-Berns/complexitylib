/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryInitialization.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryInitialization.Internal

/-!
# Initializing one represented neighborhood query
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace QueryInitialization

open RAM Structured
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

/-- Query initialization writes only in the fixed evaluator workspace. -/
theorem initialize_writesWithin
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (initializeQuery workTapeCount regs) :=
  Internal.initialize_writesWithin_internal workTapeCount regs

/-- From retained runtime parameters and a prebuilt bounded root, the
initializer establishes the exact singleton scheduler representation with an
all-zero catalytic bank. -/
theorem initialize_runs
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (node :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon)
    (store : Store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hnodeCode :
      store (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData) node)
    (hnodeBound :
      NeighborhoodScheduler.FrameBounds.QueryBound
        instanceData.horizon node) :
    ∃ final,
      Runs (initializeQuery workTapeCount regs) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.initial
          instanceData.horizon node 1
          (Fin.last (graphFanIn workTapeCount))
          (ResidueBankOps.zeroRegisters tm instanceData.blockLength))
        final :=
  Internal.initialize_runs_internal
    regs instanceData node store hparameters hnodeCode hnodeBound

end QueryInitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
