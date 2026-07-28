/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.StateRootInitialization.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.StateRootInitialization.Internal

/-!
# Uniform initialization of the state-consistency root
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace StateRootInitialization

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The state-root builder writes only its five fixed evaluator cells. -/
theorem buildStateRoot_writesWithin
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (rootFootprint regs)
      (buildStateRoot controller regs) :=
  Internal.buildStateRoot_writesWithin_internal controller regs

/-- Every state-root destination belongs to the fixed evaluator layout. -/
theorem rootFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    rootFootprint regs ⊆ regs.layout.footprint :=
  Internal.rootFootprint_subset_layout_internal regs

/-- State-root construction followed by query initialization stays inside
the fixed evaluator layout. -/
theorem initializeStateQuery_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (initializeStateQuery workTapeCount controller regs) :=
  Internal.initializeStateQuery_writesWithin_internal
    workTapeCount controller regs

/-- The fixed root builder reads the runtime horizon and installs exactly the
state-consistency root of every enumerated runtime guess. -/
theorem buildStateRoot_runs
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (store : Store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (buildStateRoot controller regs) store final ∧
      Representation.Parameters regs instanceData final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (NeighborhoodEvaluator.stateRoot instanceData.guess) ∧
      final controller.one = 1 :=
  Internal.buildStateRoot_runs_internal
    controller regs instanceData store hparameters hone

/-- Uniform root construction and query initialization establish the exact
logical state query with an empty continuation stack and zero catalytic bank. -/
theorem initializeStateQuery_runs
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (store : Store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs
        (initializeStateQuery workTapeCount controller regs)
        store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.Decision.queryInitial
          (NeighborhoodEvaluator.stateRoot instanceData.guess))
        final ∧
      final controller.one = 1 :=
  Internal.initializeStateQuery_runs_internal
    controller regs instanceData store hparameters hone

/-- Query initialization preserves the complete outer ABI required by the
uniform scheduler loop, including the packed guess word. -/
theorem initializeStateQuery_runs_preserving_abi
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (word : ℕ)
    (store : Store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hone : store controller.one = 1)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hguess : store controller.guess = word) :
    ∃ final,
      Runs
        (initializeStateQuery workTapeCount controller regs)
        store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.Decision.queryInitial
          (NeighborhoodEvaluator.stateRoot instanceData.guess))
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = word :=
  Internal.initializeStateQuery_runs_preserving_abi_internal
    controller regs instanceData word store hparameters hone
    hframe hinputLength hguess

end StateRootInitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
