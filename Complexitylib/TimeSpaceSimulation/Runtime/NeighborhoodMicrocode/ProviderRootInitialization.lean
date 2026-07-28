/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderRootInit.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderRootInit.Internal

/-!
# Uniform initialization of local-consistency provider queries
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ProviderRootInitialization

open RAM Structured
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

/-- Provider-root construction writes only in its fixed evaluator footprint. -/
theorem buildProviderRoot_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (rootFootprint regs)
      (buildProviderRoot workTapeCount controller regs) :=
  Internal.buildProviderRoot_writesWithin_internal
    workTapeCount controller regs

/-- Every provider-root destination belongs to the common evaluator layout. -/
theorem rootFootprint_subset_layout
    (regs : NeighborhoodTrial.Registers controller) :
    rootFootprint regs ⊆ regs.layout.footprint :=
  Internal.rootFootprint_subset_layout_internal regs

/-- Provider-root construction and zero-bank query initialization stay inside
the common evaluator layout. -/
theorem initializeProviderQuery_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (initializeProviderQuery workTapeCount controller regs) :=
  Internal.initializeProviderQuery_writesWithin_internal
    workTapeCount controller regs

/-- Runtime interval and predecessor cursors install exactly the corresponding
guessed provider root while preserving all candidate parameters. -/
theorem buildProviderRoot_runs
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (store : Store)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hstoreGuess : store controller.guess = code.val)
    (hstoreInterval : store controller.success = interval.val)
    (hstoreChild : store controller.verdict = child.val)
    (hparameters :
      Representation.Parameters regs instanceData store) :
    ∃ final,
      Runs
        (buildProviderRoot workTapeCount controller regs)
        store final ∧
      Representation.Parameters regs instanceData final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (providerRoot instanceData interval child) :=
  Internal.buildProviderRoot_runs_internal
    controller regs instanceData code interval child store
    hguess hstoreGuess hstoreInterval hstoreChild hparameters

/-- Building a streamed provider root and clearing the catalytic bank yields
the exact singleton scheduler query for that predecessor coordinate. -/
theorem initializeProviderQuery_runs
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (store : Store)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hstoreGuess : store controller.guess = code.val)
    (hstoreInterval : store controller.success = interval.val)
    (hstoreChild : store controller.verdict = child.val)
    (hparameters :
      Representation.Parameters regs instanceData store) :
    ∃ final,
      Runs
        (initializeProviderQuery workTapeCount controller regs)
        store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.Decision.queryInitial
          (providerRoot instanceData interval child))
        final :=
  Internal.initializeProviderQuery_runs_internal
    controller regs instanceData code interval child store
    hguess hstoreGuess hstoreInterval hstoreChild hparameters

/-- Provider-query initialization also preserves the complete outer input
frame, immutable controller ABI, and the two streamed consistency cursors. -/
theorem initializeProviderQuery_runs_preserving_abi
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (store : Store)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hstoreGuess : store controller.guess = code.val)
    (hstoreInterval : store controller.success = interval.val)
    (hstoreChild : store controller.verdict = child.val)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs
        (initializeProviderQuery workTapeCount controller regs)
        store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.Decision.queryInitial
          (providerRoot instanceData interval child))
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = code.val ∧
      final controller.success = interval.val ∧
      final controller.verdict = child.val :=
  Internal.initializeProviderQuery_runs_preserving_abi_internal
    controller regs instanceData code interval child store
    hguess hstoreGuess hstoreInterval hstoreChild hparameters
    hframe hinputLength hone

end ProviderRootInitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
