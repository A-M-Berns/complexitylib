/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.VerdictRootInitialization.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.VerdictRootInitialization.Internal

/-!
# Uniform initialization of the verdict-consistency root
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace VerdictRootInitialization

open RAM Structured
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

/-- The invalid-skipping backwards scan writes only its fixed predecessor
scratch. -/
theorem scanExactPrior_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin (ChildNode.priorFootprint regs)
      (scanExactPrior workTapeCount controller regs) :=
  Internal.scanExactPrior_writesWithin_internal
    workTapeCount controller regs

/-- Every successful exact search result contains the requested block. -/
theorem exactPriorSearchValue_contains
    (workTapeCount word tape requested count interval center : ℕ)
    (hresult :
      exactPriorSearchValue workTapeCount word tape requested count =
        some (interval, center)) :
    NeighborhoodGraph.NeighborhoodContains center requested :=
  Internal.exactPriorSearchValue_contains_internal
    workTapeCount word tape requested count interval center hresult

/-- For every enumerated movement word, including words with invalid later
prefixes, the exact scan result denotes the semantic latest-block root. -/
theorem exactPriorQueryValue_candidateGuess
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount horizon))
    (tape : TapeIndex workTapeCount)
    (requested : ℕ) :
    ChildNode.priorQueryValue
        (horizon := horizon) tape requested
        (some
          (exactPriorSearchValue
            workTapeCount code.val tape.val requested horizon)) =
      NeighborhoodEvaluator.latestBlockRoot
        (NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
        tape requested :=
  Internal.exactPriorQueryValue_candidateGuess_internal
    code tape requested

/-- The concrete exact scan returns the greatest valid containing prefix,
skipping rather than aborting on invalid later prefixes. -/
theorem scanExactPrior_runs
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (store : Store) (word tape requested interval : ℕ)
    (hguess : store controller.guess = word)
    (htape : store (ControlDecode.nodeTape regs) = tape)
    (hrequested :
      store (ChildNode.requestedBlock regs) = requested)
    (hinterval :
      store (ControlDecode.nodePayload1 regs) = interval) :
    ∃ final,
      Runs (scanExactPrior workTapeCount controller regs) store final ∧
      ScanExactPriorPost workTapeCount word tape requested interval
        controller regs store final :=
  Internal.scanExactPrior_runs_internal
    workTapeCount controller regs store word tape requested interval
    hguess htape hrequested hinterval

/-- Runtime field initialization selects the output tape, computes the block
containing verdict cell one from the positive runtime block length, and copies
the runtime horizon into the scan bound. -/
theorem initializeVerdictFields_runs
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
        (initializeVerdictFields workTapeCount controller regs)
        store final ∧
      final (ControlDecode.nodeTape regs) =
        (TapeIndex.output workTapeCount).val ∧
      final (ChildNode.requestedBlock regs) =
        blockIndex instanceData.blockLength 1 ∧
      final (ControlDecode.nodePayload1 regs) =
        instanceData.horizon ∧
      final controller.one = 1 ∧
      final controller.guess = store controller.guess :=
  Internal.initializeVerdictFields_runs_internal
    controller regs instanceData store hparameters hone

/-- Verdict-root construction writes only the shared predecessor-assembly
footprint. -/
theorem buildVerdictRoot_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin
      (ChildNode.priorAssemblyFootprint regs)
      (buildVerdictRoot workTapeCount controller regs) :=
  Internal.buildVerdictRoot_writesWithin_internal
    workTapeCount controller regs

/-- Verdict-root construction followed by bank-preserving query
reinitialization stays inside the evaluator layout. -/
theorem reinitializeVerdictQuery_writesWithin
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (reinitializeVerdictQuery workTapeCount controller regs) :=
  Internal.reinitializeVerdictQuery_writesWithin_internal
    workTapeCount controller regs

/-- The fixed builder reads the runtime horizon, block length, and packed
guess word and installs exactly the semantic verdict root. -/
theorem buildVerdictRoot_runs
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (store : Store)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hone : store controller.one = 1)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code) :
    ∃ final,
      Runs
        (buildVerdictRoot workTapeCount controller regs)
        store final ∧
      Representation.Parameters regs instanceData final ∧
      final (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData)
          (NeighborhoodEvaluator.verdictRoot
            instanceData.guess instanceData.blockLength) ∧
      final controller.one = 1 ∧
      final controller.guess = code.val ∧
      ∀ address,
        address ∉ ChildNode.priorAssemblyFootprint regs →
          final address = store address :=
  Internal.buildVerdictRoot_runs_internal
    controller regs instanceData code store
    hparameters hone hstoreGuess hguess

/-- Exact verdict-root construction replaces the old stack while retaining
the complete logical catalytic bank and choosing output coordinate zero. -/
theorem reinitializeVerdictQuery_runs
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (state : NeighborhoodScheduler.State tm instanceData)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (store : Store)
    (hquery :
      Representation.QueryState regs instanceData state store)
    (hone : store controller.one = 1)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code) :
    ∃ final,
      Runs
        (reinitializeVerdictQuery workTapeCount controller regs)
        store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.initial
          instanceData.horizon
          (NeighborhoodEvaluator.verdictRoot
            instanceData.guess instanceData.blockLength)
          1 (verdictOut workTapeCount) state.registers)
        final ∧
      final controller.one = 1 :=
  Internal.reinitializeVerdictQuery_runs_internal
    controller regs instanceData state code store hquery
    hone hstoreGuess hguess

/-- Verdict-query reinitialization preserves the public input frame and all
read-only controller values required by the uniform scheduler loop. -/
theorem reinitializeVerdictQuery_runs_preserving_abi
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (state : NeighborhoodScheduler.State tm instanceData)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (store : Store)
    (hquery :
      Representation.QueryState regs instanceData state store)
    (hone : store controller.one = 1)
    (hstoreGuess : store controller.guess = code.val)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length) :
    ∃ final,
      Runs
        (reinitializeVerdictQuery workTapeCount controller regs)
        store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.State.initial
          instanceData.horizon
          (NeighborhoodEvaluator.verdictRoot
            instanceData.guess instanceData.blockLength)
          1 (verdictOut workTapeCount) state.registers)
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = code.val :=
  Internal.reinitializeVerdictQuery_runs_preserving_abi_internal
    controller regs instanceData state code store hquery
    hone hstoreGuess hguess hframe hinputLength

end VerdictRootInitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
