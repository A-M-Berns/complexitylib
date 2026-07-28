/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderVectorCollection.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderVectorCollection.Internal

/-!
# Uniform packed collection of consistency-provider vectors
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ProviderVectorCollection

open RAM Structured
open NeighborhoodExecutableEvaluation

/-- Complete vector collection writes only in the shared trial footprint. -/
theorem collect_writesWithin
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (hcombine :
      Footprint.CmdWritesWithin regs.layout.footprint combine) :
    Footprint.CmdWritesWithin regs.footprint
      (collect tm order controller regs combine) :=
  Internal.collect_writesWithin_internal
    tm order controller regs combine hcombine

/-- The fixed command evaluates every role-major provider coordinate, packs
all result residues into `controller.hasNext`, and leaves the cursor at the
one-past-the-end fan-in value while preserving the outer ABI. -/
theorem collect_runs
    {tm : TM workTapeCount}
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (interval : Fin instanceData.horizon)
    (store : Store)
    (hcombineWrites :
      Footprint.CmdWritesWithin regs.layout.footprint combine)
    (hcombine : SchedulerStep.CombineSpec tm order regs combine)
    (hencoding :
      instanceData.encoding =
        FiniteEncoding.ofStateOrder order instanceData.blockLength)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hstoreGuess : store controller.guess = code.val)
    (hstoreInterval : store controller.success = interval.val)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (collect tm order controller regs combine) store final ∧
      Representation.Parameters regs instanceData final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = code.val ∧
      final controller.success = interval.val ∧
      final controller.verdict = graphFanIn workTapeCount ∧
      final controller.hasNext =
        collectedWord
          (Representation.fieldBase instanceData)
          (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (payloadWidth tm instanceData.blockLength)
            (graphFanIn workTapeCount))
          (fun child =>
            providerResidue tm instanceData interval child) ∧
      ∀ child chunk,
        PackedDigits.digit
            (Representation.fieldBase instanceData)
            (final controller.hasNext)
            (providerCoordinate
              (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                (payloadWidth tm instanceData.blockLength)
                (graphFanIn workTapeCount))
              child.val chunk.val) =
          ProviderResultDecoding.resultResidues
            tm instanceData interval child chunk :=
  Internal.collect_runs_internal
    order controller regs combine instanceData code interval store
    hcombineWrites hcombine hencoding hguess hstoreGuess
    hstoreInterval hparameters hframe hinputLength hone

/-- Exact equality of every packed collected residue identifies the decoded
collection with the vector of pure scheduler results. -/
theorem decodedCollectedVector_eq_results
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (store : Store)
    (hresidues :
      ∀ child chunk,
        PackedDigits.digit
            (Representation.fieldBase instanceData)
            (store controller.hasNext)
            (providerCoordinate
              (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                (payloadWidth tm instanceData.blockLength)
                (graphFanIn workTapeCount))
              child.val chunk.val) =
          ProviderResultDecoding.resultResidues
            tm instanceData interval child chunk) :
    decodedCollectedVector tm controller instanceData store =
      fun child =>
        ProviderResultDecoding.decodedResult
          tm instanceData interval child :=
  Internal.decodedCollectedVector_eq_results_internal
    tm controller instanceData interval store hresidues

/-- On a correct center prefix, the decoded collection is extensionally the
abstract predecessor-content vector for the selected interval. -/
theorem decodedCollectedVector_eq_expected
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (store : Store)
    (hresidues :
      ∀ child chunk,
        PackedDigits.digit
            (Representation.fieldBase instanceData)
            (store controller.hasNext)
            (providerCoordinate
              (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                (payloadWidth tm instanceData.blockLength)
                (graphFanIn workTapeCount))
              child.val chunk.val) =
          ProviderResultDecoding.resultResidues
            tm instanceData interval child chunk)
    (hprefix :
      ∀ boundary : Fin (instanceData.horizon + 1),
        boundary.val ≤ interval.val →
          ∀ tape : TapeIndex workTapeCount,
            instanceData.guess.derivedCenter tape boundary.val =
              some (NeighborhoodGraph.Guess.actualCenterTrajectory
                tm instanceData.x instanceData.blockLength
                  tape boundary.val)) :
    decodedCollectedVector tm controller instanceData store =
      fun child =>
        ProviderResultDecoding.expectedContent
          tm instanceData interval child :=
  Internal.decodedCollectedVector_eq_expected_internal
    tm controller instanceData interval store hresidues hprefix

/-- On a correct center prefix, the vector consumed by the abstract boundary
checker is exactly the decoded packed collection. -/
theorem providerVector_eq_some_decodedCollectedVector
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (store : Store)
    (hresidues :
      ∀ child chunk,
        PackedDigits.digit
            (Representation.fieldBase instanceData)
            (store controller.hasNext)
            (providerCoordinate
              (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
                (payloadWidth tm instanceData.blockLength)
                (graphFanIn workTapeCount))
              child.val chunk.val) =
          ProviderResultDecoding.resultResidues
            tm instanceData interval child chunk)
    (hprefix :
      ∀ boundary : Fin (instanceData.horizon + 1),
        boundary.val ≤ interval.val →
          ∀ tape : TapeIndex workTapeCount,
            instanceData.guess.derivedCenter tape boundary.val =
              some (NeighborhoodGraph.Guess.actualCenterTrajectory
                tm instanceData.x instanceData.blockLength
                  tape boundary.val)) :
    ProviderVectorSemantics.providerVector?
        tm instanceData interval =
      some
        (decodedCollectedVector
          tm controller instanceData store) :=
  Internal.providerVector_eq_some_decodedCollectedVector_internal
    tm controller instanceData interval store hresidues hprefix

end ProviderVectorCollection
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
