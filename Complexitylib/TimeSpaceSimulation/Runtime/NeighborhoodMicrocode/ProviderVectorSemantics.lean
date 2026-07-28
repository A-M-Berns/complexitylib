/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderVectorSemantics.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderVectorSemantics.Internal

/-!
# Fixed-vector semantics for streamed consistency providers

Each interval exposes exactly `graphFanIn = 4 * (workTapeCount + 2)`
role-major query coordinates. Their concrete scheduler results assemble into
the same optional input consumed by the abstract consistency provider, so one
boundary check can be rewritten entirely through this finite vector.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ProviderVectorSemantics

open NeighborhoodExecutableEvaluation
open NeighborhoodGraph
open NeighborhoodGraph.Guess

/-- Fixed optional-coordinate collection succeeds exactly when every streamed
coordinate equals the corresponding vector entry. -/
theorem collectVector_eq_some_iff
    (entries : Fin count → Option α)
    (vector : Fin count → α) :
    collectVector? entries = some vector ↔
      ∀ index, entries index = some (vector index) :=
  Internal.collectVector_eq_some_iff_internal entries vector

/-- One role-major runtime cursor selects exactly the corresponding input of
the scheduler-backed consistency provider. -/
theorem queryContent_eq_inputAt
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount)) :
    queryContent? tm instanceData interval child =
      EvaluatedProvider.inputAt?
        (NeighborhoodTrialInstance.schedulerNodeCallback tm instanceData)
        instanceData.guess interval
        ((predecessorIndexEquiv workTapeCount).symm child) :=
  Internal.queryContent_eq_inputAt_internal
    tm instanceData interval child

/-- A complete role-major vector is exactly the collection of all individual
scheduler-backed provider queries. -/
theorem providerVector_eq_some_iff
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (vector : ProviderVector tm instanceData) :
    providerVector? tm instanceData interval = some vector ↔
      ∀ child,
        queryContent? tm instanceData interval child =
          some (vector child) :=
  Internal.providerVector_eq_some_iff_internal
    tm instanceData interval vector

/-- At one interval, reindexing the fixed role-major vector gives exactly the
typed input returned by the scheduler-backed consistency provider. -/
theorem providerInputs_eq_schedulerProvider_at
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon) :
    providerInputs? tm instanceData interval =
      schedulerProvider tm instanceData
        instanceData.guess interval :=
  Internal.providerInputs_eq_schedulerProvider_at_internal
    tm instanceData interval

/-- For the canonical residue-instance guess, all interval vectors together
are extensionally equal to the exact scheduler-backed provider. -/
theorem providerInputs_eq_schedulerProvider
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    (fun interval => providerInputs? tm instanceData interval) =
      schedulerProvider tm instanceData instanceData.guess :=
  Internal.providerInputs_eq_schedulerProvider_internal
    tm instanceData

/-- The canonical scheduler-backed boundary check is exactly the finite
role-major vector check. -/
theorem boundaryCheck_eq_vectorBoundaryCheck
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon) :
    Consistency.boundaryCheck
        tm instanceData.blockLength
        (schedulerProvider tm instanceData)
        instanceData.guess interval =
      vectorBoundaryCheck tm instanceData interval :=
  Internal.boundaryCheck_eq_vectorBoundaryCheck_internal
    tm instanceData interval

end ProviderVectorSemantics
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
