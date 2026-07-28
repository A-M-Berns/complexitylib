/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderVectorSemantics.Defs

/-!
# Correctness internals for fixed consistency-provider vectors
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ProviderVectorSemantics
namespace Internal

open NeighborhoodExecutableEvaluation
open NeighborhoodGraph
open NeighborhoodGraph.Guess

theorem collectVector_eq_some_iff_internal
    (entries : Fin count → Option α)
    (vector : Fin count → α) :
    collectVector? entries = some vector ↔
      ∀ index, entries index = some (vector index) := by
  unfold collectVector?
  split <;> rename_i havailable
  · constructor
    · intro hresult index
      have hvector :
          (fun index => (entries index).get (havailable index)) =
            vector :=
        Option.some.inj hresult
      rw [← hvector]
      exact Option.eq_some_of_isSome (havailable index)
    · intro hentries
      congr 1
      funext index
      exact Option.get_of_eq_some
        (havailable index) (hentries index)
  · constructor
    · intro hresult
      contradiction
    · intro hentries
      exfalso
      apply havailable
      intro index
      simp [hentries index]

theorem queryContent_eq_inputAt_internal
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount)) :
    queryContent? tm instanceData interval child =
      EvaluatedProvider.inputAt?
        (NeighborhoodTrialInstance.schedulerNodeCallback tm instanceData)
        instanceData.guess interval
        ((predecessorIndexEquiv workTapeCount).symm child) := by
  simp [queryContent?, ProviderRootInitialization.providerRoot,
    NeighborhoodEvaluator.childAt, EvaluatedProvider.inputAt?,
    CenterGuess.predecessorAt?,
    NeighborhoodTrialInstance.schedulerNodeCallback]
  generalize
    instanceData.guess.predecessor? interval
      ((predecessorIndexEquiv workTapeCount).symm child) = predecessor
  cases predecessor <;> rfl

theorem providerVector_eq_some_iff_internal
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (vector : ProviderVector tm instanceData) :
    providerVector? tm instanceData interval = some vector ↔
      ∀ child,
        queryContent? tm instanceData interval child =
          some (vector child) := by
  unfold providerVector?
  exact collectVector_eq_some_iff_internal
    (queryContent? tm instanceData interval) vector

theorem providerInputs_eq_schedulerProvider_at_internal
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon) :
    providerInputs? tm instanceData interval =
      schedulerProvider tm instanceData
        instanceData.guess interval := by
  have havailable :
      (∀ child : Fin (graphFanIn workTapeCount),
        (queryContent? tm instanceData interval child).isSome = true) ↔
      (∀ index : PredecessorIndex workTapeCount,
        (EvaluatedProvider.inputAt?
          (NeighborhoodTrialInstance.schedulerNodeCallback
            tm instanceData)
          instanceData.guess interval index).isSome = true) := by
    constructor
    · intro hchild index
      have h :=
        hchild (predecessorIndexEquiv workTapeCount index)
      rw [queryContent_eq_inputAt_internal] at h
      simpa using h
    · intro hindex child
      have h :=
        hindex ((predecessorIndexEquiv workTapeCount).symm child)
      rw [← queryContent_eq_inputAt_internal] at h
      exact h
  unfold providerInputs? providerVector? collectVector?
    schedulerProvider EvaluatedProvider.provider
  split <;> rename_i hchild
  · simp only [dif_pos (havailable.mp hchild)]
    simp only [Option.map_some]
    congr 1
    funext index
    simp only [vectorInputs]
    apply Option.get_congr
    simpa using
      queryContent_eq_inputAt_internal
        tm instanceData interval
          (predecessorIndexEquiv workTapeCount index)
  · simp only [dif_neg ((not_congr havailable).mp hchild)]
    rfl

theorem providerInputs_eq_schedulerProvider_internal
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    (fun interval => providerInputs? tm instanceData interval) =
      schedulerProvider tm instanceData instanceData.guess := by
  funext interval
  exact providerInputs_eq_schedulerProvider_at_internal
    tm instanceData interval

theorem boundaryCheck_eq_vectorBoundaryCheck_internal
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon) :
    Consistency.boundaryCheck
        tm instanceData.blockLength
        (schedulerProvider tm instanceData)
        instanceData.guess interval =
      vectorBoundaryCheck tm instanceData interval := by
  rw [Consistency.boundaryCheck]
  rw [← providerInputs_eq_schedulerProvider_at_internal
    tm instanceData interval]
  unfold providerInputs? vectorBoundaryCheck
  cases providerVector? tm instanceData interval <;> simp

end Internal
end ProviderVectorSemantics
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
