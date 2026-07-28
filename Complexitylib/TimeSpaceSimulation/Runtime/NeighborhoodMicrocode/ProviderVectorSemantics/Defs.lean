/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderRootInit.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodTrialInstance.Defs

/-!
# Fixed provider vectors for streamed consistency checking

One interval boundary consumes exactly one compact predecessor value for each
role-major coordinate. This module exposes that fixed `Fin`-indexed vector,
its per-coordinate scheduler query, and the Boolean boundary check obtained
from it. The definitions are pure and retain the exact cursor order used by
the uniform provider-query loop.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ProviderVectorSemantics

open NeighborhoodExecutableEvaluation
open NeighborhoodGraph
open NeighborhoodGraph.Guess

variable {workTapeCount : ℕ}
variable {tm : TM workTapeCount}

/-- Compact contents returned by one scheduler-backed provider query. -/
abbrev Content
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :=
  NeighborhoodContent.Content instanceData.blockLength tm.Q

/-- Fixed role-major predecessor vector consumed by one boundary check. -/
abbrev ProviderVector
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :=
  Fin (graphFanIn workTapeCount) → Content tm instanceData

/-- Collect a fixed family of optional coordinates, failing if any coordinate
is unavailable. -/
def collectVector?
    (entries : Fin count → Option α) :
    Option (Fin count → α) :=
  if havailable :
      ∀ index, (entries index).isSome = true then
    some fun index => (entries index).get (havailable index)
  else
    none

/-- Evaluate the provider root selected by one interval and role-major
coordinate using the concrete scheduler-backed node evaluator. -/
def queryContent?
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount)) :
    Option (Content tm instanceData) :=
  match
      ProviderRootInitialization.providerRoot
        instanceData interval child with
  | .failure => none
  | .graph node =>
      NeighborhoodTrialInstance.schedulerNodeContent
        tm instanceData node

/-- Assemble all provider queries in their fixed role-major cursor order. -/
def providerVector?
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon) :
    Option (ProviderVector tm instanceData) :=
  collectVector? (queryContent? tm instanceData interval)

/-- Reindex the fixed runtime vector by the typed predecessor-role API. -/
def vectorInputs
    (vector : ProviderVector tm instanceData) :
    PredecessorIndex workTapeCount → Content tm instanceData :=
  fun index =>
    vector (predecessorIndexEquiv workTapeCount index)

/-- The exact consistency provider backed by concrete scheduler node
queries. -/
def schedulerProvider
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    Consistency.InputProvider
      tm instanceData.blockLength instanceData.horizon :=
  EvaluatedProvider.provider
    (NeighborhoodTrialInstance.schedulerNodeCallback tm instanceData)

/-- Optional typed consistency input obtained from the fixed runtime vector. -/
def providerInputs?
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon) :
    Option
      (PredecessorIndex workTapeCount → Content tm instanceData) :=
  (providerVector? tm instanceData interval).map vectorInputs

/-- One interval-boundary check expressed directly through the fixed
role-major provider vector. -/
def vectorBoundaryCheck
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon) : Bool :=
  match providerVector? tm instanceData interval with
  | none => false
  | some vector =>
      (List.finRange (workTapeCount + 2)).all fun tape =>
        instanceData.guess.derivedCenter tape (interval.val + 1) ==
          some
            (Consistency.localEndCenter
              tm instanceData.blockLength
              (Consistency.guessedCenters
                instanceData.guess interval.val)
              (vectorInputs vector) tape)

end ProviderVectorSemantics
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
