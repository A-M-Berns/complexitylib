/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.CandidateSearch.Defs
import Complexitylib.TimeSpaceSimulation.CandidateSearch.Internal

/-!
# Streamed candidate-time search

The loop is sound for every returned candidate and complete as soon as one
finite endpoint succeeds. This is the formal control-flow reason the final
simulator need not compute or query the source time-bound function.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace CandidateSearch

/-- Every returned pair is the result of its reported candidate trial. -/
theorem scanTrials_sound
    (trial : ℕ → Option Bool) {fuel current found : ℕ}
    {verdict : Bool}
    (hscan :
      scanTrials trial fuel current = some (found, verdict)) :
    trial found = some verdict :=
  Internal.scanTrials_sound_internal trial hscan

/-- Every reported candidate lies in the scanned half-open interval. -/
theorem scanTrials_range
    (trial : ℕ → Option Bool) {fuel current found : ℕ}
    {verdict : Bool}
    (hscan :
      scanTrials trial fuel current = some (found, verdict)) :
    current ≤ found ∧ found < current + fuel :=
  Internal.scanTrials_range_internal trial hscan

/-- A finite scan succeeds whenever it covers one successful candidate. -/
theorem scanTrials_complete
    (trial : ℕ → Option Bool) {fuel current target : ℕ}
    {verdict : Bool}
    (hlower : current ≤ target)
    (hupper : target < current + fuel)
    (htrial : trial target = some verdict) :
    (scanTrials trial fuel current).isSome :=
  Internal.scanTrials_complete_internal
    trial hlower hupper htrial

/-- An inclusive streamed search only returns an actual successful trial. -/
theorem searchThrough_sound
    (trial : ℕ → Option Bool) {start endpoint found : ℕ}
    {verdict : Bool}
    (hscan :
      searchThrough trial start endpoint =
        some (found, verdict)) :
    trial found = some verdict :=
  Internal.searchThrough_sound_internal trial hscan

/-- An inclusive streamed search reports a candidate in its stated range. -/
theorem searchThrough_range
    (trial : ℕ → Option Bool) {start endpoint found : ℕ}
    {verdict : Bool}
    (hscan :
      searchThrough trial start endpoint =
        some (found, verdict)) :
    start ≤ found ∧ found ≤ endpoint :=
  Internal.searchThrough_range_internal trial hscan

/-- If the endpoint trial succeeds, the inclusive streamed search from any
smaller start succeeds too. -/
theorem searchThrough_complete
    (trial : ℕ → Option Bool) {start target : ℕ}
    {verdict : Bool} (hstart : start ≤ target)
    (htrial : trial target = some verdict) :
    (searchThrough trial start target).isSome :=
  Internal.searchThrough_complete_internal
    trial hstart htrial

/-- If every trial in an inclusive prefix fits `bound`, sequentially
streaming that prefix also fits `bound`. -/
theorem streamedWorkspace_le
    (trialSpace : ℕ → ℕ) {start endpoint bound : ℕ}
    (hspace :
      ∀ candidate, start ≤ candidate → candidate ≤ endpoint →
        trialSpace candidate ≤ bound) :
    streamedWorkspace trialSpace start endpoint ≤ bound :=
  Internal.streamedWorkspace_le_internal trialSpace hspace

end CandidateSearch

end TimeSpaceSimulation

end Complexity
