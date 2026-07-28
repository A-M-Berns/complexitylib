/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.CandidateSearch.Defs

/-!
# Correctness internals for streamed candidate-time search
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace CandidateSearch

namespace Internal

theorem scanTrials_sound_internal
    (trial : ℕ → Option Bool) {fuel current found : ℕ}
    {verdict : Bool}
    (hscan :
      scanTrials trial fuel current = some (found, verdict)) :
    trial found = some verdict := by
  induction fuel generalizing current with
  | zero =>
      simp [scanTrials] at hscan
  | succ fuel ih =>
      rw [scanTrials] at hscan
      generalize htrial : trial current = result at hscan
      cases result with
      | none =>
          exact ih hscan
      | some currentVerdict =>
          have heq :
              (current, currentVerdict) = (found, verdict) := by
            simpa using hscan
          cases heq
          exact htrial

theorem scanTrials_range_internal
    (trial : ℕ → Option Bool) {fuel current found : ℕ}
    {verdict : Bool}
    (hscan :
      scanTrials trial fuel current = some (found, verdict)) :
    current ≤ found ∧ found < current + fuel := by
  induction fuel generalizing current with
  | zero =>
      simp [scanTrials] at hscan
  | succ fuel ih =>
      rw [scanTrials] at hscan
      generalize htrial : trial current = result at hscan
      cases result with
      | none =>
          obtain ⟨hlower, hupper⟩ := ih hscan
          omega
      | some currentVerdict =>
          have heq :
              (current, currentVerdict) = (found, verdict) := by
            simpa using hscan
          cases heq
          omega

theorem scanTrials_complete_internal
    (trial : ℕ → Option Bool) {fuel current target : ℕ}
    {verdict : Bool}
    (hlower : current ≤ target)
    (hupper : target < current + fuel)
    (htrial : trial target = some verdict) :
    (scanTrials trial fuel current).isSome := by
  induction fuel generalizing current with
  | zero => omega
  | succ fuel ih =>
      rw [scanTrials]
      generalize hcurrent : trial current = result
      cases result with
      | some currentVerdict =>
          simp
      | none =>
        have hneq : current ≠ target := by
          intro heq
          subst current
          rw [htrial] at hcurrent
          cases hcurrent
        exact ih (by omega) (by omega)

theorem searchThrough_sound_internal
    (trial : ℕ → Option Bool) {start endpoint found : ℕ}
    {verdict : Bool}
    (hscan :
      searchThrough trial start endpoint =
        some (found, verdict)) :
    trial found = some verdict :=
  scanTrials_sound_internal trial hscan

theorem searchThrough_range_internal
    (trial : ℕ → Option Bool) {start endpoint found : ℕ}
    {verdict : Bool}
    (hscan :
      searchThrough trial start endpoint =
        some (found, verdict)) :
    start ≤ found ∧ found ≤ endpoint := by
  unfold searchThrough intervalLength at hscan
  by_cases horder : start ≤ endpoint
  · simp only [horder, if_true] at hscan
    have hrange := scanTrials_range_internal trial hscan
    omega
  · simp [horder, scanTrials] at hscan

theorem searchThrough_complete_internal
    (trial : ℕ → Option Bool) {start target : ℕ}
    {verdict : Bool} (hstart : start ≤ target)
    (htrial : trial target = some verdict) :
    (searchThrough trial start target).isSome := by
  unfold searchThrough intervalLength
  simp only [hstart, if_true]
  apply scanTrials_complete_internal trial
  · exact hstart
  · omega
  · exact htrial

theorem workspaceFrom_le_internal
    (trialSpace : ℕ → ℕ) {start bound : ℕ}
    {fuel : ℕ}
    (hspace : ∀ candidate,
      start ≤ candidate → candidate < start + fuel →
        trialSpace candidate ≤ bound) :
    workspaceFrom trialSpace fuel start ≤ bound := by
  induction fuel generalizing start with
  | zero => simp [workspaceFrom]
  | succ fuel ih =>
      rw [workspaceFrom]
      apply max_le
      · apply hspace start
        · omega
        · omega
      · apply ih
        intro candidate hlower hupper
        apply hspace candidate
        · omega
        · omega

theorem streamedWorkspace_le_internal
    (trialSpace : ℕ → ℕ) {start endpoint bound : ℕ}
    (hspace :
      ∀ candidate, start ≤ candidate → candidate ≤ endpoint →
        trialSpace candidate ≤ bound) :
    streamedWorkspace trialSpace start endpoint ≤ bound := by
  unfold streamedWorkspace intervalLength
  by_cases horder : start ≤ endpoint
  · simp only [horder, if_true]
    apply workspaceFrom_le_internal
    intro candidate hlower hupper
    apply hspace candidate hlower
    omega
  · simp [horder, workspaceFrom]

end Internal

end CandidateSearch

end TimeSpaceSimulation

end Complexity
