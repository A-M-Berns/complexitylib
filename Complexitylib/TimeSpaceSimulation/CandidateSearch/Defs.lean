/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Data.Nat.Basic

/-!
# Streamed candidate-time search

Williams's simulation does not require a time-constructible source bound.
Instead, a fixed simulator tests ordinary candidate times in increasing
order. This module isolates that executable control loop.

`trial candidate = none` means that the candidate did not yet produce a
locally certified halted snapshot. `some verdict` is a certified Boolean
decision. The loop stores only its current counter and reuses all trial
workspace.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace CandidateSearch

/-- Number of candidates in the inclusive interval `[start, endpoint]`. -/
def intervalLength (start endpoint : ℕ) : ℕ :=
  if start ≤ endpoint then endpoint - start + 1 else 0

/-- Tail-recursive search over at most `fuel` consecutive candidate times. -/
def scanTrials (trial : ℕ → Option Bool) :
    ℕ → ℕ → Option (ℕ × Bool)
  | 0, _ => none
  | fuel + 1, current =>
      match trial current with
      | some verdict => some (current, verdict)
      | none => scanTrials trial fuel (current + 1)

/-- Search every candidate from `start` through `endpoint`, inclusive.
When `endpoint < start`, the search has zero fuel. -/
def searchThrough (trial : ℕ → Option Bool)
    (start endpoint : ℕ) : Option (ℕ × Bool) :=
  scanTrials trial (intervalLength start endpoint) start

/-- Maximum workspace among `fuel` consecutive candidate trials. -/
def workspaceFrom (trialSpace : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, current =>
      max (trialSpace current)
        (workspaceFrom trialSpace fuel (current + 1))

/-- Peak trial storage in a finite streamed prefix. The `max` expresses
sequential reuse rather than summing trial workspaces. -/
def streamedWorkspace (trialSpace : ℕ → ℕ)
    (start endpoint : ℕ) : ℕ :=
  workspaceFrom trialSpace (intervalLength start endpoint) start

end CandidateSearch

end TimeSpaceSimulation

end Complexity
