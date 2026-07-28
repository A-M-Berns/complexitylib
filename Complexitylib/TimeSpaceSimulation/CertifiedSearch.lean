/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.CertifiedSearch.Defs
import Complexitylib.TimeSpaceSimulation.CertifiedSearch.Internal
import Complexitylib.TimeSpaceSimulation.CertifiedSearch.Asymptotics

/-!
# Certified streamed search over candidate times

An exact executable engine family yields a sound finite search at every
endpoint.  The search is guaranteed to succeed by
`max |x| (actualTime |x|)`, although that proof-level endpoint is not supplied
to an individual trial.  Sequential trials reuse one common workspace.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace CertifiedSearch

open NeighborhoodGraph

/-- The least balanced interval horizon covers its candidate time. -/
theorem candidate_le_horizon_start (candidate : ℕ) :
    candidate ≤ timeBlockStart
      (WorkspaceAccounting.blockLength candidate)
      (WorkspaceAccounting.horizon candidate) :=
  Internal.candidate_le_horizon_start_internal candidate

/-- Every Boolean returned by one explicit trial is the source decision. -/
theorem trial_sound
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : EngineFamily tm) (x : List Bool)
    (candidate : ℕ) {answer : Bool}
    (hrun : trial tm family x candidate = some answer) :
    (answer = true → x ∈ L) ∧
      (answer = false → x ∉ L) :=
  Internal.trial_sound_internal tm L actualTime hdecides
    family x candidate hrun

/-- A candidate trial succeeds once it covers the source running time. -/
theorem trial_complete
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : EngineFamily tm) (x : List Bool)
    (candidate : ℕ)
    (hcover : actualTime x.length ≤ candidate) :
    (trial tm family x candidate).isSome :=
  Internal.trial_complete_internal tm L actualTime hdecides
    family x candidate hcover

/-- Every Boolean returned by a finite candidate search is correct. -/
theorem runThrough_sound
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : EngineFamily tm) (x : List Bool)
    (endpoint found : ℕ) {answer : Bool}
    (hrun :
      runThrough tm family x endpoint = some (found, answer)) :
    (answer = true → x ∈ L) ∧
      (answer = false → x ∉ L) :=
  Internal.runThrough_sound_internal
    tm L actualTime hdecides family x endpoint found hrun

/-- A finite search succeeds whenever its endpoint covers both its starting
input length and the source running time. -/
theorem runThrough_complete
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : EngineFamily tm) (x : List Bool)
    (endpoint : ℕ)
    (hinput : x.length ≤ endpoint)
    (htime : actualTime x.length ≤ endpoint) :
    (runThrough tm family x endpoint).isSome :=
  Internal.runThrough_complete_internal
    tm L actualTime hdecides family x endpoint hinput htime

/-- The proof-level endpoint `max |x| actualTime(|x|)` always suffices. -/
theorem runThrough_max_complete
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : EngineFamily tm) (x : List Bool) :
    (runThrough tm family x
      (max x.length (actualTime x.length))).isSome :=
  Internal.runThrough_max_complete_internal
    tm L actualTime hdecides family x

/-- Streaming every trial through an endpoint uses no more than that
endpoint's uniform trial envelope. -/
theorem workspaceThrough_le
    (tm : TM workTapeCount) (x : List Bool)
    (endpoint : ℕ) :
    workspaceThrough tm x endpoint ≤
      WorkspaceAccounting.trialEnvelopeBits tm.Q workTapeCount endpoint :=
  Internal.workspaceThrough_le_internal tm x endpoint

/-- Specialization of the streamed workspace bound to the guaranteed endpoint. -/
theorem workspaceThrough_max_le
    (tm : TM workTapeCount) (x : List Bool)
    (haltTime : ℕ) :
    workspaceThrough tm x (max x.length haltTime) ≤
      WorkspaceAccounting.trialEnvelopeBits tm.Q workTapeCount
        (max x.length haltTime) :=
  Internal.workspaceThrough_max_le_internal tm x haltTime

end CertifiedSearch

end TimeSpaceSimulation

end Complexity
