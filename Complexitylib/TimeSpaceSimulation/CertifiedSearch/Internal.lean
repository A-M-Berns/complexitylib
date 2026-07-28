/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.CandidateSearch
import Complexitylib.TimeSpaceSimulation.CertifiedSearch.Defs
import Complexitylib.TimeSpaceSimulation.CertifiedTrial
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.WorkspaceAccounting

/-!
# Correctness internals for certified streamed candidate search
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace CertifiedSearch

open NeighborhoodGraph


namespace Internal

theorem candidate_le_horizon_start_internal (candidate : ℕ) :
    candidate ≤ timeBlockStart
      (WorkspaceAccounting.blockLength candidate)
      (WorkspaceAccounting.horizon candidate) := by
  have hcover := le_smul_ceilDiv (α := ℕ) (β := ℕ)
    (a := WorkspaceAccounting.blockLength candidate) (b := candidate)
    (WorkspaceAccounting.blockLength_pos candidate)
  simpa [WorkspaceAccounting.horizon, timeBlockStart, nsmul_eq_mul,
    Nat.mul_comm] using hcover

theorem trial_sound_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : EngineFamily tm) (x : List Bool)
    (candidate : ℕ) {answer : Bool}
    (hrun : trial tm family x candidate = some answer) :
    (answer = true → x ∈ L) ∧
      (answer = false → x ∉ L) := by
  exact CertifiedTrial.run_sound tm L actualTime hdecides x
    (WorkspaceAccounting.blockLength candidate)
    (WorkspaceAccounting.horizon candidate)
    (WorkspaceAccounting.blockLength_pos candidate)
    (family.engine x candidate)
    (family.exact x candidate) hrun

theorem trial_complete_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : EngineFamily tm) (x : List Bool)
    (candidate : ℕ)
    (hcover : actualTime x.length ≤ candidate) :
    (trial tm family x candidate).isSome := by
  exact CertifiedTrial.run_complete tm L actualTime hdecides x
    (WorkspaceAccounting.blockLength candidate)
    (WorkspaceAccounting.horizon candidate)
    (WorkspaceAccounting.blockLength_pos candidate)
    (hcover.trans (candidate_le_horizon_start_internal candidate))
    (family.engine x candidate)
    (family.exact x candidate)

theorem runThrough_sound_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : EngineFamily tm) (x : List Bool)
    (endpoint found : ℕ) {answer : Bool}
    (hrun :
      runThrough tm family x endpoint = some (found, answer)) :
    (answer = true → x ∈ L) ∧
      (answer = false → x ∉ L) := by
  apply trial_sound_internal tm L actualTime hdecides
    family x found
  exact CandidateSearch.searchThrough_sound
    (trial tm family x) hrun

theorem runThrough_complete_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : EngineFamily tm) (x : List Bool)
    (endpoint : ℕ)
    (hinput : x.length ≤ endpoint)
    (htime : actualTime x.length ≤ endpoint) :
    (runThrough tm family x endpoint).isSome := by
  have htrial :=
    trial_complete_internal tm L actualTime hdecides
      family x endpoint htime
  obtain ⟨answer, hanswer⟩ :=
    Option.isSome_iff_exists.mp htrial
  exact CandidateSearch.searchThrough_complete
    (trial tm family x) hinput hanswer

theorem runThrough_max_complete_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : EngineFamily tm) (x : List Bool) :
    (runThrough tm family x
      (max x.length (actualTime x.length))).isSome := by
  apply runThrough_complete_internal
    tm L actualTime hdecides family x
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem workspaceThrough_le_internal
    (tm : TM workTapeCount) (x : List Bool)
    (endpoint : ℕ) :
    workspaceThrough tm x endpoint ≤
      WorkspaceAccounting.trialEnvelopeBits tm.Q workTapeCount endpoint := by
  apply CandidateSearch.streamedWorkspace_le
  intro candidate _hlower hupper
  exact WorkspaceAccounting.totalBits_le_trialEnvelope
    tm.Q workTapeCount hupper

theorem workspaceThrough_max_le_internal
    (tm : TM workTapeCount) (x : List Bool)
    (haltTime : ℕ) :
    workspaceThrough tm x (max x.length haltTime) ≤
      WorkspaceAccounting.trialEnvelopeBits tm.Q workTapeCount
        (max x.length haltTime) :=
  workspaceThrough_le_internal tm x _

end Internal

end CertifiedSearch

end TimeSpaceSimulation

end Complexity
