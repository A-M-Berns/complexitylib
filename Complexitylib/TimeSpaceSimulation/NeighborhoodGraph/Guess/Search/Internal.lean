/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Consistency
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Enumeration
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Search.Defs

/-!
# Correctness internals for executable center-guess search
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace Guess

namespace Search

open Consistency Enumeration

namespace Internal

theorem scanFrom_sound_internal
    (accept : Fin bound → Bool) {fuel current : ℕ}
    {accepted : Fin bound}
    (hscan : scanFrom bound accept fuel current = some accepted) :
    accept accepted = true := by
  induction fuel generalizing current with
  | zero =>
      simp [scanFrom] at hscan
  | succ fuel ih =>
      rw [scanFrom] at hscan
      split at hscan <;> rename_i hcurrent
      · dsimp only at hscan
        split at hscan <;> rename_i haccept
        · have heq : (⟨current, hcurrent⟩ : Fin bound) =
              accepted := by
            simpa only [Option.some.injEq] using hscan
          simpa [← heq] using haccept
        · exact ih hscan
      · simp at hscan

theorem scanFrom_complete_internal
    (accept : Fin bound → Bool) {fuel current : ℕ}
    (target : Fin bound) (hcurrent : current ≤ target.val)
    (hrange : target.val < current + fuel)
    (haccept : accept target = true) :
    (scanFrom bound accept fuel current).isSome := by
  induction fuel generalizing current with
  | zero => omega
  | succ fuel ih =>
      rw [scanFrom]
      have hwithin : current < bound :=
        lt_of_le_of_lt hcurrent target.isLt
      simp only [hwithin, dite_true]
      by_cases hhere : accept ⟨current, hwithin⟩ = true
      · simp [hhere]
      · simp only [hhere]
        have hneq : current ≠ target.val := by
          intro heq
          have hfin : (⟨current, hwithin⟩ : Fin bound) =
              target := Fin.ext heq
          rw [hfin] at hhere
          exact hhere haccept
        apply ih
        · omega
        · omega

theorem firstAccepted_sound_internal
    (accept : Fin bound → Bool) {code : Fin bound}
    (hscan : firstAccepted bound accept = some code) :
    accept code = true :=
  scanFrom_sound_internal accept hscan

theorem firstAccepted_complete_internal
    (accept : Fin bound → Bool) (target : Fin bound)
    (haccept : accept target = true) :
    (firstAccepted bound accept).isSome := by
  apply scanFrom_complete_internal accept target
  · omega
  · simp
  · exact haccept

theorem firstPassingCode_sound_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (provider : InputProvider tm blockLength horizon)
    {code : Fin (guessCount workTapeCount horizon)}
    (hscan :
      firstPassingCode tm x blockLength provider = some code) :
    Passes tm x blockLength provider
      (candidateGuess
        (Fin.cast (by simp [guessCount]) code)) := by
  exact firstAccepted_sound_internal _ hscan

theorem firstPassingCode_complete_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) (hpositive : 0 < blockLength)
    (provider : InputProvider tm blockLength horizon)
    (hexact : IsExactProvider
      tm x blockLength hpositive provider) :
    (firstPassingCode tm x blockLength provider).isSome := by
  let actual :=
    actualCenterGuess tm x blockLength horizon
  let target :
      Fin (guessCount workTapeCount horizon) :=
    Fin.cast (by simp [guessCount])
      (encodeMovementCode actual)
  apply firstAccepted_complete_internal _ target
  change passes tm x blockLength provider
      (candidateGuess
        (Fin.cast (by simp [guessCount]) target)) = true
  have hcandidate :
      candidateGuess
          (Fin.cast (by simp [guessCount]) target) =
        actual := by
    simpa [target, actual] using
      candidateGuess_encodeMovement actual
        (actualCenterGuess_initialCenter
          tm x blockLength horizon)
  rw [hcandidate]
  exact actualCenterGuess_passes
    tm x blockLength horizon hpositive provider hexact

theorem firstPassingCode_valid_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) (hpositive : 0 < blockLength)
    (provider : InputProvider tm blockLength horizon)
    (hexact : IsExactProvider
      tm x blockLength hpositive provider)
    {code : Fin (guessCount workTapeCount horizon)}
    (hscan :
      firstPassingCode tm x blockLength provider = some code) :
    (candidateGuess
      (Fin.cast (by simp [guessCount]) code :
        Fin (3 ^ movementCount workTapeCount horizon))).IsValidFor
        (actualCenterTrajectory tm x blockLength) := by
  apply passes_implies_valid
    tm x blockLength horizon hpositive provider hexact
  exact firstPassingCode_sound_internal
    tm x blockLength provider hscan

end Internal

end Search

end Guess

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
