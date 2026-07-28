/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Search.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Search.Internal

/-!
# Executable search over center-movement guesses

The scan is complete because the true movement word occurs in the explicit
ternary enumeration and passes the local checker. Every returned candidate is
sound under the provider's exact-prefix contract.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace Guess

namespace Search

open Consistency Enumeration

/-- Any code returned by a bounded scan is accepted. -/
theorem firstAccepted_sound
    (accept : Fin bound → Bool) {code : Fin bound}
    (hscan : firstAccepted bound accept = some code) :
    accept code = true :=
  Internal.firstAccepted_sound_internal accept hscan

/-- A bounded scan returns some code whenever an accepted code exists. -/
theorem firstAccepted_complete
    (accept : Fin bound → Bool) (target : Fin bound)
    (haccept : accept target = true) :
    (firstAccepted bound accept).isSome :=
  Internal.firstAccepted_complete_internal accept target haccept

/-- Every movement code returned by the finite local search passes. -/
theorem firstPassingCode_sound
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (provider : InputProvider tm blockLength horizon)
    {code : Fin (guessCount workTapeCount horizon)}
    (hscan :
      firstPassingCode tm x blockLength provider = some code) :
    Passes tm x blockLength provider
      (candidateGuess
        (Fin.cast (by simp [guessCount]) code)) :=
  Internal.firstPassingCode_sound_internal
    tm x blockLength provider hscan

/-- Exact local predecessor evaluation guarantees that the bounded movement
search terminates successfully. -/
theorem firstPassingCode_complete
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) (hpositive : 0 < blockLength)
    (provider : InputProvider tm blockLength horizon)
    (hexact : IsExactProvider
      tm x blockLength hpositive provider) :
    (firstPassingCode tm x blockLength provider).isSome :=
  Internal.firstPassingCode_complete_internal
    tm x blockLength horizon hpositive provider hexact

/-- Every code returned by the bounded local search yields the actual center
trajectory. -/
theorem firstPassingCode_valid
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
        (actualCenterTrajectory tm x blockLength) :=
  Internal.firstPassingCode_valid_internal
    tm x blockLength horizon hpositive provider hexact hscan

end Search

end Guess

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
