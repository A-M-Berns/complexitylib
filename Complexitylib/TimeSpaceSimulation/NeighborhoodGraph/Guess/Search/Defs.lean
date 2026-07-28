/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Consistency.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Enumeration.Defs

/-!
# Executable search over center-movement guesses

The search streams a bounded ternary counter and stops at the first candidate
accepted by the local self-consistency checker. It neither constructs a list
of all guesses nor consults the source trajectory.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace Guess

namespace Search

open Consistency Enumeration

/-- Tail-recursive bounded scan starting at `current`, with at most `fuel`
candidate tests. -/
def scanFrom (bound : ℕ) (accept : Fin bound → Bool) :
    ℕ → ℕ → Option (Fin bound)
  | 0, _ => none
  | fuel + 1, current =>
      if hcurrent : current < bound then
        let code : Fin bound := ⟨current, hcurrent⟩
        if accept code then
          some code
        else
          scanFrom bound accept fuel (current + 1)
      else
        none

/-- Scan every bounded code in increasing order. -/
def firstAccepted (bound : ℕ) (accept : Fin bound → Bool) :
    Option (Fin bound) :=
  scanFrom bound accept bound 0

/-- Number of center-movement candidates for one finite horizon. -/
def guessCount (workTapeCount horizon : ℕ) : ℕ :=
  3 ^ movementCount workTapeCount horizon

/-- First center-movement code accepted by the finite local checker. -/
def firstPassingCode (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (provider : InputProvider tm blockLength horizon) :
    Option (Fin (guessCount workTapeCount horizon)) :=
  firstAccepted (guessCount workTapeCount horizon) fun code =>
    passes tm x blockLength provider
      (candidateGuess
        (Fin.cast
          (by simp [guessCount])
          code))

/-- Decode the first locally accepted movement code. -/
def firstPassingGuess (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (provider : InputProvider tm blockLength horizon) :
    Option (CenterGuess workTapeCount horizon) :=
  (firstPassingCode tm x blockLength provider).map fun code =>
    candidateGuess
      (Fin.cast
        (by simp [guessCount])
        code)

end Search

end Guess

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
