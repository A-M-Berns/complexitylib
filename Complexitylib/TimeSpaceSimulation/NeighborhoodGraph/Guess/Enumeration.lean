/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Enumeration.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Enumeration.Internal

/-!
# Streaming enumeration of center-movement guesses

The runtime candidates are the bounded ternary counters below
`3 ^ (horizon * (workTapeCount + 2))`. Decoding fixes every initial center to
zero and assigns one trit to each interval/tape movement. The true source-run
guess is proved to occur in this enumeration.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace Guess

namespace Enumeration

/-- Ternary movement decoding is a left inverse of movement encoding. -/
theorem moveOfDigit_moveToDigit (move : CenterMove) :
    moveOfDigit (moveToDigit move) = move :=
  Internal.ofDigit_toDigit_internal move

/-- Every movement encoding is a genuine ternary digit. -/
theorem moveToDigit_lt (move : CenterMove) :
    moveToDigit move < 3 :=
  Internal.toDigit_lt_internal move

/-- The proof-side movement word has exactly the runtime guess length. -/
theorem movementDigits_length
    (guess : CenterGuess workTapeCount horizon) :
    (movementDigits guess).length =
      movementCount workTapeCount horizon :=
  Internal.movementDigits_length_internal guess

/-- Every proof-side movement digit is below three. -/
theorem movementDigits_digit_lt
    (guess : CenterGuess workTapeCount horizon)
    {digit : ℕ} (hdigit : digit ∈ movementDigits guess) :
    digit < 3 :=
  Internal.movementDigits_digit_lt_internal guess hdigit

/-- Fixed-length candidate decoding recovers an encoded movement word. -/
theorem candidateDigits_encodeMovement
    (guess : CenterGuess workTapeCount horizon) :
    candidateDigits (encodeMovementCode guess) =
      movementDigits guess :=
  Internal.candidateDigits_encodeMovement_internal guess

/-- Every guess whose source centers are zero occurs in the bounded ternary
enumeration. -/
theorem candidateGuess_encodeMovement
    (guess : CenterGuess workTapeCount horizon)
    (hinitial : ∀ tape, guess.initialCenter tape = 0) :
    candidateGuess (encodeMovementCode guess) = guess :=
  Internal.candidateGuess_encodeMovement_internal guess hinitial

/-- Every named source head starts in block zero. -/
theorem actualCenterGuess_initialCenter
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) (tape : TapeIndex workTapeCount) :
    (actualCenterGuess tm x blockLength horizon).initialCenter tape = 0 :=
  Internal.actualCenterGuess_initialCenter_internal
    tm x blockLength horizon tape

/-- The true center-movement guess is one of the explicitly bounded runtime
candidates. -/
theorem actualCenterGuess_enumerated
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) :
    candidateGuess
        (encodeMovementCode
          (actualCenterGuess tm x blockLength horizon)) =
      actualCenterGuess tm x blockLength horizon :=
  Internal.actualCenterGuess_enumerated_internal
    tm x blockLength horizon

end Enumeration

end Guess

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
