/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Streaming enumeration of center-movement guesses

A center guess contains one three-valued movement for each interval and
named tape. This file gives an explicit base-three enumeration of those
movement arrays. Candidate code `c` is decoded in little-endian order; no
semantic trajectory or source running time occurs in the decoder.

The initial centers are fixed to zero. This loses no genuine source run:
every input, work, and output head starts at position zero.

## Main definitions

- `movementCount` -- number of movement trits
- `movementIndex` -- row-major interval/tape index
- `candidateGuess` -- decode one bounded ternary counter
- `encodeMovement` -- proof-side inverse used for completeness
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace Guess

namespace Enumeration

/-- Number of interval/tape movement trits in one guess. -/
def movementCount (workTapeCount horizon : ℕ) : ℕ :=
  horizon * (workTapeCount + 2)

/-- Row-major index of one interval/tape movement. -/
def movementIndex (interval : Fin horizon)
    (tape : TapeIndex workTapeCount) :
    Fin (movementCount workTapeCount horizon) :=
  finProdFinEquiv (interval, tape)

/-- Ternary digit assigned to one center movement. -/
def moveToDigit : CenterMove → ℕ
  | .left => 0
  | .stay => 1
  | .right => 2

/-- Decode a ternary digit, defaulting out-of-range values to `right`.
Candidate codes below the advertised bound only produce digits below three. -/
def moveOfDigit : ℕ → CenterMove
  | 0 => .left
  | 1 => .stay
  | _ => .right

/-- Fixed-length ternary digits of a bounded candidate counter. -/
def candidateDigits
    (code : Fin (3 ^ movementCount workTapeCount horizon)) : List ℕ :=
  Nat.digitsAppend 3 (movementCount workTapeCount horizon) code.val

/-- Decode one bounded ternary counter as a center guess.

The entire movement word occupies exactly `movementCount` trits. A concrete
machine may either retain that word or recompute a digit from the counter;
both representations fit the same linear movement budget. -/
def candidateGuess
    (code : Fin (3 ^ movementCount workTapeCount horizon)) :
    CenterGuess workTapeCount horizon where
  initialCenter := fun _ => 0
  movement := fun interval tape =>
    moveOfDigit
      ((candidateDigits code).getD
        (movementIndex interval tape).val 0)

/-- Row-major ternary word of an arbitrary movement array. -/
def movementDigitAt
    (guess : CenterGuess workTapeCount horizon)
    (index : Fin (movementCount workTapeCount horizon)) : ℕ :=
  let checkpoint := finProdFinEquiv.symm index
  moveToDigit (guess.movement checkpoint.1 checkpoint.2)

/-- Row-major ternary word of an arbitrary movement array. -/
def movementDigits
    (guess : CenterGuess workTapeCount horizon) : List ℕ :=
  List.ofFn (movementDigitAt guess)

/-- Encode a movement array as a natural number in base three. -/
def encodeMovement
    (guess : CenterGuess workTapeCount horizon) : ℕ :=
  Nat.ofDigits 3 (movementDigits guess)

/-- The bounded ternary code of an arbitrary movement array. -/
def encodeMovementCode
    (guess : CenterGuess workTapeCount horizon) :
    Fin (3 ^ movementCount workTapeCount horizon) :=
  ⟨encodeMovement guess, by
    have hdigits :
        ∀ digit ∈ movementDigits guess, digit < 3 := by
      intro digit hdigit
      rw [movementDigits, List.mem_ofFn] at hdigit
      obtain ⟨index, rfl⟩ := hdigit
      change moveToDigit
        (guess.movement
          (finProdFinEquiv.symm index).1
          (finProdFinEquiv.symm index).2) < 3
      generalize guess.movement
        (finProdFinEquiv.symm index).1
        (finProdFinEquiv.symm index).2 = move
      cases move <;> decide
    simpa [encodeMovement, movementDigits] using
      (Nat.ofDigits_lt_base_pow_length (b := 3)
        (by omega) hdigits)⟩

end Enumeration

end Guess

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
