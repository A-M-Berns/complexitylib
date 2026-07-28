/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Enumeration.Defs

/-!
# Correctness internals for center-guess enumeration
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace Guess

namespace Enumeration

namespace Internal

theorem ofDigit_toDigit_internal (move : CenterMove) :
    moveOfDigit (moveToDigit move) = move := by
  cases move <;> rfl

theorem toDigit_lt_internal (move : CenterMove) :
    moveToDigit move < 3 := by
  cases move <;> decide

theorem movementDigits_length_internal
    (guess : CenterGuess workTapeCount horizon) :
    (movementDigits guess).length =
      movementCount workTapeCount horizon := by
  simp [movementDigits]

theorem movementDigits_digit_lt_internal
    (guess : CenterGuess workTapeCount horizon)
    {digit : ℕ} (hdigit : digit ∈ movementDigits guess) :
    digit < 3 := by
  rw [movementDigits, List.mem_ofFn] at hdigit
  obtain ⟨index, rfl⟩ := hdigit
  exact toDigit_lt_internal _

@[simp] theorem movementDigitAt_movementIndex_internal
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon) (tape : TapeIndex workTapeCount) :
    movementDigitAt guess (movementIndex interval tape) =
      moveToDigit (guess.movement interval tape) := by
  simp [movementDigitAt, movementIndex]

theorem candidateDigits_encodeMovement_internal
    (guess : CenterGuess workTapeCount horizon) :
    candidateDigits (encodeMovementCode guess) =
      movementDigits guess := by
  apply (Nat.setInvOn_digitsAppend_ofDigits
    (b := 3) (by omega)
    (movementCount workTapeCount horizon)).1
  exact
    ⟨movementDigits_length_internal guess,
      fun digit hdigit =>
        movementDigits_digit_lt_internal guess hdigit⟩

theorem candidateGuess_encodeMovement_internal
    (guess : CenterGuess workTapeCount horizon)
    (hinitial : ∀ tape, guess.initialCenter tape = 0) :
    candidateGuess (encodeMovementCode guess) = guess := by
  cases guess with
  | mk initialCenter movement =>
      apply congrArg₂ CenterGuess.mk
      · funext tape
        exact (hinitial tape).symm
      · funext interval tape
        rw [show candidateDigits
            (encodeMovementCode
              { initialCenter := initialCenter,
                movement := movement }) =
              movementDigits
                { initialCenter := initialCenter,
                  movement := movement } from
          candidateDigits_encodeMovement_internal _]
        rw [List.getD_eq_getElem?_getD]
        simp [movementDigits,
          movementDigitAt_movementIndex_internal]
        exact ofDigit_toDigit_internal _

theorem actualCenterGuess_initialCenter_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) (tape : TapeIndex workTapeCount) :
    (actualCenterGuess tm x blockLength horizon).initialCenter tape = 0 := by
  unfold actualCenterGuess centerBlock TM.activeBlock timeBlockStart
    headBlock blockIndex
  simp only [zero_mul, TM.configurationAt_zero]
  unfold tapeAt
  split <;> rename_i hinput
  · simp
  · split <;> rename_i houtput
    · simp
    · simp

theorem actualCenterGuess_enumerated_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) :
    candidateGuess
        (encodeMovementCode
          (actualCenterGuess tm x blockLength horizon)) =
      actualCenterGuess tm x blockLength horizon :=
  candidateGuess_encodeMovement_internal _
    (actualCenterGuess_initialCenter_internal
      tm x blockLength horizon)

end Internal

end Enumeration

end Guess

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
