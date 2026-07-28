/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype

/-!
# Succinct guessed computation graphs

Williams's non-oblivious simulation enumerates a constant-size movement label
for every named tape at every time-block boundary. A label records whether the
next active tape block is one block left, unchanged, or one block right.
Prefix evaluation of these labels reconstructs every active block index and
therefore the entire last-visit computation graph.

This file defines the executable encoding, its partial prefix semantics, the
option-valued predecessor oracle, and finite FAIL sets. The partial semantics
rejects a left move from block zero rather than silently using truncated
natural subtraction.

## Main definitions

- `BoundaryMove` -- a compact `{-1, 0, 1}` movement label
- `MovementGuess` -- one label per boundary and named tape
- `MovementGuess.derivedBlock` -- prefix-derived active block index
- `MovementGuess.predecessor?` -- option-valued guessed edge oracle
- `MovementGuess.trajectoryFailures` -- finite semantic FAIL checkpoints
- `actualMovementGuess` -- the canonical labels from an actual run
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace Guess

/-- A tape-block boundary movement, encoded by one of three values. -/
inductive BoundaryMove where
  /-- Move to the immediately preceding tape block. -/
  | left
  /-- Keep the current tape block active. -/
  | stay
  /-- Move to the immediately following tape block. -/
  | right
  deriving DecidableEq, Fintype

namespace BoundaryMove

/-- Signed `{-1, 0, 1}` interpretation of a boundary movement. -/
def signedOffset : BoundaryMove → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

/-- Apply a boundary movement to a natural tape-block index.

A left move from block zero is rejected with `none`. -/
def apply : BoundaryMove → ℕ → Option ℕ
  | .left, 0 => none
  | .left, block + 1 => some block
  | .stay, block => some block
  | .right, block => some (block + 1)

/-- Encode two consecutive block indices as a movement label.

The right label is the default outside the adjacent-block cases. Soundness
theorems show that this default is never used for a block-respecting run. -/
def between (current next : ℕ) : BoundaryMove :=
  if next = current then
    .stay
  else if next + 1 = current then
    .left
  else
    .right

end BoundaryMove

/-- A succinct movement-sequence guess for `horizon` time-block boundaries.

Entry `movement i tape` describes the change from active block `i` to active
block `i + 1`. -/
structure MovementGuess (workTapeCount horizon : ℕ) where
  /-- Active block of every named tape at time block zero. -/
  initialBlock : TapeIndex workTapeCount → ℕ
  /-- One trit per named tape and time-block boundary. -/
  movement : Fin horizon → TapeIndex workTapeCount → BoundaryMove

namespace MovementGuess

/-- Derive the active block at a time by streaming over the movement prefix.

The result is `none` after the horizon or when a prefix attempts to move left
from block zero. -/
def derivedBlock (guess : MovementGuess workTapeCount horizon)
    (tape : TapeIndex workTapeCount) : ℕ → Option ℕ
  | 0 => some (guess.initialBlock tape)
  | time + 1 =>
      if htime : time < horizon then
        (guess.derivedBlock tape time).bind
          (guess.movement ⟨time, htime⟩ tape).apply
      else
        none

/-- Earlier derived visits to a specified tape block. -/
def priorDerivedVisits (guess : MovementGuess workTapeCount horizon)
    (tape : TapeIndex workTapeCount) (time block : ℕ) : Finset ℕ :=
  (Finset.range time).filter fun previous =>
    guess.derivedBlock tape previous = some block

/-- Greatest earlier visit to the currently derived block.

An invalid current prefix yields `none`; callers distinguish that case by
first querying `derivedBlock`. -/
def previousDerivedVisit (guess : MovementGuess workTapeCount horizon)
    (tape : TapeIndex workTapeCount) (time : ℕ) : Option ℕ :=
  match guess.derivedBlock tape time with
  | none => none
  | some block =>
      if h : (guess.priorDerivedVisits tape time block).Nonempty then
        some ((guess.priorDerivedVisits tape time block).max' h)
      else
        none

/-- Guessed last-visit content predecessor, or `none` on an invalid prefix. -/
def contentPredecessor? (guess : MovementGuess workTapeCount horizon)
    (timeBlock : Fin horizon) (tape : TapeIndex workTapeCount) :
    Option (Node workTapeCount) :=
  match guess.derivedBlock tape timeBlock.val with
  | none => none
  | some block =>
      match guess.previousDerivedVisit tape timeBlock.val with
      | none => some (.source tape block)
      | some previous => some (.computation tape previous)

/-- Guessed chronological predecessor, or `none` on an invalid prefix. -/
def chronologicalPredecessor?
    (guess : MovementGuess workTapeCount horizon)
    (timeBlock : Fin horizon) (tape : TapeIndex workTapeCount) :
    Option (Node workTapeCount) :=
  match guess.derivedBlock tape timeBlock.val with
  | none => none
  | some block =>
      match timeBlock.val with
      | 0 => some (.source tape block)
      | previous + 1 => some (.computation tape previous)

/-- Select one option-valued predecessor role from the guessed graph. -/
def predecessor? (guess : MovementGuess workTapeCount horizon)
    (timeBlock : Fin horizon)
    (index : PredecessorIndex workTapeCount) :
    Option (Node workTapeCount) :=
  match index.1 with
  | .content => guess.contentPredecessor? timeBlock index.2
  | .chronological =>
      guess.chronologicalPredecessor? timeBlock index.2

/-- Fin-indexed option-valued predecessor oracle for a guessed graph. -/
def predecessorAt? (guess : MovementGuess workTapeCount horizon)
    (timeBlock : Fin horizon)
    (index : Fin (2 * (workTapeCount + 2))) :
    Option (Node workTapeCount) :=
  guess.predecessor? timeBlock
    ((predecessorIndexEquiv workTapeCount).symm index)

/-- Finite checkpoints whose derived movement prefix underflows. -/
def underflowFailures (guess : MovementGuess workTapeCount horizon) :
    Finset (Fin (horizon + 1) × TapeIndex workTapeCount) :=
  Finset.univ.filter fun checkpoint =>
    guess.derivedBlock checkpoint.2 checkpoint.1.val = none

/-- Finite FAIL checkpoints against an executable claimed trajectory.

This captures both an underflow and any incorrect movement label. -/
def trajectoryFailures (guess : MovementGuess workTapeCount horizon)
    (trajectory : TapeIndex workTapeCount → ℕ → ℕ) :
    Finset (Fin (horizon + 1) × TapeIndex workTapeCount) :=
  Finset.univ.filter fun checkpoint =>
    guess.derivedBlock checkpoint.2 checkpoint.1.val ≠
      some (trajectory checkpoint.2 checkpoint.1.val)

/-- A guessed movement sequence produces no FAIL against a trajectory. -/
def IsValidFor (guess : MovementGuess workTapeCount horizon)
    (trajectory : TapeIndex workTapeCount → ℕ → ℕ) : Prop :=
  guess.trajectoryFailures trajectory = ∅

end MovementGuess

/-- The actual active-block trajectory in tape-first argument order. -/
def actualTrajectory (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) : TapeIndex workTapeCount → ℕ → ℕ :=
  fun tape timeBlock =>
    activeTrajectory tm x blockLength tape timeBlock

/-- The canonical movement labels extracted from an actual run. -/
def actualMovementGuess (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) : MovementGuess workTapeCount horizon where
  initialBlock := fun tape =>
    tm.activeBlock x blockLength 0 tape
  movement := fun timeBlock tape =>
    BoundaryMove.between
      (tm.activeBlock x blockLength timeBlock.val tape)
      (tm.activeBlock x blockLength (timeBlock.val + 1) tape)

end Guess

end ComputationGraph

end TimeSpaceSimulation

end Complexity
