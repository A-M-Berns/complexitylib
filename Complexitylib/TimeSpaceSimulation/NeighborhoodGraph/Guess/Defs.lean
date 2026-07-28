/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Defs

/-!
# Guessed center trajectories for direct neighborhood graphs

For every named tape, one trit records whether the next interval center is
one block left, unchanged, or one block right. Prefix evaluation reconstructs
all guessed centers and rejects a left step from block zero.

The reconstructed centers determine the complete direct three-block graph:
each requested block, earlier containing neighborhood, and predecessor edge
is executable from the guess. Finite FAIL sets compare this reconstruction
with an arbitrary claimed center trajectory, while `firstFailure?` identifies
the least failing interval boundary.

No block-respecting hypothesis occurs in these definitions.

## Main definitions

- `CenterMove` -- compact `{-1, 0, 1}` center movement
- `CenterGuess` -- one movement per tape and interval boundary
- `CenterGuess.derivedCenter` -- partial prefix-derived center
- `CenterGuess.predecessorAt?` -- option-valued guessed graph oracle
- `CenterGuess.trajectoryFailures` -- finite FAIL checkpoints
- `CenterGuess.firstFailure?` -- least failing interval boundary
- `actualCenterGuess` -- movements extracted from the true computation
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace Guess

/-- Change of one tape's center block across an interval boundary. -/
inductive CenterMove where
  /-- Move to the preceding block. -/
  | left
  /-- Keep the same center block. -/
  | stay
  /-- Move to the succeeding block. -/
  | right
  deriving DecidableEq, Fintype

namespace CenterMove

/-- Signed interpretation of a center movement. -/
def signedOffset : CenterMove → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

/-- Apply a center movement, rejecting a left move from block zero. -/
def apply : CenterMove → ℕ → Option ℕ
  | .left, 0 => none
  | .left, center + 1 => some center
  | .stay, center => some center
  | .right, center => some (center + 1)

/-- Encode a pair of consecutive center blocks.

The right movement is the default outside the adjacent cases. Soundness
shows that the default is exact for true interval centers. -/
def between (current next : ℕ) : CenterMove :=
  if next = current then
    .stay
  else if next + 1 = current then
    .left
  else
    .right

end CenterMove

/-- Succinct center movements through `horizon` interval boundaries. -/
structure CenterGuess (workTapeCount horizon : ℕ) where
  /-- Center of every named tape at interval zero. -/
  initialCenter : TapeIndex workTapeCount → ℕ
  /-- Movement from interval `i` to interval `i + 1`. -/
  movement : Fin horizon → TapeIndex workTapeCount → CenterMove

namespace CenterGuess

/-- Reconstruct one tape center by streaming over a movement prefix. -/
def derivedCenter (guess : CenterGuess workTapeCount horizon)
    (tape : TapeIndex workTapeCount) : ℕ → Option ℕ
  | 0 => some (guess.initialCenter tape)
  | interval + 1 =>
      if hinterval : interval < horizon then
        (guess.derivedCenter tape interval).bind
          (guess.movement ⟨interval, hinterval⟩ tape).apply
      else
        none

/-- Earlier guessed intervals whose neighborhood contains a requested block. -/
def priorIntervals (guess : CenterGuess workTapeCount horizon)
    (tape : TapeIndex workTapeCount)
    (requestedBlock interval : ℕ) : Finset (Fin interval) :=
  Finset.univ.filter fun previous =>
    (match guess.derivedCenter tape previous.val with
    | none => false
    | some center =>
        decide (NeighborhoodContains center requestedBlock)) = true

/-- Greatest earlier guessed neighborhood containing the requested block. -/
def previousInterval (guess : CenterGuess workTapeCount horizon)
    (tape : TapeIndex workTapeCount)
    (requestedBlock interval : ℕ) : Option (Fin interval) :=
  if h :
      (guess.priorIntervals tape requestedBlock interval).Nonempty then
    some ((guess.priorIntervals tape requestedBlock interval).max' h)
  else
    none

/-- Guessed content predecessor, or `none` after an invalid center prefix. -/
def contentPredecessor? (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon) (tape : TapeIndex workTapeCount)
    (slot : Slot) : Option (Node workTapeCount) :=
  match guess.derivedCenter tape interval.val with
  | none => none
  | some center =>
      let requested := neighborBlock center slot
      match guess.previousInterval tape requested interval.val with
      | none => some (.source tape requested)
      | some previous =>
          match guess.derivedCenter tape previous.val with
          | none => none
          | some previousCenter =>
              some (.computation tape
                (matchingSlot previousCenter requested) previous.val)

/-- Guessed chronological predecessor, or `none` on an invalid prefix. -/
def chronologicalPredecessor?
    (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon) (tape : TapeIndex workTapeCount) :
    Option (Node workTapeCount) :=
  match guess.derivedCenter tape interval.val with
  | none => none
  | some center =>
      match interval.val with
      | 0 => some (.source tape center)
      | previous + 1 => some (.computation tape .center previous)

/-- Select one option-valued predecessor role from the guessed graph. -/
def predecessor? (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (index : PredecessorIndex workTapeCount) :
    Option (Node workTapeCount) :=
  match index.1 with
  | .content slot =>
      guess.contentPredecessor? interval index.2 slot
  | .chronological =>
      guess.chronologicalPredecessor? interval index.2

/-- Fixed-Fin option-valued predecessor oracle for the guessed graph. -/
def predecessorAt? (guess : CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (index : Fin (4 * (workTapeCount + 2))) :
    Option (Node workTapeCount) :=
  guess.predecessor? interval
    ((predecessorIndexEquiv workTapeCount).symm index)

/-- Finite checkpoints whose derived center disagrees with a trajectory. -/
def trajectoryFailures (guess : CenterGuess workTapeCount horizon)
    (trajectory : TapeIndex workTapeCount → ℕ → ℕ) :
    Finset (Fin (horizon + 1) × TapeIndex workTapeCount) :=
  Finset.univ.filter fun checkpoint =>
    guess.derivedCenter checkpoint.2 checkpoint.1.val ≠
      some (trajectory checkpoint.2 checkpoint.1.val)

/-- Interval boundaries carrying at least one failing named tape. -/
def failureTimes (guess : CenterGuess workTapeCount horizon)
    (trajectory : TapeIndex workTapeCount → ℕ → ℕ) :
    Finset (Fin (horizon + 1)) :=
  Finset.univ.filter fun interval =>
    ∃ tape : TapeIndex workTapeCount,
      guess.derivedCenter tape interval.val ≠
        some (trajectory tape interval.val)

/-- Least failing interval boundary, if any. -/
def firstFailure? (guess : CenterGuess workTapeCount horizon)
    (trajectory : TapeIndex workTapeCount → ℕ → ℕ) :
    Option (Fin (horizon + 1)) :=
  if h : (guess.failureTimes trajectory).Nonempty then
    some ((guess.failureTimes trajectory).min' h)
  else
    none

/-- A center guess produces no FAIL against the supplied trajectory. -/
def IsValidFor (guess : CenterGuess workTapeCount horizon)
    (trajectory : TapeIndex workTapeCount → ℕ → ℕ) : Prop :=
  guess.trajectoryFailures trajectory = ∅

end CenterGuess

/-- True interval-center trajectory in tape-first argument order. -/
def actualCenterTrajectory (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) : TapeIndex workTapeCount → ℕ → ℕ :=
  fun tape interval =>
    centerBlock tm x blockLength interval tape

/-- Canonical movement guess extracted from the true center trajectory. -/
def actualCenterGuess (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) : CenterGuess workTapeCount horizon where
  initialCenter := fun tape =>
    centerBlock tm x blockLength 0 tape
  movement := fun interval tape =>
    CenterMove.between
      (centerBlock tm x blockLength interval.val tape)
      (centerBlock tm x blockLength (interval.val + 1) tape)

end Guess

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
