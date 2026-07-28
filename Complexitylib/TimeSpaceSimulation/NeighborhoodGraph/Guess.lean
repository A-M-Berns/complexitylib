/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Internal

/-!
# Guessed direct three-block neighborhood graphs

One movement trit per named tape and interval boundary reconstructs the
center block of every direct three-block neighborhood. A left step from block
zero is rejected, and finite FAIL sets compare every derived center with a
claimed trajectory.

For every positive block length, exactly `b` Turing-machine transitions move
a head by at most `b` cells. Quotienting positions into length-`b` blocks
therefore changes each true center by at most one, without a block-respecting
normalization hypothesis. Consequently the canonical center guess never
fails.

More strongly, any no-FAIL guess induces exactly the direct neighborhood
graph's content, chronological, combined, and fixed-Fin predecessor oracles.
Every false finite guess has a least failing interval boundary and all named
tapes agree at every earlier boundary.

## Main theorems

- `centerBlock_adjacent` -- arbitrary-machine centers change by at most one
- `CenterGuess.isValidFor_iff` -- no FAIL iff pointwise agreement
- `CenterGuess.not_isValidFor_has_firstFailure` -- least failure certificate
- `CenterGuess.predecessorAt?_eq` -- complete guessed-graph soundness
- `actualCenterGuess_isValidFor` -- the true center guess never fails
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace Guess

/-- Adjacent center blocks are reconstructed exactly by `between`, including
the natural-number left boundary. -/
theorem CenterMove.apply_between {current next : ℕ}
    (hadjacent : next ≤ current + 1 ∧ current ≤ next + 1) :
    (CenterMove.between current next).apply current = some next :=
  Internal.centerMove_apply_between_internal hadjacent

/-- Dividing by a positive block length turns a displacement of at most one
block length into a block-index increase of at most one. -/
theorem blockIndex_le_succ_of_le_add_blockLength
    {blockLength left right : ℕ}
    (hpositive : 0 < blockLength)
    (h : left ≤ right + blockLength) :
    blockIndex blockLength left ≤
      blockIndex blockLength right + 1 :=
  Internal.blockIndex_le_succ_of_le_add_blockLength_internal
    hpositive h

/-- Across any exact number of frozen deterministic transitions, every named
head moves by at most that many cells in either direction. -/
theorem TM.configurationAt_head_distance
    (tm : TM workTapeCount) (x : List Bool)
    (start steps : ℕ) (tape : TapeIndex workTapeCount) :
    (tapeAt (tm.configurationAt x (start + steps)) tape).head ≤
        (tapeAt (tm.configurationAt x start) tape).head + steps ∧
      (tapeAt (tm.configurationAt x start) tape).head ≤
        (tapeAt (tm.configurationAt x (start + steps)) tape).head +
          steps :=
  Internal.configurationAt_head_distance_internal
    tm x start steps tape

/-- Consecutive true interval centers of an arbitrary machine differ by at
most one block. -/
theorem centerBlock_adjacent
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength interval : ℕ)
    (tape : TapeIndex workTapeCount)
    (hpositive : 0 < blockLength) :
    centerBlock tm x blockLength (interval + 1) tape ≤
        centerBlock tm x blockLength interval tape + 1 ∧
      centerBlock tm x blockLength interval tape ≤
        centerBlock tm x blockLength (interval + 1) tape + 1 :=
  Internal.centerBlock_adjacent_internal
    tm x blockLength interval tape hpositive

/-- Membership in the finite tape-by-boundary FAIL set. -/
theorem CenterGuess.mem_trajectoryFailures
    {guess : CenterGuess workTapeCount horizon}
    {trajectory : TapeIndex workTapeCount → ℕ → ℕ}
    {checkpoint :
      Fin (horizon + 1) × TapeIndex workTapeCount} :
    checkpoint ∈ guess.trajectoryFailures trajectory ↔
      guess.derivedCenter checkpoint.2 checkpoint.1.val ≠
        some (trajectory checkpoint.2 checkpoint.1.val) :=
  Internal.mem_trajectoryFailures_internal

/-- Membership in the finite set of failing interval boundaries. -/
theorem CenterGuess.mem_failureTimes
    {guess : CenterGuess workTapeCount horizon}
    {trajectory : TapeIndex workTapeCount → ℕ → ℕ}
    {interval : Fin (horizon + 1)} :
    interval ∈ guess.failureTimes trajectory ↔
      ∃ tape : TapeIndex workTapeCount,
        guess.derivedCenter tape interval.val ≠
          some (trajectory tape interval.val) :=
  Internal.mem_failureTimes_internal

/-- No FAIL is equivalent to exact center agreement at every finite
checkpoint. -/
theorem CenterGuess.isValidFor_iff
    {guess : CenterGuess workTapeCount horizon}
    {trajectory : TapeIndex workTapeCount → ℕ → ℕ} :
    guess.IsValidFor trajectory ↔
      ∀ (interval : Fin (horizon + 1))
          (tape : TapeIndex workTapeCount),
        guess.derivedCenter tape interval.val =
          some (trajectory tape interval.val) :=
  Internal.isValidFor_iff_internal

/-- Every invalid finite center guess has a least failing interval boundary.
At least one named tape fails there, and every tape agrees strictly before
it. -/
theorem CenterGuess.not_isValidFor_has_firstFailure
    (guess : CenterGuess workTapeCount horizon)
    (trajectory : TapeIndex workTapeCount → ℕ → ℕ)
    (hinvalid : ¬guess.IsValidFor trajectory) :
    ∃ (first : Fin (horizon + 1))
        (tape : TapeIndex workTapeCount),
      guess.firstFailure? trajectory = some first ∧
        guess.derivedCenter tape first.val ≠
          some (trajectory tape first.val) ∧
        ∀ earlier : Fin (horizon + 1), earlier.val < first.val →
          ∀ earlierTape : TapeIndex workTapeCount,
            guess.derivedCenter earlierTape earlier.val =
              some (trajectory earlierTape earlier.val) :=
  Internal.not_isValidFor_has_firstFailure_internal
    guess trajectory hinvalid

/-- A no-FAIL guess recovers every earlier neighborhood containing a
requested block. -/
theorem CenterGuess.priorIntervals_eq
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon) (tape : TapeIndex workTapeCount)
    (requested : ℕ)
    (hvalid : guess.IsValidFor
      (actualCenterTrajectory tm x blockLength)) :
    guess.priorIntervals tape requested interval.val =
      NeighborhoodGraph.priorIntervals tm x blockLength tape
        requested interval.val :=
  Internal.priorIntervals_eq_internal
    guess tm x blockLength interval tape requested hvalid

/-- A no-FAIL guess recovers the greatest earlier containing interval. -/
theorem CenterGuess.previousInterval_eq
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon) (tape : TapeIndex workTapeCount)
    (requested : ℕ)
    (hvalid : guess.IsValidFor
      (actualCenterTrajectory tm x blockLength)) :
    guess.previousInterval tape requested interval.val =
      NeighborhoodGraph.previousInterval tm x blockLength tape
        requested interval.val :=
  Internal.previousInterval_eq_internal
    guess tm x blockLength interval tape requested hvalid

/-- A no-FAIL guess recovers the direct graph's content predecessor. -/
theorem CenterGuess.contentPredecessor?_eq
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon) (tape : TapeIndex workTapeCount)
    (slot : Slot)
    (hvalid : guess.IsValidFor
      (actualCenterTrajectory tm x blockLength)) :
    guess.contentPredecessor? interval tape slot =
      some (NeighborhoodGraph.contentPredecessor
        tm x blockLength interval.val tape slot) :=
  Internal.contentPredecessor?_eq_internal
    guess tm x blockLength interval tape slot hvalid

/-- A no-FAIL guess recovers the direct graph's chronological predecessor. -/
theorem CenterGuess.chronologicalPredecessor?_eq
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon) (tape : TapeIndex workTapeCount)
    (hvalid : guess.IsValidFor
      (actualCenterTrajectory tm x blockLength)) :
    guess.chronologicalPredecessor? interval tape =
      some (NeighborhoodGraph.chronologicalPredecessor
        tm x blockLength interval.val tape) :=
  Internal.chronologicalPredecessor?_eq_internal
    guess tm x blockLength interval tape hvalid

/-- A no-FAIL guess recovers the combined predecessor oracle. -/
theorem CenterGuess.predecessor?_eq
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon)
    (index : PredecessorIndex workTapeCount)
    (hvalid : guess.IsValidFor
      (actualCenterTrajectory tm x blockLength)) :
    guess.predecessor? interval index =
      some (NeighborhoodGraph.predecessor
        tm x blockLength interval.val index) :=
  Internal.predecessor?_eq_internal
    guess tm x blockLength interval index hvalid

/-- Fixed-Fin form of complete guessed-neighborhood-graph soundness. -/
theorem CenterGuess.predecessorAt?_eq
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon)
    (index : Fin (4 * (workTapeCount + 2)))
    (hvalid : guess.IsValidFor
      (actualCenterTrajectory tm x blockLength)) :
    guess.predecessorAt? interval index =
      some (NeighborhoodGraph.predecessorAt
        tm x blockLength interval.val index) :=
  Internal.predecessorAt?_eq_internal
    guess tm x blockLength interval index hvalid

/-- Agreement through the requested interval already determines its typed
predecessor; no later guessed center is needed. -/
theorem CenterGuess.predecessor?_eq_of_prefix
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon)
    (index : PredecessorIndex workTapeCount)
    (hprefix :
      ∀ boundary : Fin (horizon + 1),
        boundary.val ≤ interval.val →
          ∀ tape : TapeIndex workTapeCount,
            guess.derivedCenter tape boundary.val =
              some (actualCenterTrajectory
                tm x blockLength tape boundary.val)) :
    guess.predecessor? interval index =
      some (NeighborhoodGraph.predecessor
        tm x blockLength interval.val index) :=
  Internal.predecessor?_eq_of_prefix_internal
    guess tm x blockLength interval index hprefix

/-- Fixed-Fin predecessor soundness needs only center agreement through the
requested interval. -/
theorem CenterGuess.predecessorAt?_eq_of_prefix
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon)
    (index : Fin (4 * (workTapeCount + 2)))
    (hprefix :
      ∀ boundary : Fin (horizon + 1),
        boundary.val ≤ interval.val →
          ∀ tape : TapeIndex workTapeCount,
            guess.derivedCenter tape boundary.val =
              some (actualCenterTrajectory
                tm x blockLength tape boundary.val)) :
    guess.predecessorAt? interval index =
      some (NeighborhoodGraph.predecessorAt
        tm x blockLength interval.val index) :=
  Internal.predecessorAt?_eq_of_prefix_internal
    guess tm x blockLength interval index hprefix

/-- The canonical movements reconstruct every true center in range. -/
theorem actualCenterGuess_derivedCenter
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon interval : ℕ)
    (tape : TapeIndex workTapeCount)
    (hpositive : 0 < blockLength)
    (hinterval : interval ≤ horizon) :
    (actualCenterGuess tm x blockLength horizon).derivedCenter
        tape interval =
      some (centerBlock tm x blockLength interval tape) :=
  Internal.actualCenterGuess_derivedCenter_internal
    tm x blockLength horizon interval tape hpositive hinterval

/-- The true center movement sequence of every arbitrary deterministic
machine is valid for every positive block length. -/
theorem actualCenterGuess_isValidFor
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (hpositive : 0 < blockLength) :
    (actualCenterGuess tm x blockLength horizon).IsValidFor
      (actualCenterTrajectory tm x blockLength) :=
  Internal.actualCenterGuess_isValidFor_internal
    tm x blockLength horizon hpositive

end Guess

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
