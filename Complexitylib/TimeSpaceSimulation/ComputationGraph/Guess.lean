/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Guess.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Guess.Internal

/-!
# Succinct guessed computation-graph validation

This module exposes Williams's constant-bits-per-boundary encoding of a
guessed computation graph. Prefix evaluation reconstructs each active tape
block, and finite FAIL sets detect underflow or disagreement with a claimed
trajectory.

For a block-respecting run, the canonical labels never FAIL. More strongly,
any guess with no trajectory FAIL induces exactly the existing
`contentPredecessor`, `chronologicalPredecessor`, and combined edge oracles.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace Guess

/-- Adjacent block indices are reconstructed exactly by `between`. -/
theorem BoundaryMove.apply_between {current next : ℕ}
    (hadjacent : next ≤ current + 1 ∧ current ≤ next + 1) :
    (BoundaryMove.between current next).apply current = some next :=
  Internal.boundaryMove_apply_between_internal hadjacent

/-- Quotient block indices change by at most one when positions do. -/
theorem blockIndex_le_succ_of_le_succ
    {blockLength left right : ℕ} (hblockLength : 0 < blockLength)
    (h : left ≤ right + 1) :
    blockIndex blockLength left ≤ blockIndex blockLength right + 1 :=
  Internal.blockIndex_le_succ_of_le_succ_internal hblockLength h

/-- A frozen deterministic transition moves every named tape head by at most
one cell in either direction. -/
theorem TM.configurationAt_head_adjacent
    (tm : TM workTapeCount) (x : List Bool) (time : ℕ)
    (tape : TapeIndex workTapeCount) :
    (tapeAt (tm.configurationAt x (time + 1)) tape).head ≤
        (tapeAt (tm.configurationAt x time) tape).head + 1 ∧
      (tapeAt (tm.configurationAt x time) tape).head ≤
        (tapeAt (tm.configurationAt x (time + 1)) tape).head + 1 :=
  Internal.configurationAt_head_adjacent_internal tm x time tape

/-- Consecutive active blocks of a block-respecting run differ by at most
one. -/
theorem TM.BlockRespectingOnInput.activeBlock_adjacent
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount)
    (hrespecting : tm.BlockRespectingOnInput x blockLength) :
    tm.activeBlock x blockLength (timeBlock + 1) tape ≤
        tm.activeBlock x blockLength timeBlock tape + 1 ∧
      tm.activeBlock x blockLength timeBlock tape ≤
        tm.activeBlock x blockLength (timeBlock + 1) tape + 1 :=
  Internal.activeBlock_adjacent_internal
    tm x blockLength timeBlock tape hrespecting

/-- Membership in the finite syntactic-underflow FAIL set. -/
theorem MovementGuess.mem_underflowFailures
    {guess : MovementGuess workTapeCount horizon}
    {checkpoint :
      Fin (horizon + 1) × TapeIndex workTapeCount} :
    checkpoint ∈ guess.underflowFailures ↔
      guess.derivedBlock checkpoint.2 checkpoint.1.val = none :=
  Internal.mem_underflowFailures_internal

/-- Membership in the finite trajectory-mismatch FAIL set. -/
theorem MovementGuess.mem_trajectoryFailures
    {guess : MovementGuess workTapeCount horizon}
    {trajectory : TapeIndex workTapeCount → ℕ → ℕ}
    {checkpoint :
      Fin (horizon + 1) × TapeIndex workTapeCount} :
    checkpoint ∈ guess.trajectoryFailures trajectory ↔
      guess.derivedBlock checkpoint.2 checkpoint.1.val ≠
        some (trajectory checkpoint.2 checkpoint.1.val) :=
  Internal.mem_trajectoryFailures_internal

/-- No FAIL is equivalent to exact derived-trajectory agreement at every
finite checkpoint. -/
theorem MovementGuess.isValidFor_iff
    {guess : MovementGuess workTapeCount horizon}
    {trajectory : TapeIndex workTapeCount → ℕ → ℕ} :
    guess.IsValidFor trajectory ↔
      ∀ (time : Fin (horizon + 1))
          (tape : TapeIndex workTapeCount),
        guess.derivedBlock tape time.val =
          some (trajectory tape time.val) :=
  Internal.isValidFor_iff_internal

/-- Any no-FAIL guess recovers the true content predecessor. -/
theorem MovementGuess.contentPredecessor?_eq
    (guess : MovementGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (timeBlock : Fin horizon) (tape : TapeIndex workTapeCount)
    (hvalid : guess.IsValidFor
      (actualTrajectory tm x blockLength)) :
    guess.contentPredecessor? timeBlock tape =
      some (contentPredecessor tm x blockLength timeBlock.val tape) :=
  Internal.contentPredecessor?_eq_internal
    guess tm x blockLength timeBlock tape hvalid

/-- Any no-FAIL guess recovers the true chronological predecessor. -/
theorem MovementGuess.chronologicalPredecessor?_eq
    (guess : MovementGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (timeBlock : Fin horizon) (tape : TapeIndex workTapeCount)
    (hvalid : guess.IsValidFor
      (actualTrajectory tm x blockLength)) :
    guess.chronologicalPredecessor? timeBlock tape =
      some (chronologicalPredecessor
        tm x blockLength timeBlock.val tape) :=
  Internal.chronologicalPredecessor?_eq_internal
    guess tm x blockLength timeBlock tape hvalid

/-- Any no-FAIL guess recovers the combined predecessor oracle. -/
theorem MovementGuess.predecessor?_eq
    (guess : MovementGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (timeBlock : Fin horizon)
    (index : PredecessorIndex workTapeCount)
    (hvalid : guess.IsValidFor
      (actualTrajectory tm x blockLength)) :
    guess.predecessor? timeBlock index =
      some (predecessor tm x blockLength timeBlock.val index) :=
  Internal.predecessor?_eq_internal
    guess tm x blockLength timeBlock index hvalid

/-- Fin-indexed form of guessed-edge soundness. -/
theorem MovementGuess.predecessorAt?_eq
    (guess : MovementGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (timeBlock : Fin horizon)
    (index : Fin (2 * (workTapeCount + 2)))
    (hvalid : guess.IsValidFor
      (actualTrajectory tm x blockLength)) :
    guess.predecessorAt? timeBlock index =
      some (predecessorAt tm x blockLength timeBlock.val index) :=
  Internal.predecessorAt?_eq_internal
    guess tm x blockLength timeBlock index hvalid

/-- The canonical labels reconstruct every actual active block in range. -/
theorem actualMovementGuess_derivedBlock
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon time : ℕ)
    (tape : TapeIndex workTapeCount)
    (hrespecting : tm.BlockRespectingOnInput x blockLength)
    (htime : time ≤ horizon) :
    (actualMovementGuess tm x blockLength horizon).derivedBlock tape time =
      some (tm.activeBlock x blockLength time tape) :=
  Internal.actualMovementGuess_derivedBlock_internal
    tm x blockLength horizon time tape hrespecting htime

/-- The actual movement sequence of a block-respecting trajectory never
produces FAIL. -/
theorem actualMovementGuess_isValidFor
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (hrespecting : tm.BlockRespectingOnInput x blockLength) :
    (actualMovementGuess tm x blockLength horizon).IsValidFor
      (actualTrajectory tm x blockLength) :=
  Internal.actualMovementGuess_isValidFor_internal
    tm x blockLength horizon hrespecting

end Guess

end ComputationGraph

end TimeSpaceSimulation

end Complexity
