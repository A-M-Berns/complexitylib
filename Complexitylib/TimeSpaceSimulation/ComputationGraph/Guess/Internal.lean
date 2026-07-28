/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Contents
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Guess.Defs

/-!
# Soundness internals for succinct guessed computation graphs

This file proves that one Turing-machine transition changes a named tape
block by at most one, that the canonical movement labels reconstruct the
actual active-block trajectory, and that every no-FAIL guess induces exactly
the existing last-visit and chronological predecessor graph.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace Guess

namespace Internal

theorem boundaryMove_apply_between_internal {current next : ℕ}
    (hadjacent : next ≤ current + 1 ∧ current ≤ next + 1) :
    (BoundaryMove.between current next).apply current = some next := by
  unfold BoundaryMove.between
  split_ifs with hequal hleft
  · subst next
    rfl
  · cases current with
    | zero => omega
    | succ current =>
        simp only [BoundaryMove.apply, Option.some.injEq]
        omega
  · have hright : next = current + 1 := by omega
    rw [hright]
    rfl

theorem blockIndex_le_succ_of_le_succ_internal
    {blockLength left right : ℕ} (hblockLength : 0 < blockLength)
    (h : left ≤ right + 1) :
    blockIndex blockLength left ≤ blockIndex blockLength right + 1 := by
  unfold blockIndex
  calc
    left / blockLength ≤ (right + 1) / blockLength :=
      Nat.div_le_div_right h
    _ ≤ right / blockLength + 1 := by
      apply Nat.div_le_of_le_mul
      exact Nat.succ_le_of_lt
        (Nat.lt_mul_div_succ right hblockLength)

theorem tape_head_le_move_add_one_internal
    (tape : Tape) (direction : Dir3) :
    tape.head ≤ (tape.move direction).head + 1 := by
  cases direction <;> simp [Tape.move] <;> omega

theorem tape_head_le_writeAndMove_add_one_internal
    (tape : Tape) (symbol : Γ) (direction : Dir3) :
    tape.head ≤ (tape.writeAndMove symbol direction).head + 1 := by
  simpa only [Tape.write_head] using
    tape_head_le_move_add_one_internal (tape.write symbol) direction

theorem tapeAt_trace_one_head_adjacent_internal
    (tm : NTM workTapeCount) (cfg : Cfg workTapeCount tm.Q)
    (choice : Bool) (tape : TapeIndex workTapeCount) :
    (tapeAt (tm.trace 1 (fun _ => choice) cfg) tape).head ≤
        (tapeAt cfg tape).head + 1 ∧
      (tapeAt cfg tape).head ≤
        (tapeAt (tm.trace 1 (fun _ => choice) cfg) tape).head + 1 := by
  by_cases hinput : tape.val = 0
  · have htape : tape = TapeIndex.input workTapeCount := Fin.ext hinput
    rw [htape]
    simp only [tapeAt_input]
    by_cases hhalt : cfg.state = tm.qhalt
    · simp [NTM.trace, hhalt]
    · simp only [NTM.trace, hhalt, if_false]
      exact
        ⟨Tape.head_move_le _ _,
          tape_head_le_move_add_one_internal _ _⟩
  · by_cases houtput : tape.val = workTapeCount + 1
    · have htape : tape = TapeIndex.output workTapeCount :=
        Fin.ext houtput
      rw [htape]
      simp only [tapeAt_output]
      by_cases hhalt : cfg.state = tm.qhalt
      · simp [NTM.trace, hhalt]
      · simp only [NTM.trace, hhalt, if_false]
        exact
          ⟨Tape.head_writeAndMove_le _ _ _,
            tape_head_le_writeAndMove_add_one_internal _ _ _⟩
    · let index : Fin workTapeCount :=
        ⟨tape.val - 1, by omega⟩
      have htape : tape = TapeIndex.work index := by
        apply Fin.ext
        simp only [TapeIndex.work, index]
        omega
      rw [htape]
      simp only [tapeAt_work]
      by_cases hhalt : cfg.state = tm.qhalt
      · simp [NTM.trace, hhalt]
      · simp only [NTM.trace, hhalt, if_false]
        exact
          ⟨Tape.head_writeAndMove_le _ _ _,
            tape_head_le_writeAndMove_add_one_internal _ _ _⟩

theorem configurationAt_head_adjacent_internal
    (tm : TM workTapeCount) (x : List Bool) (time : ℕ)
    (tape : TapeIndex workTapeCount) :
    (tapeAt (tm.configurationAt x (time + 1)) tape).head ≤
        (tapeAt (tm.configurationAt x time) tape).head + 1 ∧
      (tapeAt (tm.configurationAt x time) tape).head ≤
        (tapeAt (tm.configurationAt x (time + 1)) tape).head + 1 := by
  rw [TM.configurationAt_succ]
  exact tapeAt_trace_one_head_adjacent_internal _ _ _ _

theorem activeBlock_adjacent_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount)
    (hrespecting : tm.BlockRespectingOnInput x blockLength) :
    tm.activeBlock x blockLength (timeBlock + 1) tape ≤
        tm.activeBlock x blockLength timeBlock tape + 1 ∧
      tm.activeBlock x blockLength timeBlock tape ≤
        tm.activeBlock x blockLength (timeBlock + 1) tape + 1 := by
  have hpositive : 0 < blockLength :=
    hrespecting.blockLength_pos tm x blockLength
  let lastOffset : Fin blockLength :=
    ⟨blockLength - 1, by omega⟩
  let boundaryTime :=
    timeBlockStart blockLength timeBlock + lastOffset.val
  have hboundarySucc : boundaryTime + 1 =
      timeBlockStart blockLength (timeBlock + 1) := by
    dsimp only [boundaryTime, lastOffset]
    simp only [timeBlockStart, Nat.add_mul]
    omega
  have hbefore :
      headBlock blockLength
          (tm.configurationAt x boundaryTime) tape =
        tm.activeBlock x blockLength timeBlock tape := by
    dsimp only [boundaryTime]
    exact hrespecting.headBlock
      tm x blockLength timeBlock lastOffset tape
  have hnext :
      headBlock blockLength
          (tm.configurationAt x (boundaryTime + 1)) tape =
        tm.activeBlock x blockLength (timeBlock + 1) tape := by
    rw [hboundarySucc]
    rfl
  have hheads :=
    configurationAt_head_adjacent_internal tm x boundaryTime tape
  have hforward :=
    blockIndex_le_succ_of_le_succ_internal hpositive hheads.1
  have hbackward :=
    blockIndex_le_succ_of_le_succ_internal hpositive hheads.2
  change
    headBlock blockLength
        (tm.configurationAt x (boundaryTime + 1)) tape ≤
      headBlock blockLength
        (tm.configurationAt x boundaryTime) tape + 1
    at hforward
  change
    headBlock blockLength
        (tm.configurationAt x boundaryTime) tape ≤
      headBlock blockLength
        (tm.configurationAt x (boundaryTime + 1)) tape + 1
    at hbackward
  simpa only [hbefore, hnext] using
    And.intro hforward hbackward

theorem mem_underflowFailures_internal
    {guess : MovementGuess workTapeCount horizon}
    {checkpoint :
      Fin (horizon + 1) × TapeIndex workTapeCount} :
    checkpoint ∈ guess.underflowFailures ↔
      guess.derivedBlock checkpoint.2 checkpoint.1.val = none := by
  simp [MovementGuess.underflowFailures]

theorem mem_trajectoryFailures_internal
    {guess : MovementGuess workTapeCount horizon}
    {trajectory : TapeIndex workTapeCount → ℕ → ℕ}
    {checkpoint :
      Fin (horizon + 1) × TapeIndex workTapeCount} :
    checkpoint ∈ guess.trajectoryFailures trajectory ↔
      guess.derivedBlock checkpoint.2 checkpoint.1.val ≠
        some (trajectory checkpoint.2 checkpoint.1.val) := by
  simp [MovementGuess.trajectoryFailures]

theorem isValidFor_iff_internal
    {guess : MovementGuess workTapeCount horizon}
    {trajectory : TapeIndex workTapeCount → ℕ → ℕ} :
    guess.IsValidFor trajectory ↔
      ∀ (time : Fin (horizon + 1))
          (tape : TapeIndex workTapeCount),
        guess.derivedBlock tape time.val =
          some (trajectory tape time.val) := by
  constructor
  · intro hvalid time tape
    have hnotmem :
        (time, tape) ∉ guess.trajectoryFailures trajectory := by
      rw [hvalid]
      simp
    by_contra hne
    exact hnotmem (mem_trajectoryFailures_internal.mpr hne)
  · intro htrajectory
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨checkpoint, hmem⟩
    exact (mem_trajectoryFailures_internal.mp hmem)
      (htrajectory checkpoint.1 checkpoint.2)

theorem previousDerivedVisit_eq_previousVisit_internal
    (guess : MovementGuess workTapeCount horizon)
    (trajectory : TapeIndex workTapeCount → ℕ → ℕ)
    (tape : TapeIndex workTapeCount) (time : ℕ)
    (htrajectory : ∀ previous, previous ≤ time →
      guess.derivedBlock tape previous =
        some (trajectory tape previous)) :
    guess.previousDerivedVisit tape time =
      previousVisit (trajectory tape) time := by
  have hcurrent := htrajectory time le_rfl
  have hprior :
      guess.priorDerivedVisits tape time (trajectory tape time) =
        priorVisits (trajectory tape) time := by
    ext previous
    simp only [MovementGuess.priorDerivedVisits, priorVisits,
      Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hlt, hderived⟩
      have hprevious := htrajectory previous (Nat.le_of_lt hlt)
      rw [hprevious] at hderived
      exact ⟨hlt, Option.some.inj hderived⟩
    · rintro ⟨hlt, hactive⟩
      refine ⟨hlt, ?_⟩
      rw [htrajectory previous (Nat.le_of_lt hlt), hactive]
  unfold MovementGuess.previousDerivedVisit
  simp only [hcurrent]
  unfold previousVisit
  rw [hprior]

theorem contentPredecessor?_eq_internal
    (guess : MovementGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (timeBlock : Fin horizon) (tape : TapeIndex workTapeCount)
    (hvalid : guess.IsValidFor
      (actualTrajectory tm x blockLength)) :
    guess.contentPredecessor? timeBlock tape =
      some (contentPredecessor tm x blockLength timeBlock.val tape) := by
  have htrajectory : ∀ previous, previous ≤ timeBlock.val →
      guess.derivedBlock tape previous =
        some (actualTrajectory tm x blockLength tape previous) := by
    intro previous hprevious
    exact isValidFor_iff_internal.mp hvalid
      ⟨previous, by omega⟩ tape
  have hcurrent := htrajectory timeBlock.val le_rfl
  have hprevious := previousDerivedVisit_eq_previousVisit_internal guess
    (actualTrajectory tm x blockLength) tape timeBlock.val htrajectory
  unfold MovementGuess.contentPredecessor?
  simp only [hcurrent]
  rw [hprevious]
  generalize hvisit :
    previousVisit (actualTrajectory tm x blockLength tape)
      timeBlock.val = visit
  change previousVisit (activeTrajectory tm x blockLength tape)
    timeBlock.val = visit at hvisit
  cases visit <;>
    simp [contentPredecessor, hvisit, actualTrajectory]

theorem chronologicalPredecessor?_eq_internal
    (guess : MovementGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (timeBlock : Fin horizon) (tape : TapeIndex workTapeCount)
    (hvalid : guess.IsValidFor
      (actualTrajectory tm x blockLength)) :
    guess.chronologicalPredecessor? timeBlock tape =
      some (chronologicalPredecessor
        tm x blockLength timeBlock.val tape) := by
  have hcurrent := isValidFor_iff_internal.mp hvalid
    ⟨timeBlock.val, by omega⟩ tape
  unfold MovementGuess.chronologicalPredecessor?
  simp only [hcurrent]
  cases htime : timeBlock.val with
  | zero => simp [chronologicalPredecessor, actualTrajectory]
  | succ previous => simp [chronologicalPredecessor]

theorem predecessor?_eq_internal
    (guess : MovementGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (timeBlock : Fin horizon)
    (index : PredecessorIndex workTapeCount)
    (hvalid : guess.IsValidFor
      (actualTrajectory tm x blockLength)) :
    guess.predecessor? timeBlock index =
      some (predecessor tm x blockLength timeBlock.val index) := by
  cases index with
  | mk kind tape =>
      cases kind with
      | content =>
          exact contentPredecessor?_eq_internal
            guess tm x blockLength timeBlock tape hvalid
      | chronological =>
          exact chronologicalPredecessor?_eq_internal
            guess tm x blockLength timeBlock tape hvalid

theorem predecessorAt?_eq_internal
    (guess : MovementGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (timeBlock : Fin horizon)
    (index : Fin (2 * (workTapeCount + 2)))
    (hvalid : guess.IsValidFor
      (actualTrajectory tm x blockLength)) :
    guess.predecessorAt? timeBlock index =
      some (predecessorAt tm x blockLength timeBlock.val index) := by
  unfold MovementGuess.predecessorAt? predecessorAt
  exact predecessor?_eq_internal guess tm x blockLength timeBlock
    ((predecessorIndexEquiv workTapeCount).symm index) hvalid

theorem actualMovementGuess_derivedBlock_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon time : ℕ)
    (tape : TapeIndex workTapeCount)
    (hrespecting : tm.BlockRespectingOnInput x blockLength)
    (htime : time ≤ horizon) :
    (actualMovementGuess tm x blockLength horizon).derivedBlock tape time =
      some (tm.activeBlock x blockLength time tape) := by
  induction time with
  | zero => rfl
  | succ time ih =>
      have hlt : time < horizon := by omega
      rw [MovementGuess.derivedBlock]
      simp only [hlt, dite_true]
      rw [ih (Nat.le_of_lt hlt)]
      exact boundaryMove_apply_between_internal
        (activeBlock_adjacent_internal
          tm x blockLength time tape hrespecting)

theorem actualMovementGuess_isValidFor_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (hrespecting : tm.BlockRespectingOnInput x blockLength) :
    (actualMovementGuess tm x blockLength horizon).IsValidFor
      (actualTrajectory tm x blockLength) := by
  apply isValidFor_iff_internal.mpr
  intro time tape
  simpa only [actualTrajectory] using
    actualMovementGuess_derivedBlock_internal
      tm x blockLength horizon time.val tape hrespecting (by omega)

end Internal

end Guess

end ComputationGraph

end TimeSpaceSimulation

end Complexity
