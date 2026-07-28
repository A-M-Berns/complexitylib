/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Locality
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Defs

/-!
# Soundness internals for guessed direct neighborhood graphs

This file derives center adjacency from the exact length-`b` locality head
distance, proves soundness of the guessed predecessor oracle, validates the
canonical true guess, and identifies the first failing interval boundary of
every invalid finite guess.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodGraph

namespace Guess

namespace Internal

theorem centerMove_apply_between_internal {current next : ℕ}
    (hadjacent : next ≤ current + 1 ∧ current ≤ next + 1) :
    (CenterMove.between current next).apply current = some next := by
  unfold CenterMove.between
  split_ifs with hequal hleft
  · subst next
    rfl
  · cases current with
    | zero => omega
    | succ current =>
        simp only [CenterMove.apply, Option.some.injEq]
        omega
  · have hright : next = current + 1 := by omega
    rw [hright]
    rfl

theorem blockIndex_le_succ_of_le_add_blockLength_internal
    {blockLength left right : ℕ}
    (hpositive : 0 < blockLength)
    (h : left ≤ right + blockLength) :
    blockIndex blockLength left ≤
      blockIndex blockLength right + 1 := by
  unfold blockIndex
  calc
    left / blockLength ≤ (right + blockLength) / blockLength :=
      Nat.div_le_div_right h
    _ = right / blockLength + 1 :=
      Nat.add_div_right right hpositive

theorem configurationAt_head_distance_internal
    (tm : TM workTapeCount) (x : List Bool)
    (start steps : ℕ) (tape : TapeIndex workTapeCount) :
    (tapeAt (tm.configurationAt x (start + steps)) tape).head ≤
        (tapeAt (tm.configurationAt x start) tape).head + steps ∧
      (tapeAt (tm.configurationAt x start) tape).head ≤
        (tapeAt (tm.configurationAt x (start + steps)) tape).head +
          steps := by
  have hconfiguration :
      tm.configurationAt x (start + steps) =
        tm.toNTM.trace steps (fun _ => false)
          (tm.configurationAt x start) := by
    unfold TM.configurationAt
    simpa using tm.toNTM.trace_add_fun start steps
      (fun _ => false) (tm.initCfg x)
  rw [hconfiguration]
  exact TimeSpaceSimulation.NTM.trace_head_distance tm.toNTM steps
    (fun _ => false) (tm.configurationAt x start) tape

theorem centerBlock_adjacent_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength interval : ℕ)
    (tape : TapeIndex workTapeCount)
    (hpositive : 0 < blockLength) :
    centerBlock tm x blockLength (interval + 1) tape ≤
        centerBlock tm x blockLength interval tape + 1 ∧
      centerBlock tm x blockLength interval tape ≤
        centerBlock tm x blockLength (interval + 1) tape + 1 := by
  have hnextTime :
      timeBlockStart blockLength (interval + 1) =
        timeBlockStart blockLength interval + blockLength := by
    simp [timeBlockStart, Nat.add_mul]
  have hdistance :=
    configurationAt_head_distance_internal tm x
      (timeBlockStart blockLength interval) blockLength tape
  unfold centerBlock TM.activeBlock headBlock
  rw [hnextTime]
  exact
    ⟨blockIndex_le_succ_of_le_add_blockLength_internal
        hpositive hdistance.1,
      blockIndex_le_succ_of_le_add_blockLength_internal
        hpositive hdistance.2⟩

theorem mem_trajectoryFailures_internal
    {guess : CenterGuess workTapeCount horizon}
    {trajectory : TapeIndex workTapeCount → ℕ → ℕ}
    {checkpoint :
      Fin (horizon + 1) × TapeIndex workTapeCount} :
    checkpoint ∈ guess.trajectoryFailures trajectory ↔
      guess.derivedCenter checkpoint.2 checkpoint.1.val ≠
        some (trajectory checkpoint.2 checkpoint.1.val) := by
  simp [CenterGuess.trajectoryFailures]

theorem mem_failureTimes_internal
    {guess : CenterGuess workTapeCount horizon}
    {trajectory : TapeIndex workTapeCount → ℕ → ℕ}
    {interval : Fin (horizon + 1)} :
    interval ∈ guess.failureTimes trajectory ↔
      ∃ tape : TapeIndex workTapeCount,
        guess.derivedCenter tape interval.val ≠
          some (trajectory tape interval.val) := by
  simp [CenterGuess.failureTimes]

theorem isValidFor_iff_internal
    {guess : CenterGuess workTapeCount horizon}
    {trajectory : TapeIndex workTapeCount → ℕ → ℕ} :
    guess.IsValidFor trajectory ↔
      ∀ (interval : Fin (horizon + 1))
          (tape : TapeIndex workTapeCount),
        guess.derivedCenter tape interval.val =
          some (trajectory tape interval.val) := by
  constructor
  · intro hvalid interval tape
    have hnotmem :
        (interval, tape) ∉ guess.trajectoryFailures trajectory := by
      rw [hvalid]
      simp
    by_contra hne
    exact hnotmem (mem_trajectoryFailures_internal.mpr hne)
  · intro htrajectory
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨checkpoint, hmem⟩
    exact (mem_trajectoryFailures_internal.mp hmem)
      (htrajectory checkpoint.1 checkpoint.2)

theorem not_isValidFor_has_firstFailure_internal
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
              some (trajectory earlierTape earlier.val) := by
  unfold CenterGuess.IsValidFor at hinvalid
  have hcheckpoint :
      (guess.trajectoryFailures trajectory).Nonempty :=
    Finset.nonempty_of_ne_empty hinvalid
  obtain ⟨checkpoint, hcheckpoint⟩ := hcheckpoint
  have htime :
      checkpoint.1 ∈ guess.failureTimes trajectory :=
    mem_failureTimes_internal.mpr
      ⟨checkpoint.2,
        mem_trajectoryFailures_internal.mp hcheckpoint⟩
  have htimes :
      (guess.failureTimes trajectory).Nonempty :=
    ⟨checkpoint.1, htime⟩
  let first := (guess.failureTimes trajectory).min' htimes
  have hfirst :
      first ∈ guess.failureTimes trajectory := by
    exact Finset.min'_mem _ _
  obtain ⟨tape, htape⟩ :=
    mem_failureTimes_internal.mp hfirst
  refine ⟨first, tape, ?_, htape, ?_⟩
  · simp [CenterGuess.firstFailure?, htimes, first]
  · intro earlier hearlier earlierTape
    by_contra hearlierFailure
    have hearlierMem :
        earlier ∈ guess.failureTimes trajectory :=
      mem_failureTimes_internal.mpr
        ⟨earlierTape, hearlierFailure⟩
    have hminimum : first ≤ earlier :=
      Finset.min'_le _ _ hearlierMem
    omega

theorem priorIntervals_eq_internal
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon) (tape : TapeIndex workTapeCount)
    (requested : ℕ)
    (hvalid : guess.IsValidFor
      (actualCenterTrajectory tm x blockLength)) :
    guess.priorIntervals tape requested interval.val =
      NeighborhoodGraph.priorIntervals tm x blockLength tape
        requested interval.val := by
  ext previous
  have hcenter := isValidFor_iff_internal.mp hvalid
    ⟨previous.val, by omega⟩ tape
  simp only [CenterGuess.priorIntervals,
    NeighborhoodGraph.priorIntervals, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [hcenter]
  simp [actualCenterTrajectory]

theorem previousInterval_eq_internal
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon) (tape : TapeIndex workTapeCount)
    (requested : ℕ)
    (hvalid : guess.IsValidFor
      (actualCenterTrajectory tm x blockLength)) :
    guess.previousInterval tape requested interval.val =
      NeighborhoodGraph.previousInterval tm x blockLength tape
        requested interval.val := by
  unfold CenterGuess.previousInterval
    NeighborhoodGraph.previousInterval
  rw [priorIntervals_eq_internal
    guess tm x blockLength interval tape requested hvalid]

theorem contentPredecessor?_eq_internal
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon) (tape : TapeIndex workTapeCount)
    (slot : Slot)
    (hvalid : guess.IsValidFor
      (actualCenterTrajectory tm x blockLength)) :
    guess.contentPredecessor? interval tape slot =
      some (NeighborhoodGraph.contentPredecessor
        tm x blockLength interval.val tape slot) := by
  have hcurrent :
      guess.derivedCenter tape interval.val =
        some (centerBlock tm x blockLength interval.val tape) := by
    simpa only [actualCenterTrajectory] using
      isValidFor_iff_internal.mp hvalid
        ⟨interval.val, by omega⟩ tape
  let requested :=
    neighborBlock
      (centerBlock tm x blockLength interval.val tape) slot
  have hprevious := previousInterval_eq_internal
    guess tm x blockLength interval tape requested hvalid
  unfold CenterGuess.contentPredecessor?
  simp only [hcurrent]
  rw [hprevious]
  unfold NeighborhoodGraph.contentPredecessor
  simp only [NeighborhoodGraph.requestedBlock]
  generalize hp :
    NeighborhoodGraph.previousInterval tm x blockLength tape
      requested interval.val = previousResult
  cases previousResult with
  | none => rfl
  | some previous =>
      have hpreviousCenter :
          guess.derivedCenter tape previous.val =
            some (centerBlock
              tm x blockLength previous.val tape) := by
        simpa only [actualCenterTrajectory] using
          isValidFor_iff_internal.mp hvalid
            ⟨previous.val, by omega⟩ tape
      simp only [hpreviousCenter]

theorem chronologicalPredecessor?_eq_internal
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon) (tape : TapeIndex workTapeCount)
    (hvalid : guess.IsValidFor
      (actualCenterTrajectory tm x blockLength)) :
    guess.chronologicalPredecessor? interval tape =
      some (NeighborhoodGraph.chronologicalPredecessor
        tm x blockLength interval.val tape) := by
  have hcurrent :
      guess.derivedCenter tape interval.val =
        some (centerBlock tm x blockLength interval.val tape) := by
    simpa only [actualCenterTrajectory] using
      isValidFor_iff_internal.mp hvalid
        ⟨interval.val, by omega⟩ tape
  unfold CenterGuess.chronologicalPredecessor?
  simp only [hcurrent]
  cases htime : interval.val with
  | zero =>
      simp [NeighborhoodGraph.chronologicalPredecessor]
  | succ previous =>
      simp [NeighborhoodGraph.chronologicalPredecessor]

theorem predecessor?_eq_internal
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon)
    (index : PredecessorIndex workTapeCount)
    (hvalid : guess.IsValidFor
      (actualCenterTrajectory tm x blockLength)) :
    guess.predecessor? interval index =
      some (NeighborhoodGraph.predecessor
        tm x blockLength interval.val index) := by
  cases index with
  | mk kind tape =>
      cases kind with
      | content slot =>
          exact contentPredecessor?_eq_internal
            guess tm x blockLength interval tape slot hvalid
      | chronological =>
          exact chronologicalPredecessor?_eq_internal
            guess tm x blockLength interval tape hvalid

theorem predecessorAt?_eq_internal
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon)
    (index : Fin (4 * (workTapeCount + 2)))
    (hvalid : guess.IsValidFor
      (actualCenterTrajectory tm x blockLength)) :
    guess.predecessorAt? interval index =
      some (NeighborhoodGraph.predecessorAt
        tm x blockLength interval.val index) := by
  unfold CenterGuess.predecessorAt?
    NeighborhoodGraph.predecessorAt
  exact predecessor?_eq_internal guess tm x blockLength interval
    ((predecessorIndexEquiv workTapeCount).symm index) hvalid

private theorem priorIntervals_eq_of_prefix_internal
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon) (tape : TapeIndex workTapeCount)
    (requested : ℕ)
    (hprefix :
      ∀ boundary : Fin (horizon + 1),
        boundary.val ≤ interval.val →
          ∀ currentTape : TapeIndex workTapeCount,
            guess.derivedCenter currentTape boundary.val =
              some (actualCenterTrajectory
                tm x blockLength currentTape boundary.val)) :
    guess.priorIntervals tape requested interval.val =
      NeighborhoodGraph.priorIntervals tm x blockLength tape
        requested interval.val := by
  ext previous
  have hcenter := hprefix
    ⟨previous.val, by omega⟩
      (show previous.val ≤ interval.val from
        Nat.le_of_lt previous.isLt) tape
  simp only [CenterGuess.priorIntervals,
    NeighborhoodGraph.priorIntervals, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [hcenter]
  simp [actualCenterTrajectory]

private theorem previousInterval_eq_of_prefix_internal
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon) (tape : TapeIndex workTapeCount)
    (requested : ℕ)
    (hprefix :
      ∀ boundary : Fin (horizon + 1),
        boundary.val ≤ interval.val →
          ∀ currentTape : TapeIndex workTapeCount,
            guess.derivedCenter currentTape boundary.val =
              some (actualCenterTrajectory
                tm x blockLength currentTape boundary.val)) :
    guess.previousInterval tape requested interval.val =
      NeighborhoodGraph.previousInterval tm x blockLength tape
        requested interval.val := by
  unfold CenterGuess.previousInterval
    NeighborhoodGraph.previousInterval
  rw [priorIntervals_eq_of_prefix_internal
    guess tm x blockLength interval tape requested hprefix]

private theorem contentPredecessor?_eq_of_prefix_internal
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon) (tape : TapeIndex workTapeCount)
    (slot : Slot)
    (hprefix :
      ∀ boundary : Fin (horizon + 1),
        boundary.val ≤ interval.val →
          ∀ currentTape : TapeIndex workTapeCount,
            guess.derivedCenter currentTape boundary.val =
              some (actualCenterTrajectory
                tm x blockLength currentTape boundary.val)) :
    guess.contentPredecessor? interval tape slot =
      some (NeighborhoodGraph.contentPredecessor
        tm x blockLength interval.val tape slot) := by
  have hcurrent :
      guess.derivedCenter tape interval.val =
        some (centerBlock tm x blockLength interval.val tape) := by
    simpa only [actualCenterTrajectory] using
      hprefix ⟨interval.val, by omega⟩ le_rfl tape
  let requested :=
    neighborBlock
      (centerBlock tm x blockLength interval.val tape) slot
  have hprevious := previousInterval_eq_of_prefix_internal
    guess tm x blockLength interval tape requested hprefix
  unfold CenterGuess.contentPredecessor?
  simp only [hcurrent]
  rw [hprevious]
  unfold NeighborhoodGraph.contentPredecessor
  simp only [NeighborhoodGraph.requestedBlock]
  generalize hp :
    NeighborhoodGraph.previousInterval tm x blockLength tape
      requested interval.val = previousResult
  cases previousResult with
  | none => rfl
  | some previous =>
      have hpreviousCenter :
          guess.derivedCenter tape previous.val =
            some (centerBlock
              tm x blockLength previous.val tape) := by
        simpa only [actualCenterTrajectory] using
          hprefix ⟨previous.val, by omega⟩
            (show previous.val ≤ interval.val from
              Nat.le_of_lt previous.isLt) tape
      simp only [hpreviousCenter]

private theorem chronologicalPredecessor?_eq_of_prefix_internal
    (guess : CenterGuess workTapeCount horizon)
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (interval : Fin horizon) (tape : TapeIndex workTapeCount)
    (hprefix :
      ∀ boundary : Fin (horizon + 1),
        boundary.val ≤ interval.val →
          ∀ currentTape : TapeIndex workTapeCount,
            guess.derivedCenter currentTape boundary.val =
              some (actualCenterTrajectory
                tm x blockLength currentTape boundary.val)) :
    guess.chronologicalPredecessor? interval tape =
      some (NeighborhoodGraph.chronologicalPredecessor
        tm x blockLength interval.val tape) := by
  have hcurrent :
      guess.derivedCenter tape interval.val =
        some (centerBlock tm x blockLength interval.val tape) := by
    simpa only [actualCenterTrajectory] using
      hprefix ⟨interval.val, by omega⟩ le_rfl tape
  unfold CenterGuess.chronologicalPredecessor?
  simp only [hcurrent]
  cases htime : interval.val with
  | zero =>
      simp [NeighborhoodGraph.chronologicalPredecessor]
  | succ previous =>
      simp [NeighborhoodGraph.chronologicalPredecessor]

theorem predecessor?_eq_of_prefix_internal
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
        tm x blockLength interval.val index) := by
  cases index with
  | mk kind tape =>
      cases kind with
      | content slot =>
          exact contentPredecessor?_eq_of_prefix_internal
            guess tm x blockLength interval tape slot hprefix
      | chronological =>
          exact chronologicalPredecessor?_eq_of_prefix_internal
            guess tm x blockLength interval tape hprefix

theorem predecessorAt?_eq_of_prefix_internal
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
        tm x blockLength interval.val index) := by
  unfold CenterGuess.predecessorAt?
    NeighborhoodGraph.predecessorAt
  exact predecessor?_eq_of_prefix_internal
    guess tm x blockLength interval
      ((predecessorIndexEquiv workTapeCount).symm index) hprefix

theorem actualCenterGuess_derivedCenter_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon interval : ℕ)
    (tape : TapeIndex workTapeCount)
    (hpositive : 0 < blockLength)
    (hinterval : interval ≤ horizon) :
    (actualCenterGuess tm x blockLength horizon).derivedCenter
        tape interval =
      some (centerBlock tm x blockLength interval tape) := by
  induction interval with
  | zero => rfl
  | succ interval ih =>
      have hlt : interval < horizon := by omega
      rw [CenterGuess.derivedCenter]
      simp only [hlt, dite_true]
      rw [ih (Nat.le_of_lt hlt)]
      exact centerMove_apply_between_internal
        (centerBlock_adjacent_internal
          tm x blockLength interval tape hpositive)

theorem actualCenterGuess_isValidFor_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ)
    (hpositive : 0 < blockLength) :
    (actualCenterGuess tm x blockLength horizon).IsValidFor
      (actualCenterTrajectory tm x blockLength) := by
  apply isValidFor_iff_internal.mpr
  intro interval tape
  simpa only [actualCenterTrajectory] using
    actualCenterGuess_derivedCenter_internal
      tm x blockLength horizon interval.val tape hpositive (by omega)

end Internal

end Guess

end NeighborhoodGraph

end TimeSpaceSimulation

end Complexity
