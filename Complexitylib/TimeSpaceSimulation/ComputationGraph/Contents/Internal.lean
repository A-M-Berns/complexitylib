/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Trace
import Complexitylib.TimeSpaceSimulation.ComputationGraph
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Contents.Defs

/-!
# Computation-graph tape-block content internals

This file proves that cells outside the current head are unchanged, lifts the
one-step fact across inactive time blocks, and uses the greatest-prior-visit
oracle to justify computation-graph content edges.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace Internal

theorem writeAndMove_cells_of_ne_internal
    (tape : Tape) (symbol : Γ) (direction : Dir3)
    {position : ℕ} (hne : position ≠ tape.head) :
    (tape.writeAndMove symbol direction).cells position =
      tape.cells position := by
  rw [Tape.move_cells]
  unfold Tape.write
  split
  · rfl
  · change Function.update tape.cells tape.head symbol position =
      tape.cells position
    exact Function.update_of_ne hne symbol tape.cells

theorem tapeAt_trace_one_cells_of_ne_internal
    (tm : NTM workTapeCount) (cfg : Cfg workTapeCount tm.Q)
    (choice : Bool) (tape : TapeIndex workTapeCount) (position : ℕ)
    (hne : position ≠ (tapeAt cfg tape).head) :
    (tapeAt (tm.trace 1 (fun _ => choice) cfg) tape).cells position =
      (tapeAt cfg tape).cells position := by
  by_cases hinput : tape.val = 0
  · have htape : tape = TapeIndex.input workTapeCount := Fin.ext hinput
    rw [htape] at hne ⊢
    simp only [tapeAt_input]
    by_cases hhalt : cfg.state = tm.qhalt
    · simp [NTM.trace, hhalt]
    · simp [NTM.trace, hhalt, Tape.move_cells]
  · by_cases houtput : tape.val = workTapeCount + 1
    · have htape : tape = TapeIndex.output workTapeCount := Fin.ext houtput
      rw [htape] at hne ⊢
      simp only [tapeAt_output] at hne ⊢
      by_cases hhalt : cfg.state = tm.qhalt
      · simp [NTM.trace, hhalt]
      · simp only [NTM.trace, hhalt, if_false]
        exact writeAndMove_cells_of_ne_internal _ _ _ hne
    · let index : Fin workTapeCount :=
        ⟨tape.val - 1, by omega⟩
      have htape : tape = TapeIndex.work index := by
        apply Fin.ext
        simp only [TapeIndex.work, index]
        omega
      rw [htape] at hne ⊢
      simp only [tapeAt_work] at hne ⊢
      by_cases hhalt : cfg.state = tm.qhalt
      · simp [NTM.trace, hhalt]
      · simp only [NTM.trace, hhalt, if_false]
        exact writeAndMove_cells_of_ne_internal _ _ _ hne

theorem configurationAt_succ_internal
    (tm : TM workTapeCount) (x : List Bool) (time : ℕ) :
    tm.configurationAt x (time + 1) =
      tm.toNTM.trace 1 (fun _ => false)
        (tm.configurationAt x time) := by
  unfold TM.configurationAt
  rw [NTM.trace_snoc]

theorem configurationAt_cell_succ_of_ne_internal
    (tm : TM workTapeCount) (x : List Bool) (time : ℕ)
    (tape : TapeIndex workTapeCount) (position : ℕ)
    (hne : position ≠
      (tapeAt (tm.configurationAt x time) tape).head) :
    (tapeAt (tm.configurationAt x (time + 1)) tape).cells position =
      (tapeAt (tm.configurationAt x time) tape).cells position := by
  rw [configurationAt_succ_internal]
  exact tapeAt_trace_one_cells_of_ne_internal _ _ _ _ _ hne

theorem configurationAt_cells_add_eq_of_avoids_internal
    (tm : TM workTapeCount) (x : List Bool)
    (start steps : ℕ) (tape : TapeIndex workTapeCount) (position : ℕ)
    (havoid : ∀ offset, offset < steps →
      position ≠
        (tapeAt (tm.configurationAt x (start + offset)) tape).head) :
    (tapeAt (tm.configurationAt x (start + steps)) tape).cells position =
      (tapeAt (tm.configurationAt x start) tape).cells position := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Nat.add_succ]
      calc
        (tapeAt
            (tm.configurationAt x (start + steps + 1)) tape).cells position =
            (tapeAt
              (tm.configurationAt x (start + steps)) tape).cells position := by
          exact configurationAt_cell_succ_of_ne_internal
            tm x (start + steps) tape position
              (havoid steps (Nat.lt_succ_self steps))
        _ =
            (tapeAt (tm.configurationAt x start) tape).cells position := by
          apply ih
          intro offset hoffset
          exact havoid offset (Nat.lt_succ_of_lt hoffset)

theorem blockOffset_in_block_internal
    (blockLength block : ℕ) (offset : Fin blockLength) :
    InBlock blockLength block
      (block * blockLength + offset.val) := by
  unfold InBlock
  constructor
  · omega
  · rw [Nat.add_mul]
    omega

theorem blockIndex_eq_of_inBlock_internal
    {blockLength block position : ℕ}
    (h : InBlock blockLength block position) :
    blockIndex blockLength position = block := by
  exact Nat.div_eq_of_lt_le h.1 h.2

theorem blockContentsAt_add_eq_of_headBlock_ne_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength block start steps : ℕ)
    (tape : TapeIndex workTapeCount)
    (havoid : ∀ offset, offset < steps →
      headBlock blockLength
        (tm.configurationAt x (start + offset)) tape ≠ block) :
    blockContentsAt tm x blockLength (start + steps) tape block =
      blockContentsAt tm x blockLength start tape block := by
  funext offset
  apply configurationAt_cells_add_eq_of_avoids_internal
  intro time htime heq
  have hposition :
      blockIndex blockLength
          (block * blockLength + offset.val) = block :=
    blockIndex_eq_of_inBlock_internal
      (blockOffset_in_block_internal blockLength block offset)
  have hhead :
      headBlock blockLength
          (tm.configurationAt x (start + time)) tape = block := by
    unfold headBlock
    rw [← heq]
    exact hposition
  exact havoid time htime hhead

theorem inactive_timeBlock_preserves_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock block : ℕ)
    (tape : TapeIndex workTapeCount)
    (h : tm.BlockRespectingOnInput x blockLength)
    (hinactive :
      tm.activeBlock x blockLength timeBlock tape ≠ block) :
    blockContentsAt tm x blockLength
        (timeBlockStart blockLength (timeBlock + 1)) tape block =
      blockContentsAt tm x blockLength
        (timeBlockStart blockLength timeBlock) tape block := by
  have hpersist :=
    blockContentsAt_add_eq_of_headBlock_ne_internal
      tm x blockLength block
        (timeBlockStart blockLength timeBlock) blockLength tape
  rw [show timeBlockStart blockLength timeBlock + blockLength =
      timeBlockStart blockLength (timeBlock + 1) by
        simp [timeBlockStart, Nat.add_mul]] at hpersist
  apply hpersist
  intro offset hoffset
  have hhead :=
    h.headBlock tm x blockLength timeBlock
      ⟨offset, hoffset⟩ tape
  intro heq
  apply hinactive
  rw [← hhead]
  exact heq

theorem inactive_timeBlocks_preserve_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength first count block : ℕ)
    (tape : TapeIndex workTapeCount)
    (h : tm.BlockRespectingOnInput x blockLength)
    (hinactive : ∀ offset, offset < count →
      tm.activeBlock x blockLength (first + offset) tape ≠ block) :
    blockContentsAt tm x blockLength
        (timeBlockStart blockLength (first + count)) tape block =
      blockContentsAt tm x blockLength
        (timeBlockStart blockLength first) tape block := by
  induction count with
  | zero => simp
  | succ count ih =>
      calc
        blockContentsAt tm x blockLength
            (timeBlockStart blockLength (first + (count + 1)))
            tape block =
            blockContentsAt tm x blockLength
              (timeBlockStart blockLength (first + count))
              tape block := by
          have hpersist :=
            inactive_timeBlock_preserves_internal
              tm x blockLength (first + count) block tape h
                (hinactive count (Nat.lt_succ_self count))
          simpa [Nat.add_assoc] using hpersist
        _ =
            blockContentsAt tm x blockLength
              (timeBlockStart blockLength first) tape block := by
          apply ih
          intro offset hoffset
          exact hinactive offset (Nat.lt_succ_of_lt hoffset)

theorem nodeBlockContents_contentPredecessor_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount)
    (h : tm.BlockRespectingOnInput x blockLength) :
    nodeBlockContents tm x blockLength
        (contentPredecessor tm x blockLength timeBlock tape) =
      startBlockContents tm x blockLength tape timeBlock := by
  generalize hprevious :
    previousVisit
      (activeTrajectory tm x blockLength tape) timeBlock = result
  cases result with
  | none =>
      rw [show contentPredecessor tm x blockLength timeBlock tape =
          .source tape
            (activeTrajectory tm x blockLength tape timeBlock) by
        simp [contentPredecessor, hprevious]]
      simp only [nodeBlockContents]
      unfold sourceBlockContents startBlockContents
      symm
      have hpersist :=
        inactive_timeBlocks_preserve_internal
          tm x blockLength 0 timeBlock
            (activeTrajectory tm x blockLength tape timeBlock) tape h
      simpa [activeTrajectory, timeBlockStart] using hpersist (by
        intro offset hoffset
        simpa [activeTrajectory] using
          previousVisit_eq_none_iff.mp hprevious offset hoffset)
  | some previous =>
      rw [show contentPredecessor tm x blockLength timeBlock tape =
          .computation tape previous by
        simp [contentPredecessor, hprevious]]
      have hprevious_lt : previous < timeBlock :=
        previousVisit_some_lt hprevious
      have hsame :
          activeTrajectory tm x blockLength tape previous =
            activeTrajectory tm x blockLength tape timeBlock :=
        previousVisit_some_active hprevious
      simp only [nodeBlockContents]
      unfold computedBlockContents startBlockContents
      change tm.activeBlock x blockLength previous tape =
        tm.activeBlock x blockLength timeBlock tape at hsame
      rw [hsame]
      symm
      let count := timeBlock - (previous + 1)
      have hpersist :=
        inactive_timeBlocks_preserve_internal
          tm x blockLength (previous + 1) count
            (activeTrajectory tm x blockLength tape timeBlock) tape h
      have hsum : previous + 1 + count = timeBlock := by
        dsimp only [count]
        omega
      rw [hsum] at hpersist
      exact hpersist (by
        intro offset hoffset hactive
        have hcandidate_lt :
            previous + 1 + offset < timeBlock := by
          dsimp only [count] at hoffset
          omega
        have hcandidate_le :=
          previousVisit_some_maximal hprevious hcandidate_lt (by
              simpa [activeTrajectory] using hactive)
        omega)

end Internal

end ComputationGraph

end TimeSpaceSimulation

end Complexity
