/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Internal
import Complexitylib.TimeSpaceSimulation.BlockRespecting.Defs

/-!
# Block-respecting computation internals

This file proves the arithmetic and trace facts underlying the public
block-respecting interface.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Internal

variable {workTapeCount : ℕ} {Q : Type}

theorem tapeAt_input_internal (cfg : Cfg workTapeCount Q) :
    tapeAt cfg (TapeIndex.input workTapeCount) = cfg.input := by
  simp [tapeAt, TapeIndex.input]

theorem tapeAt_work_internal (cfg : Cfg workTapeCount Q)
    (index : Fin workTapeCount) :
    tapeAt cfg (TapeIndex.work index) = cfg.work index := by
  have hne : index.val ≠ workTapeCount := Nat.ne_of_lt index.isLt
  simp [tapeAt, TapeIndex.work, hne]

theorem tapeAt_output_internal (cfg : Cfg workTapeCount Q) :
    tapeAt cfg (TapeIndex.output workTapeCount) = cfg.output := by
  simp [tapeAt, TapeIndex.output]

theorem position_in_ownBlock_internal (blockLength position : ℕ)
    (hpositive : 0 < blockLength) :
    InBlock blockLength (blockIndex blockLength position) position := by
  constructor
  · simpa [blockIndex, Nat.mul_comm] using
      Nat.div_mul_le_self position blockLength
  · simpa [blockIndex, Nat.mul_comm] using
      Nat.lt_mul_div_succ position hpositive

theorem blockContents_ownBlock_internal (tape : Tape)
    (blockLength position : ℕ) (hpositive : 0 < blockLength) :
    blockContents tape blockLength (blockIndex blockLength position)
        ⟨position % blockLength, Nat.mod_lt _ hpositive⟩ =
      tape.cells position := by
  simp [blockContents, blockIndex, Nat.div_add_mod']

theorem blockContents_head_internal (tape : Tape)
    (blockLength : ℕ) (hpositive : 0 < blockLength) :
    blockContents tape blockLength (blockIndex blockLength tape.head)
        ⟨tape.head % blockLength, Nat.mod_lt _ hpositive⟩ =
      tape.read := by
  exact blockContents_ownBlock_internal
    tape blockLength tape.head hpositive

theorem configurationAt_zero_internal (tm : TM workTapeCount)
    (x : List Bool) :
    tm.configurationAt x 0 = tm.initCfg x := rfl

theorem configurationAt_reaches_internal (tm : TM workTapeCount)
    (x : List Bool) (time : ℕ) :
    tm.reaches (tm.initCfg x) (tm.configurationAt x time) := by
  exact tm.toNTM_trace_reaches
    (tm.initCfg x) time (fun _ => false)

theorem configurationAt_of_reachesIn_internal
    (tm : TM workTapeCount) {x : List Bool}
    {cfg : Cfg workTapeCount tm.Q} {haltTime horizon : ℕ}
    (hreach : tm.reachesIn haltTime (tm.initCfg x) cfg)
    (hhalt : tm.halted cfg) (hle : haltTime ≤ horizon) :
    tm.configurationAt x horizon = cfg := by
  exact tm.toNTM_trace_of_reachesIn
    hreach hhalt hle (fun _ => false)

theorem blockRespectingOnInput_blockLength_pos_internal
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength) :
    0 < blockLength :=
  h.1

theorem blockRespectingOnInput_headBlock_internal
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength)
    (timeBlock : ℕ) (offset : Fin blockLength)
    (tape : TapeIndex workTapeCount) :
    headBlock blockLength
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock + offset.val))
        tape =
      tm.activeBlock x blockLength timeBlock tape :=
  h.2 timeBlock offset tape

theorem blockRespectingOnInput_head_in_activeBlock_internal
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength)
    (timeBlock : ℕ) (offset : Fin blockLength)
    (tape : TapeIndex workTapeCount) :
    InBlock blockLength (tm.activeBlock x blockLength timeBlock tape)
      (tapeAt
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock + offset.val))
        tape).head := by
  have hown :=
    position_in_ownBlock_internal blockLength
      (tapeAt
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock + offset.val))
        tape).head
      h.1
  change
    InBlock blockLength
      (headBlock blockLength
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock + offset.val))
        tape)
      _ at hown
  rw [blockRespectingOnInput_headBlock_internal
    tm x blockLength h timeBlock offset tape] at hown
  exact hown

theorem blockRespectingOnInput_headBlock_at_time_internal
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength)
    (time : ℕ) (tape : TapeIndex workTapeCount) :
    headBlock blockLength (tm.configurationAt x time) tape =
      tm.activeBlock x blockLength (time / blockLength) tape := by
  have hoffset : time % blockLength < blockLength :=
    Nat.mod_lt _ h.1
  have hres :=
    blockRespectingOnInput_headBlock_internal tm x blockLength h
      (time / blockLength) ⟨time % blockLength, hoffset⟩ tape
  rw [show
    timeBlockStart blockLength (time / blockLength) +
        time % blockLength = time by
      simp [timeBlockStart, Nat.div_add_mod']] at hres
  exact hres

theorem blockRespectingOnInput_head_in_timeBlock_internal
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength)
    (time : ℕ) (tape : TapeIndex workTapeCount) :
    InBlock blockLength
      (tm.activeBlock x blockLength (time / blockLength) tape)
      (tapeAt (tm.configurationAt x time) tape).head := by
  have hown :=
    position_in_ownBlock_internal blockLength
      (tapeAt (tm.configurationAt x time) tape).head h.1
  change
    InBlock blockLength
      (headBlock blockLength (tm.configurationAt x time) tape) _ at hown
  rw [blockRespectingOnInput_headBlock_at_time_internal
    tm x blockLength h time tape] at hown
  exact hown

theorem blockRespecting_onInput_internal
    (tm : TM workTapeCount) (blockLength : ℕ → ℕ)
    (h : tm.BlockRespecting blockLength) (x : List Bool) :
    tm.BlockRespectingOnInput x (blockLength x.length) :=
  h x

end Internal

end TimeSpaceSimulation

end Complexity
