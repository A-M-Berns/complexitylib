/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Contents
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LocalSimulation.Defs

/-!
# Local time-block simulation internals

This file proves a lockstep noninterference theorem. If two configurations
agree on the state, heads, and active block of every tape, one transition
preserves that agreement while the heads remain in those blocks. Induction
then shows that a block-respecting time block can be replayed from any locally
agreeing configuration.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace LocalSimulation

namespace Internal

theorem tapeBlockAgreement_read_eq_internal
    {blockLength block : ℕ} {left right : Tape}
    (h : TapeBlockAgreement blockLength block left right)
    (hleft : InBlock blockLength block left.head) :
    left.read = right.read := by
  unfold Tape.read
  rw [h.head_eq]
  apply h.cells_eq
  rwa [← h.head_eq]

theorem tapeBlockAgreement_move_internal
    {blockLength block : ℕ} {left right : Tape}
    (h : TapeBlockAgreement blockLength block left right)
    (direction : Dir3) :
    TapeBlockAgreement blockLength block
      (left.move direction) (right.move direction) := by
  constructor
  · cases direction <;> simp [Tape.move, h.head_eq]
  · intro position hposition
    simpa only [Tape.move_cells] using
      h.cells_eq position hposition

theorem tapeBlockAgreement_writeAndMove_internal
    {blockLength block : ℕ} {left right : Tape}
    (h : TapeBlockAgreement blockLength block left right)
    (symbol : Γ) (direction : Dir3) :
    TapeBlockAgreement blockLength block
      (left.writeAndMove symbol direction)
      (right.writeAndMove symbol direction) := by
  have hwrite : TapeBlockAgreement blockLength block
      (left.write symbol) (right.write symbol) := by
    constructor
    · simpa only [Tape.write_head] using h.head_eq
    · intro position hposition
      by_cases hzero : left.head = 0
      · have hrightzero : right.head = 0 := by
          rwa [← h.head_eq]
        simp [Tape.write, hzero, hrightzero,
          h.cells_eq position hposition]
      · have hrightzero : right.head ≠ 0 := by
          rwa [← h.head_eq]
        simp only [Tape.write, hzero, hrightzero, if_false]
        change Function.update left.cells left.head symbol position =
          Function.update right.cells right.head symbol position
        rw [h.head_eq]
        by_cases hpositionHead : position = right.head
        · subst position
          simp
        · rw [Function.update_of_ne hpositionHead]
          rw [Function.update_of_ne hpositionHead]
          exact h.cells_eq position hposition
  exact tapeBlockAgreement_move_internal hwrite direction

theorem trace_one_cfgBlockAgreement_internal
    (tm : TM workTapeCount) (blockLength : ℕ)
    (blocks : TapeIndex workTapeCount → ℕ)
    (left right : Cfg workTapeCount tm.Q)
    (h : CfgBlockAgreement blockLength blocks left right)
    (hinput :
      InBlock blockLength (blocks (TapeIndex.input workTapeCount))
        left.input.head)
    (hwork : ∀ index,
      InBlock blockLength (blocks (TapeIndex.work index))
        (left.work index).head)
    (houtput :
      InBlock blockLength (blocks (TapeIndex.output workTapeCount))
        left.output.head) :
    CfgBlockAgreement blockLength blocks
      (tm.toNTM.trace 1 (fun _ => false) left)
      (tm.toNTM.trace 1 (fun _ => false) right) := by
  have hinputRead : left.input.read = right.input.read :=
    tapeBlockAgreement_read_eq_internal h.input hinput
  have hworkRead :
      (fun index => (left.work index).read) =
        (fun index => (right.work index).read) := by
    funext index
    exact tapeBlockAgreement_read_eq_internal
      (h.work index) (hwork index)
  have houtputRead : left.output.read = right.output.read :=
    tapeBlockAgreement_read_eq_internal h.output houtput
  by_cases hhalt : left.state = tm.qhalt
  · have hhaltRight : right.state = tm.qhalt := by
      rw [← h.state_eq]
      exact hhalt
    simpa [NTM.trace, TM.toNTM, hhalt, hhaltRight] using h
  · have hhaltRight : right.state ≠ tm.qhalt := by
      intro hright
      apply hhalt
      rw [h.state_eq]
      exact hright
    simp only [NTM.trace, TM.toNTM, hhalt, hhaltRight, if_false]
    rw [← h.state_eq, ← hinputRead, ← hworkRead, ← houtputRead]
    constructor
    · rfl
    · exact tapeBlockAgreement_move_internal h.input _
    · intro index
      exact tapeBlockAgreement_writeAndMove_internal
        (h.work index) _ _
    · exact tapeBlockAgreement_writeAndMove_internal h.output _ _

theorem configurationAt_trace_cfgBlockAgreement_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength start steps : ℕ)
    (blocks : TapeIndex workTapeCount → ℕ)
    (seed : Cfg workTapeCount tm.Q)
    (hstart : CfgBlockAgreement blockLength blocks
      (tm.configurationAt x start) seed)
    (hinput : ∀ offset, offset < steps →
      InBlock blockLength (blocks (TapeIndex.input workTapeCount))
        (tm.configurationAt x (start + offset)).input.head)
    (hwork : ∀ offset, offset < steps → ∀ index,
      InBlock blockLength (blocks (TapeIndex.work index))
        ((tm.configurationAt x (start + offset)).work index).head)
    (houtput : ∀ offset, offset < steps →
      InBlock blockLength (blocks (TapeIndex.output workTapeCount))
        (tm.configurationAt x (start + offset)).output.head) :
    CfgBlockAgreement blockLength blocks
      (tm.configurationAt x (start + steps))
      (tm.toNTM.trace steps (fun _ => false) seed) := by
  induction steps with
  | zero => simpa [NTM.trace] using hstart
  | succ steps ih =>
      rw [Nat.add_succ, TM.configurationAt_succ]
      rw [show tm.toNTM.trace (steps + 1) (fun _ => false) seed =
          tm.toNTM.trace 1 (fun _ => false)
            (tm.toNTM.trace steps (fun _ => false) seed) by
        exact NTM.trace_snoc _ _ _ _]
      apply trace_one_cfgBlockAgreement_internal
      · apply ih
        · intro offset hoffset
          exact hinput offset (Nat.lt_succ_of_lt hoffset)
        · intro offset hoffset index
          exact hwork offset (Nat.lt_succ_of_lt hoffset) index
        · intro offset hoffset
          exact houtput offset (Nat.lt_succ_of_lt hoffset)
      · exact hinput steps (Nat.lt_succ_self steps)
      · exact hwork steps (Nat.lt_succ_self steps)
      · exact houtput steps (Nat.lt_succ_self steps)

theorem timeBlock_trace_cfgBlockAgreement_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (seed : Cfg workTapeCount tm.Q)
    (hrespecting : tm.BlockRespectingOnInput x blockLength)
    (hstart : CfgBlockAgreement blockLength
      (activeBlocks tm x blockLength timeBlock)
      (tm.configurationAt x
        (timeBlockStart blockLength timeBlock))
      seed) :
    CfgBlockAgreement blockLength
      (activeBlocks tm x blockLength timeBlock)
      (tm.configurationAt x
        (timeBlockStart blockLength (timeBlock + 1)))
      (tm.toNTM.trace blockLength (fun _ => false) seed) := by
  have hagreement :=
    configurationAt_trace_cfgBlockAgreement_internal
      tm x blockLength (timeBlockStart blockLength timeBlock)
        blockLength (activeBlocks tm x blockLength timeBlock)
        seed hstart
  rw [show timeBlockStart blockLength timeBlock + blockLength =
      timeBlockStart blockLength (timeBlock + 1) by
        simp [timeBlockStart, Nat.add_mul]] at hagreement
  apply hagreement
  · intro offset hoffset
    simpa only [activeBlocks, tapeAt_input] using
      hrespecting.head_in_activeBlock
        tm x blockLength timeBlock ⟨offset, hoffset⟩
          (TapeIndex.input workTapeCount)
  · intro offset hoffset index
    simpa only [activeBlocks, tapeAt_work] using
      hrespecting.head_in_activeBlock
        tm x blockLength timeBlock ⟨offset, hoffset⟩
          (TapeIndex.work index)
  · intro offset hoffset
    simpa only [activeBlocks, tapeAt_output] using
      hrespecting.head_in_activeBlock
        tm x blockLength timeBlock ⟨offset, hoffset⟩
          (TapeIndex.output workTapeCount)

end Internal

end LocalSimulation

end ComputationGraph

end TimeSpaceSimulation

end Complexity
