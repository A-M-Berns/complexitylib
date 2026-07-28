/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Internal
import Complexitylib.Models.TuringMachine.Trace
import Complexitylib.TimeSpaceSimulation.BlockRespecting
import Complexitylib.TimeSpaceSimulation.Locality.Defs

/-!
# Three-block locality internals

This file proves symmetric head-displacement bounds, three-block residence,
and lockstep noninterference from three-block configuration agreement.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Locality

namespace Internal

theorem localityIntervalCount_le_iff_internal
    {time blockLength intervals : ℕ}
    (hpositive : 0 < blockLength) :
    localityIntervalCount time blockLength ≤ intervals ↔
      time ≤ blockLength * intervals :=
  ceilDiv_le_iff_le_mul hpositive

theorem time_le_blockLength_mul_localityIntervalCount_internal
    {time blockLength : ℕ} (hpositive : 0 < blockLength) :
    time ≤ blockLength * localityIntervalCount time blockLength :=
  (localityIntervalCount_le_iff_internal hpositive).mp le_rfl

theorem threeBlockLower_zero_internal (blockLength : ℕ) :
    threeBlockLower blockLength 0 = 0 := by
  simp [threeBlockLower]

theorem threeBlockUpper_zero_internal (blockLength : ℕ) :
    threeBlockUpper blockLength 0 = 2 * blockLength := by
  simp [threeBlockUpper]

theorem inThreeBlockNeighborhood_zero_iff_internal
    (blockLength position : ℕ) :
    InThreeBlockNeighborhood blockLength 0 position ↔
      position < 2 * blockLength := by
  simp [InThreeBlockNeighborhood, threeBlockLower,
    threeBlockUpper]

theorem inThreeBlockNeighborhood_iff_three_blocks_internal
    {blockLength centerBlock position : ℕ} :
    InThreeBlockNeighborhood blockLength centerBlock position ↔
      InBlock blockLength (centerBlock - 1) position ∨
        InBlock blockLength centerBlock position ∨
        InBlock blockLength (centerBlock + 1) position := by
  constructor
  · intro hneighborhood
    by_cases hleft : position < centerBlock * blockLength
    · left
      cases centerBlock with
      | zero => omega
      | succ centerBlock =>
          constructor
          · exact hneighborhood.1
          · simpa [InBlock] using hleft
    · by_cases hcenter :
          position < (centerBlock + 1) * blockLength
      · right
        left
        exact ⟨by omega, hcenter⟩
      · right
        right
        exact ⟨by omega, hneighborhood.2⟩
  · rintro (hleft | hcenter | hright)
    · constructor
      · exact hleft.1
      · calc
          position < (centerBlock - 1 + 1) * blockLength :=
            hleft.2
          _ ≤ (centerBlock + 2) * blockLength :=
            Nat.mul_le_mul_right blockLength (by omega)
    · constructor
      · calc
          (centerBlock - 1) * blockLength ≤
              centerBlock * blockLength :=
            Nat.mul_le_mul_right blockLength (by omega)
          _ ≤ position := hcenter.1
      · calc
          position < (centerBlock + 1) * blockLength :=
            hcenter.2
          _ ≤ (centerBlock + 2) * blockLength :=
            Nat.mul_le_mul_right blockLength (by omega)
    · constructor
      · calc
          (centerBlock - 1) * blockLength ≤
              (centerBlock + 1) * blockLength :=
            Nat.mul_le_mul_right blockLength (by omega)
          _ ≤ position := hright.1
      · simpa [InThreeBlockNeighborhood, threeBlockUpper] using
          hright.2

theorem inThreeBlockNeighborhood_zero_iff_two_blocks_internal
    {blockLength position : ℕ} :
    InThreeBlockNeighborhood blockLength 0 position ↔
      InBlock blockLength 0 position ∨
        InBlock blockLength 1 position := by
  rw [inThreeBlockNeighborhood_iff_three_blocks_internal]
  simp only [Nat.zero_sub, Nat.zero_add]
  tauto

private theorem tape_head_le_move_add_one_internal
    (tape : Tape) (direction : Dir3) :
    tape.head ≤ (tape.move direction).head + 1 := by
  cases direction <;> simp [Tape.move] <;> omega

private theorem tape_head_le_writeAndMove_add_one_internal
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
  · have htape : tape = TapeIndex.input workTapeCount :=
      Fin.ext hinput
    rw [htape]
    simp only [tapeAt_input]
    by_cases hhalt : cfg.state = tm.qhalt
    · simp [NTM.trace, hhalt]
    · simp only [NTM.trace, hhalt, if_false]
      exact ⟨Tape.head_move_le _ _,
        tape_head_le_move_add_one_internal _ _⟩
  · by_cases houtput : tape.val = workTapeCount + 1
    · have htape : tape = TapeIndex.output workTapeCount :=
        Fin.ext houtput
      rw [htape]
      simp only [tapeAt_output]
      by_cases hhalt : cfg.state = tm.qhalt
      · simp [NTM.trace, hhalt]
      · simp only [NTM.trace, hhalt, if_false]
        exact ⟨Tape.head_writeAndMove_le _ _ _,
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
        exact ⟨Tape.head_writeAndMove_le _ _ _,
          tape_head_le_writeAndMove_add_one_internal _ _ _⟩

theorem tapeAt_trace_head_distance_internal
    (tm : NTM workTapeCount) (steps : ℕ)
    (choices : Fin steps → Bool)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount) :
    (tapeAt (tm.trace steps choices cfg) tape).head ≤
        (tapeAt cfg tape).head + steps ∧
      (tapeAt cfg tape).head ≤
        (tapeAt (tm.trace steps choices cfg) tape).head + steps := by
  induction steps generalizing cfg with
  | zero => simp [NTM.trace]
  | succ steps ih =>
      rw [NTM.trace_succ]
      have hfirst := tapeAt_trace_one_head_adjacent_internal
        tm cfg (choices ⟨0, by omega⟩) tape
      have htail := ih
        (fun i => choices ⟨i.val + 1, by omega⟩)
        (tm.trace 1 (fun _ => choices ⟨0, by omega⟩) cfg)
      constructor <;> omega

theorem position_in_threeBlockNeighborhood_of_distance_internal
    {blockLength start position steps : ℕ}
    (hpositive : 0 < blockLength)
    (hsteps : steps ≤ blockLength)
    (hforward : position ≤ start + steps)
    (hbackward : start ≤ position + steps) :
    InThreeBlockNeighborhood blockLength
      (blockIndex blockLength start) position := by
  have hown :=
    position_in_ownBlock blockLength start hpositive
  constructor
  · cases hcenter : blockIndex blockLength start with
    | zero => simp [threeBlockLower]
    | succ center =>
        have hlower : (center + 1) * blockLength ≤ start := by
          simpa [hcenter] using hown.1
        have hposition : center * blockLength ≤ position := by
          rw [Nat.add_mul] at hlower
          omega
        simpa [threeBlockLower] using hposition
  · have hstartUpper :
        start < (blockIndex blockLength start + 1) * blockLength :=
      hown.2
    show position <
      threeBlockUpper blockLength (blockIndex blockLength start)
    calc
      position ≤ start + steps := hforward
      _ < (blockIndex blockLength start + 1) * blockLength +
          blockLength := by omega
      _ = threeBlockUpper blockLength
          (blockIndex blockLength start) := by
        simp [threeBlockUpper, Nat.add_mul]
        omega

theorem tapeAt_trace_head_in_threeBlockNeighborhood_internal
    (tm : NTM workTapeCount) (blockLength steps : ℕ)
    (choices : Fin steps → Bool)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (hpositive : 0 < blockLength)
    (hsteps : steps ≤ blockLength) :
    InThreeBlockNeighborhood blockLength
      (blockIndex blockLength (tapeAt cfg tape).head)
      (tapeAt (tm.trace steps choices cfg) tape).head := by
  have hdistance :=
    tapeAt_trace_head_distance_internal tm steps choices cfg tape
  exact position_in_threeBlockNeighborhood_of_distance_internal
    hpositive hsteps hdistance.1 hdistance.2

theorem tapeNeighborhoodAgreement_read_eq_internal
    {blockLength centerBlock : ℕ} {left right : Tape}
    (h : TapeNeighborhoodAgreement blockLength centerBlock left right)
    (hleft : InThreeBlockNeighborhood
      blockLength centerBlock left.head) :
    left.read = right.read := by
  unfold Tape.read
  rw [h.head_eq]
  apply h.cells_eq
  rwa [← h.head_eq]

theorem tapeNeighborhoodAgreement_move_internal
    {blockLength centerBlock : ℕ} {left right : Tape}
    (h : TapeNeighborhoodAgreement blockLength centerBlock left right)
    (direction : Dir3) :
    TapeNeighborhoodAgreement blockLength centerBlock
      (left.move direction) (right.move direction) := by
  constructor
  · cases direction <;> simp [Tape.move, h.head_eq]
  · intro position hposition
    simpa only [Tape.move_cells] using
      h.cells_eq position hposition

theorem tapeNeighborhoodAgreement_writeAndMove_internal
    {blockLength centerBlock : ℕ} {left right : Tape}
    (h : TapeNeighborhoodAgreement blockLength centerBlock left right)
    (symbol : Γ) (direction : Dir3) :
    TapeNeighborhoodAgreement blockLength centerBlock
      (left.writeAndMove symbol direction)
      (right.writeAndMove symbol direction) := by
  have hwrite : TapeNeighborhoodAgreement blockLength centerBlock
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
  exact tapeNeighborhoodAgreement_move_internal hwrite direction

theorem trace_one_cfgNeighborhoodAgreement_internal
    (tm : TM workTapeCount) (blockLength : ℕ)
    (centerBlocks : TapeIndex workTapeCount → ℕ)
    (left right : Cfg workTapeCount tm.Q)
    (h : CfgNeighborhoodAgreement
      blockLength centerBlocks left right)
    (hinput : InThreeBlockNeighborhood blockLength
      (centerBlocks (TapeIndex.input workTapeCount))
      left.input.head)
    (hwork : ∀ index, InThreeBlockNeighborhood blockLength
      (centerBlocks (TapeIndex.work index))
      (left.work index).head)
    (houtput : InThreeBlockNeighborhood blockLength
      (centerBlocks (TapeIndex.output workTapeCount))
      left.output.head) :
    CfgNeighborhoodAgreement blockLength centerBlocks
      (tm.toNTM.trace 1 (fun _ => false) left)
      (tm.toNTM.trace 1 (fun _ => false) right) := by
  have hinputRead : left.input.read = right.input.read :=
    tapeNeighborhoodAgreement_read_eq_internal h.input hinput
  have hworkRead :
      (fun index => (left.work index).read) =
        (fun index => (right.work index).read) := by
    funext index
    exact tapeNeighborhoodAgreement_read_eq_internal
      (h.work index) (hwork index)
  have houtputRead : left.output.read = right.output.read :=
    tapeNeighborhoodAgreement_read_eq_internal h.output houtput
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
    · exact tapeNeighborhoodAgreement_move_internal h.input _
    · intro index
      exact tapeNeighborhoodAgreement_writeAndMove_internal
        (h.work index) _ _
    · exact tapeNeighborhoodAgreement_writeAndMove_internal
        h.output _ _

theorem trace_cfgNeighborhoodAgreement_of_residence_internal
    (tm : TM workTapeCount) (blockLength steps : ℕ)
    (centerBlocks : TapeIndex workTapeCount → ℕ)
    (left right : Cfg workTapeCount tm.Q)
    (hstart : CfgNeighborhoodAgreement
      blockLength centerBlocks left right)
    (hresidence : ∀ offset, offset < steps → ∀ tape,
      InThreeBlockNeighborhood blockLength (centerBlocks tape)
        (tapeAt
          (tm.toNTM.trace offset (fun _ => false) left)
          tape).head) :
    CfgNeighborhoodAgreement blockLength centerBlocks
      (tm.toNTM.trace steps (fun _ => false) left)
      (tm.toNTM.trace steps (fun _ => false) right) := by
  induction steps with
  | zero => simpa [NTM.trace] using hstart
  | succ steps ih =>
      rw [show
        tm.toNTM.trace (steps + 1) (fun _ => false) left =
          tm.toNTM.trace 1 (fun _ => false)
            (tm.toNTM.trace steps (fun _ => false) left) by
        exact NTM.trace_snoc _ _ _ _]
      rw [show
        tm.toNTM.trace (steps + 1) (fun _ => false) right =
          tm.toNTM.trace 1 (fun _ => false)
            (tm.toNTM.trace steps (fun _ => false) right) by
        exact NTM.trace_snoc _ _ _ _]
      apply trace_one_cfgNeighborhoodAgreement_internal
      · apply ih
        intro offset hoffset tape
        exact hresidence offset
          (Nat.lt_succ_of_lt hoffset) tape
      · simpa only [tapeAt_input] using
          hresidence steps (Nat.lt_succ_self steps)
            (TapeIndex.input workTapeCount)
      · intro index
        simpa only [tapeAt_work] using
          hresidence steps (Nat.lt_succ_self steps)
            (TapeIndex.work index)
      · simpa only [tapeAt_output] using
          hresidence steps (Nat.lt_succ_self steps)
            (TapeIndex.output workTapeCount)

theorem trace_cfgThreeBlockAgreement_internal
    (tm : TM workTapeCount) (blockLength steps : ℕ)
    (left right : Cfg workTapeCount tm.Q)
    (hpositive : 0 < blockLength)
    (hsteps : steps ≤ blockLength)
    (hstart : CfgThreeBlockAgreement blockLength left right) :
    CfgNeighborhoodAgreement blockLength
      (startingBlocks blockLength left)
      (tm.toNTM.trace steps (fun _ => false) left)
      (tm.toNTM.trace steps (fun _ => false) right) := by
  apply trace_cfgNeighborhoodAgreement_of_residence_internal
    tm blockLength steps (startingBlocks blockLength left)
      left right hstart
  intro offset hoffset tape
  unfold startingBlocks
  exact tapeAt_trace_head_in_threeBlockNeighborhood_internal
    tm.toNTM blockLength offset (fun _ => false) left tape
      hpositive (by omega)

theorem configurationAt_add_locality_internal
    (tm : TM workTapeCount) (x : List Bool)
    (start steps : ℕ) :
    tm.configurationAt x (start + steps) =
      tm.toNTM.trace steps (fun _ => false)
        (tm.configurationAt x start) := by
  unfold TM.configurationAt
  simpa using tm.toNTM.trace_add_fun start steps
    (fun _ => false) (tm.initCfg x)

theorem configurationAt_head_in_threeBlockNeighborhood_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength start steps : ℕ)
    (tape : TapeIndex workTapeCount)
    (hpositive : 0 < blockLength)
    (hsteps : steps ≤ blockLength) :
    InThreeBlockNeighborhood blockLength
      (blockIndex blockLength
        (tapeAt (tm.configurationAt x start) tape).head)
      (tapeAt (tm.configurationAt x (start + steps)) tape).head := by
  rw [configurationAt_add_locality_internal]
  exact tapeAt_trace_head_in_threeBlockNeighborhood_internal
    tm.toNTM blockLength steps (fun _ => false)
      (tm.configurationAt x start) tape hpositive hsteps

theorem configurationAt_threeBlock_noninterference_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength start steps : ℕ)
    (seed : Cfg workTapeCount tm.Q)
    (hpositive : 0 < blockLength)
    (hsteps : steps ≤ blockLength)
    (hstart : CfgThreeBlockAgreement blockLength
      (tm.configurationAt x start) seed) :
    CfgNeighborhoodAgreement blockLength
      (startingBlocks blockLength (tm.configurationAt x start))
      (tm.configurationAt x (start + steps))
      (tm.toNTM.trace steps (fun _ => false) seed) := by
  rw [configurationAt_add_locality_internal]
  exact trace_cfgThreeBlockAgreement_internal
    tm blockLength steps (tm.configurationAt x start) seed
      hpositive hsteps hstart

end Internal

end Locality

end TimeSpaceSimulation

end Complexity
