/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalConfiguration.Defs
import Complexitylib.TimeSpaceSimulation.Locality
import Complexitylib.TimeSpaceSimulation.Runtime.PackedDigits

/-!
# Packed finite local configurations -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalConfiguration
namespace Internal

open NeighborhoodGraph

theorem radix_pos_internal (tm : TM workTapeCount) :
    0 < radix tm := by
  simp [radix]

theorem stateCode_lt_radix_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (state : tm.Q) :
    CompactValueCodeSemantics.stateCode order state < radix tm := by
  have hcode := (order.state state).isLt
  change (order.state state).val <
    max 16 (Fintype.card tm.Q + 1)
  exact lt_of_lt_of_le hcode
    (le_trans (Nat.le_succ _) (le_max_right _ _))

theorem gammaCode_lt_four_internal (symbol : Γ) :
    CompactValueCodeSemantics.gammaCode symbol < 4 :=
  (NeighborhoodExecutableEvaluation.FiniteEncoding.gammaEquiv symbol).isLt

theorem cellDigit_lt_radix_internal
    (tm : TM workTapeCount)
    (cfg : Cfg workTapeCount tm.Q)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (tape : TapeIndex workTapeCount)
    (localPosition : ℕ) :
    cellDigit cfg blockLength centers tape localPosition < radix tm := by
  have hgamma :=
    gammaCode_lt_four_internal
      ((tapeAt cfg tape).cells
        (absolutePosition blockLength (centers tape) localPosition))
  simp only [cellDigit]
  cases decide ((tapeAt cfg tape).head =
      absolutePosition blockLength (centers tape) localPosition) <;>
    simp only [Bool.toNat_false, Bool.toNat_true]
  · simp only [mul_zero, add_zero]
    exact lt_of_lt_of_le hgamma (by simp [radix])
  · have : CompactValueCodeSemantics.gammaCode
        ((tapeAt cfg tape).cells
          (absolutePosition blockLength
            (centers tape) localPosition)) + 4 < 16 := by
      omega
    exact lt_of_lt_of_le this (by simp [radix])

theorem configurationDigit_lt_radix_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (index : ℕ) :
    configurationDigit tm order blockLength centers cfg index <
      radix tm := by
  unfold configurationDigit
  split
  · exact stateCode_lt_radix_internal tm order cfg.state
  · exact cellDigit_lt_radix_internal tm cfg blockLength centers _ _

theorem encodeAbove_digit_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix index : ℕ)
    (hindex : index < digitCount workTapeCount blockLength) :
    PackedDigits.digit (radix tm)
        (encodeAbove tm order blockLength centers cfg suffix) index =
      configurationDigit tm order blockLength centers cfg index := by
  unfold encodeAbove PackedDigits.prepend
  simpa using
    PackedDigits.prependFrom_digit
      (radix_pos_internal tm)
      (configurationDigit_lt_radix_internal
        tm order blockLength centers cfg)
      0 (digitCount workTapeCount blockLength) suffix index hindex

theorem encodeAbove_state_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix : ℕ) :
    PackedDigits.digit (radix tm)
        (encodeAbove tm order blockLength centers cfg suffix) 0 =
      CompactValueCodeSemantics.stateCode order cfg.state := by
  rw [encodeAbove_digit_internal]
  · simp [configurationDigit]
  · simp [digitCount]

theorem cellIndex_lt_digitCount_internal
    (blockLength : ℕ) (tape : TapeIndex workTapeCount)
    (localPosition : ℕ)
    (hlocal : localPosition < tapeSpan blockLength) :
    cellIndex blockLength tape localPosition <
      digitCount workTapeCount blockLength := by
  have htape : tape.val + 1 ≤ workTapeCount + 2 :=
    Nat.succ_le_of_lt tape.isLt
  have hmul :=
    Nat.mul_le_mul_right (tapeSpan blockLength) htape
  simp only [cellIndex, digitCount]
  nlinarith

theorem configurationDigit_cell_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (localPosition : ℕ)
    (hlocal : localPosition < tapeSpan blockLength) :
    configurationDigit tm order blockLength centers cfg
        (cellIndex blockLength tape localPosition) =
      cellDigit cfg blockLength centers tape localPosition := by
  simp only [configurationDigit, cellIndex]
  rw [if_neg (by omega)]
  have hspan : 0 < tapeSpan blockLength := by
    simp [tapeSpan]
    omega
  have hflat :
      1 + tape.val * tapeSpan blockLength + localPosition - 1 =
        tape.val * tapeSpan blockLength + localPosition := by
    omega
  rw [hflat, Nat.mul_comm tape.val (tapeSpan blockLength)]
  rw [Nat.mul_add_div hspan, Nat.div_eq_of_lt hlocal, Nat.add_zero]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlocal]
  have htape : tape.val % (workTapeCount + 2) = tape.val :=
    Nat.mod_eq_of_lt tape.isLt
  simp only [tapeOfNat, htape]

theorem encodeAbove_cell_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (localPosition suffix : ℕ)
    (hlocal : localPosition < tapeSpan blockLength) :
    PackedDigits.digit (radix tm)
        (encodeAbove tm order blockLength centers cfg suffix)
        (cellIndex blockLength tape localPosition) =
      cellDigit cfg blockLength centers tape localPosition := by
  rw [encodeAbove_digit_internal]
  · exact configurationDigit_cell_internal
      tm order blockLength hpositive centers cfg tape
        localPosition hlocal
  · exact cellIndex_lt_digitCount_internal
      blockLength tape localPosition hlocal

theorem drop_encodeAbove_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix : ℕ) :
    PackedDigits.drop (radix tm)
        (digitCount workTapeCount blockLength)
        (encodeAbove tm order blockLength centers cfg suffix) =
      suffix := by
  unfold encodeAbove PackedDigits.prepend
  exact PackedDigits.drop_prependFrom
    (radix_pos_internal tm)
    (configurationDigit_lt_radix_internal
      tm order blockLength centers cfg)
    0 (digitCount workTapeCount blockLength) suffix

theorem requestedLocalPosition_lt_internal
    (blockLength center offset : ℕ) (slot : Slot)
    (hpositive : 0 < blockLength)
    (hoffset : offset < blockLength) :
    requestedLocalPosition blockLength center slot offset <
      tapeSpan blockLength := by
  cases center with
  | zero =>
      cases slot <;>
        simp [requestedLocalPosition, neighborBlock,
          windowStart, tapeSpan] <;>
        omega
  | succ center =>
      cases slot <;>
        simp [requestedLocalPosition, neighborBlock,
          windowStart, tapeSpan, Nat.add_mul] <;>
        omega

theorem absolutePosition_requested_internal
    (blockLength center offset : ℕ) (slot : Slot) :
    absolutePosition blockLength center
        (requestedLocalPosition blockLength center slot offset) =
      neighborBlock center slot * blockLength + offset := by
  cases center <;> cases slot <;>
    simp [absolutePosition, requestedLocalPosition, neighborBlock,
      windowStart, Nat.add_mul] <;>
    omega

theorem symbolPart_cellDigit_internal
    (cfg : Cfg workTapeCount Q)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (tape : TapeIndex workTapeCount)
    (localPosition : ℕ) :
    symbolPart
        (cellDigit cfg blockLength centers tape localPosition) =
      CompactValueCodeSemantics.gammaCode
        ((tapeAt cfg tape).cells
          (absolutePosition blockLength
            (centers tape) localPosition)) := by
  simp only [symbolPart, cellDigit]
  have hgamma :=
    gammaCode_lt_four_internal
      ((tapeAt cfg tape).cells
        (absolutePosition blockLength
          (centers tape) localPosition))
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hgamma]

theorem markerPart_cellDigit_internal
    (cfg : Cfg workTapeCount Q)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (tape : TapeIndex workTapeCount)
    (localPosition : ℕ) :
    markerPart
        (cellDigit cfg blockLength centers tape localPosition) =
      (decide ((tapeAt cfg tape).head =
        absolutePosition blockLength
          (centers tape) localPosition)).toNat := by
  simp only [markerPart, cellDigit]
  have hgamma :=
    gammaCode_lt_four_internal
      ((tapeAt cfg tape).cells
        (absolutePosition blockLength
          (centers tape) localPosition))
  rw [Nat.add_mul_div_left _ _ (by omega),
    Nat.div_eq_of_lt hgamma, Nat.zero_add]

theorem findMarkedFrom_eq_internal
    (marker : ℕ → ℕ) (start count target : ℕ)
    (hlower : start ≤ target)
    (hupper : target < start + count)
    (hmarker :
      ∀ index, start ≤ index → index < start + count →
        marker index = if index = target then 1 else 0) :
    findMarkedFrom marker start count = target := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
      rw [findMarkedFrom]
      by_cases heq : start = target
      · subst target
        have hmark : marker start = 1 := by
          simpa using hmarker start (by omega) (by omega)
        simp [hmark]
      · have hmark : marker start = 0 := by
          simpa [heq] using hmarker start (by omega) (by omega)
        simp only [hmark, ↓reduceIte]
        apply ih (start := start + 1)
        · omega
        · omega
        · intro index hindexLower hindexUpper
          exact hmarker index (by omega) (by omega)

theorem findHeadOffset_encodeAbove_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (suffix : ℕ)
    (hlower :
      windowStart blockLength (centers tape) ≤
        (tapeAt cfg tape).head)
    (hupper :
      (tapeAt cfg tape).head <
        windowStart blockLength (centers tape) +
          tapeSpan blockLength) :
    findHeadOffset tm blockLength tape
        (encodeAbove tm order blockLength centers cfg suffix) =
      localHead blockLength (centers tape)
        (tapeAt cfg tape).head := by
  let target :=
    localHead blockLength (centers tape) (tapeAt cfg tape).head
  have htarget : target < tapeSpan blockLength := by
    simp only [target, localHead]
    omega
  have habsolute :
      absolutePosition blockLength (centers tape) target =
        (tapeAt cfg tape).head := by
    simp only [absolutePosition, target, localHead]
    exact Nat.add_sub_of_le hlower
  unfold findHeadOffset
  change findMarkedFrom _ 0 (tapeSpan blockLength) = target
  apply findMarkedFrom_eq_internal (target := target)
  · omega
  · simpa only [Nat.zero_add] using htarget
  · intro index _ hindex
    rw [encodeAbove_cell_internal
      tm order blockLength hpositive centers cfg tape
      index suffix (by simpa only [Nat.zero_add] using hindex)]
    rw [markerPart_cellDigit_internal]
    by_cases heq : index = target
    · subst index
      simp [habsolute]
    · have hposition :
          (tapeAt cfg tape).head ≠
            absolutePosition blockLength (centers tape) index := by
        intro hsame
        apply heq
        simp only [absolutePosition] at habsolute hsame
        omega
      simp [heq, hposition]

theorem outputBitFromWord_encodeAbove_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (suffix coordinate : ℕ)
    (hlower :
      windowStart blockLength (centers targetTape) ≤
        (tapeAt cfg targetTape).head)
    (hupper :
      (tapeAt cfg targetTape).head <
        windowStart blockLength (centers targetTape) +
          tapeSpan blockLength) :
    outputBitFromWord tm blockLength coordinate
        (centers targetTape) targetTape targetSlot
        (encodeAbove tm order blockLength centers cfg suffix) =
      CompactValueCodeSemantics.coordinateBit
        tm order blockLength coordinate
        (requestedContent cfg blockLength hpositive
          (centers targetTape) targetTape targetSlot) := by
  by_cases hstate : coordinate < Fintype.card tm.Q
  · simp only [outputBitFromWord,
      CompactValueCodeSemantics.coordinateBit, hstate, if_true]
    rw [encodeAbove_state_internal]
    rfl
  · by_cases hhead :
        coordinate < Fintype.card tm.Q + blockLength
    · simp only [outputBitFromWord,
        CompactValueCodeSemantics.coordinateBit,
        hstate, if_false, hhead, if_true]
      rw [findHeadOffset_encodeAbove_internal
        tm order blockLength hpositive centers cfg
        targetTape suffix hlower hupper]
      simp only [requestedContent]
      have hdecomp :
          windowStart blockLength (centers targetTape) +
              localHead blockLength (centers targetTape)
                (tapeAt cfg targetTape).head =
            (tapeAt cfg targetTape).head := by
        simp only [localHead]
        exact Nat.add_sub_of_le hlower
      have hmod :
          localHead blockLength (centers targetTape)
                (tapeAt cfg targetTape).head % blockLength =
            (tapeAt cfg targetTape).head % blockLength := by
        have hcongr :=
          congrArg (fun value => value % blockLength) hdecomp
        simpa [windowStart, Nat.add_mod] using hcongr
      simp only [hmod]
      rfl
    · by_cases hcell :
          Fintype.card tm.Q + blockLength ≤ coordinate ∧
            coordinate <
              Fintype.card tm.Q + blockLength + blockLength * 4
      · simp only [outputBitFromWord,
          CompactValueCodeSemantics.coordinateBit,
          hstate, if_false, hhead]
        rw [dif_pos hcell, dif_pos hcell]
        let cellCode :=
          coordinate - (Fintype.card tm.Q + blockLength)
        let offset : Fin blockLength :=
          ⟨cellCode / 4, by omega⟩
        let localPosition :=
          requestedLocalPosition blockLength
            (centers targetTape) targetSlot offset.val
        have hlocal :
            localPosition < tapeSpan blockLength := by
          apply requestedLocalPosition_lt_internal
            blockLength (centers targetTape)
            offset.val targetSlot hpositive offset.isLt
        have hpacked :
            symbolPart
                (PackedDigits.digit (radix tm)
                  (encodeAbove tm order blockLength centers cfg suffix)
                  (cellIndex blockLength targetTape localPosition)) =
              CompactValueCodeSemantics.gammaCode
                ((tapeAt cfg targetTape).cells
                  (absolutePosition blockLength
                    (centers targetTape) localPosition)) := by
          rw [encodeAbove_cell_internal
            tm order blockLength hpositive centers cfg
            targetTape localPosition suffix hlocal]
          exact symbolPart_cellDigit_internal
            cfg blockLength centers targetTape localPosition
        have habsolute :=
          absolutePosition_requested_internal blockLength
            (centers targetTape) offset.val targetSlot
        dsimp only [localPosition, offset, cellCode] at hpacked habsolute
        simp only [requestedContent, blockContents]
        simp only [hpacked]
        rw [habsolute]
        rfl
      · simp only [outputBitFromWord,
          CompactValueCodeSemantics.coordinateBit,
          hstate, if_false, hhead]
        rw [dif_neg hcell, dif_neg hcell]

theorem localStartCfg_head_internal
    (tm : TM workTapeCount) (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q)
    (tape : TapeIndex workTapeCount) :
    (tapeAt
      (Guess.Consistency.localStartCfg
        tm blockLength centers inputs) tape).head =
      centers tape * blockLength +
        (inputs (.chronological, tape)).headRemainder.val := by
  by_cases hinput : tape.val = 0
  · have htape :
        tape = TapeIndex.input workTapeCount :=
      Fin.ext hinput
    rw [htape]
    simp [Guess.Consistency.localStartCfg,
      NeighborhoodContent.cfgFromNeighborhoods,
      NeighborhoodContent.tapeFromNeighborhood]
  · by_cases houtput : tape.val = workTapeCount + 1
    · have htape :
          tape = TapeIndex.output workTapeCount :=
        Fin.ext houtput
      rw [htape]
      simp [Guess.Consistency.localStartCfg,
        NeighborhoodContent.cfgFromNeighborhoods,
        NeighborhoodContent.tapeFromNeighborhood]
    · let index : Fin workTapeCount :=
        ⟨tape.val - 1, by omega⟩
      have htape : tape = TapeIndex.work index := by
        apply Fin.ext
        simp only [TapeIndex.work, index]
        omega
      rw [htape]
      simp [Guess.Consistency.localStartCfg,
        NeighborhoodContent.cfgFromNeighborhoods,
        NeighborhoodContent.tapeFromNeighborhood]

theorem localStartCfg_headBlock_internal
    (tm : TM workTapeCount)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q)
    (tape : TapeIndex workTapeCount) :
    blockIndex blockLength
        (tapeAt
          (Guess.Consistency.localStartCfg
            tm blockLength centers inputs) tape).head =
      centers tape := by
  rw [localStartCfg_head_internal]
  rw [blockIndex,
    Nat.mul_comm (centers tape) blockLength,
    Nat.mul_add_div hpositive,
    Nat.div_eq_of_lt
      (inputs (.chronological, tape)).headRemainder.isLt,
    Nat.add_zero]

theorem localTrace_head_window_internal
    (tm : TM workTapeCount)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (inputs :
      PredecessorIndex workTapeCount →
        NeighborhoodContent.Content blockLength tm.Q)
    (tape : TapeIndex workTapeCount) :
    windowStart blockLength (centers tape) ≤
        (tapeAt
          (GuessedLocalEvaluation.localTraceAtCenters
            tm blockLength centers inputs) tape).head ∧
      (tapeAt
          (GuessedLocalEvaluation.localTraceAtCenters
            tm blockLength centers inputs) tape).head <
        windowStart blockLength (centers tape) +
          tapeSpan blockLength := by
  let start :=
    Guess.Consistency.localStartCfg
      tm blockLength centers inputs
  have htrace :=
    TimeSpaceSimulation.NTM.trace_head_in_threeBlockNeighborhood
      tm.toNTM blockLength blockLength (fun _ => false)
      start tape hpositive (by omega)
  have hblock :
      blockIndex blockLength (tapeAt start tape).head =
        centers tape := by
    exact localStartCfg_headBlock_internal
      tm blockLength hpositive centers inputs tape
  dsimp only [start] at htrace hblock
  have htrace' :
      InThreeBlockNeighborhood blockLength (centers tape)
        (tapeAt
          (GuessedLocalEvaluation.localTraceAtCenters
            tm blockLength centers inputs) tape).head := by
    change
      InThreeBlockNeighborhood blockLength (centers tape)
        (tapeAt
          (tm.toNTM.trace blockLength (fun _ => false)
            (Guess.Consistency.localStartCfg
              tm blockLength centers inputs)) tape).head
    let finalHead :=
      (tapeAt
        (tm.toNTM.trace blockLength (fun _ => false)
          (Guess.Consistency.localStartCfg
            tm blockLength centers inputs)) tape).head
    exact Eq.mp
      (congrArg
        (fun center =>
          InThreeBlockNeighborhood blockLength center finalHead)
        hblock)
      htrace
  constructor
  · simpa [threeBlockLower, windowStart] using htrace'.1
  · apply lt_of_lt_of_le htrace'.2
    cases hcenter : centers tape with
    | zero =>
        simp [threeBlockUpper, windowStart, tapeSpan]
        omega
    | succ center =>
        simp [threeBlockUpper, windowStart, tapeSpan,
          Nat.add_mul]
        omega

theorem outputBit_assignmentFinalWord_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (code suffix coordinate : ℕ) :
    outputBitFromWord tm blockLength coordinate
        (Guess.Consistency.guessedCenters guess interval.val targetTape)
        targetTape targetSlot
        (assignmentFinalWord tm order blockLength hpositive
          guess interval code suffix) =
      LocalAssignmentSemantics.outputBit
        tm order blockLength hpositive guess interval
        targetTape targetSlot code coordinate := by
  let centers :=
    Guess.Consistency.guessedCenters guess interval.val
  let inputs :=
    LocalAssignmentSemantics.assignmentInputs
      tm order blockLength hpositive code
  let final :=
    GuessedLocalEvaluation.localTraceAtCenters
      tm blockLength centers inputs
  have hwindow :=
    localTrace_head_window_internal
      tm blockLength hpositive centers inputs targetTape
  change
    outputBitFromWord tm blockLength coordinate
        (centers targetTape) targetTape targetSlot
        (encodeAbove tm order blockLength centers final suffix) =
      CompactValueCodeSemantics.coordinateBit
        tm order blockLength coordinate
        (LocalAssignmentSemantics.assignmentResult
          tm order blockLength hpositive guess interval
          targetTape targetSlot code)
  rw [outputBitFromWord_encodeAbove_internal
    tm order blockLength hpositive centers final
    targetTape targetSlot suffix coordinate hwindow.1 hwindow.2]
  rfl

end Internal
end PackedLocalConfiguration
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
