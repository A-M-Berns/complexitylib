/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalRepresentation.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalConfiguration
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedOutputChunkSemantics
import Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram

/-!
# Mutable packed-local representation -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalRepresentation
namespace Internal

open NeighborhoodGraph
open TreeEval CookMertz

theorem encodeAbove_represents_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix : ℕ) :
    Represents tm order blockLength centers cfg suffix
      (PackedLocalConfiguration.encodeAbove
        tm order blockLength centers cfg suffix) := by
  constructor
  · intro index hindex
    exact PackedLocalConfiguration.encodeAbove_digit
      tm order blockLength centers cfg suffix index hindex
  · exact PackedLocalConfiguration.drop_encodeAbove
      tm order blockLength centers cfg suffix

private theorem prependFrom_congr
    (base : ℕ) (first second : ℕ → ℕ)
    (firstStart secondStart count suffix : ℕ)
    (heq :
      ∀ offset, offset < count →
        first (firstStart + offset) =
          second (secondStart + offset)) :
    PackedDigits.prependFrom base first firstStart count suffix =
      PackedDigits.prependFrom base second secondStart count suffix := by
  induction count generalizing firstStart secondStart with
  | zero =>
      rfl
  | succ count ih =>
      simp only [PackedDigits.prependFrom]
      congr 1
      · simpa using heq 0 (by omega)
      · apply ih
        intro offset hoffset
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          heq (offset + 1) (by omega)

private theorem prepend_digits_drop
    (base count word : ℕ) :
    PackedDigits.prepend base count
        (fun index => PackedDigits.digit base word index)
        (PackedDigits.drop base count word) =
      word := by
  induction count generalizing word with
  | zero =>
      rfl
  | succ count ih =>
      simp only [PackedDigits.prepend, PackedDigits.prependFrom,
        PackedDigits.drop]
      have htail :
          PackedDigits.prependFrom base
              (fun index => PackedDigits.digit base word index)
              1 count
              (PackedDigits.drop base count
                (PackedDigits.pop base word)) =
            PackedDigits.pop base word := by
        calc
          PackedDigits.prependFrom base
                (fun index => PackedDigits.digit base word index)
                1 count
                (PackedDigits.drop base count
                  (PackedDigits.pop base word)) =
              PackedDigits.prependFrom base
                (fun index =>
                  PackedDigits.digit base
                    (PackedDigits.pop base word) index)
                0 count
                (PackedDigits.drop base count
                  (PackedDigits.pop base word)) := by
            apply prependFrom_congr
            intro offset hoffset
            rw [PackedDigits.digit_pop]
            congr 1
            omega
          _ = PackedDigits.pop base word := by
            simpa [PackedDigits.prepend] using
              ih (word := PackedDigits.pop base word)
      rw [htail]
      exact PackedDigits.push_digit_pop base word

theorem represents_eq_encodeAbove_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (hrep :
      Represents tm order blockLength centers cfg suffix word) :
    word =
      PackedLocalConfiguration.encodeAbove
        tm order blockLength centers cfg suffix := by
  let base := PackedLocalConfiguration.radix tm
  let count :=
    PackedLocalConfiguration.digitCount workTapeCount blockLength
  calc
    word =
        PackedDigits.prepend base count
          (fun index => PackedDigits.digit base word index)
          (PackedDigits.drop base count word) :=
      (prepend_digits_drop base count word).symm
    _ =
        PackedDigits.prepend base count
          (PackedLocalConfiguration.configurationDigit
            tm order blockLength centers cfg)
          suffix := by
      have hsuffix :
          PackedDigits.drop base count word = suffix := by
        simpa [base, count] using hrep.suffix_eq
      rw [hsuffix]
      unfold PackedDigits.prepend
      apply prependFrom_congr
      intro offset hoffset
      simpa [base, count] using hrep.digit_eq offset hoffset
    _ =
        PackedLocalConfiguration.encodeAbove
          tm order blockLength centers cfg suffix := by
      rfl

private theorem drop_eq_popN
    (base count word : ℕ) :
    PackedDigits.drop base count word =
      NeighborhoodProgram.popN base count word := by
  induction count generalizing word with
  | zero =>
      rfl
  | succ count ih =>
      rw [PackedDigits.drop, NeighborhoodProgram.popN, ih]
      exact NeighborhoodProgram.Internal.popN_pop_internal
        base word count

private theorem popN_add
    (base first second word : ℕ) :
    NeighborhoodProgram.popN base (first + second) word =
      NeighborhoodProgram.popN base second
        (NeighborhoodProgram.popN base first word) := by
  simp only [NeighborhoodProgram.Internal.popN_eq_div_pow_internal]
  rw [Nat.div_div_eq_div_mul, ← pow_add]

private theorem popN_restoreN
    {base : ℕ} (hbase : 0 < base) :
    ∀ count word buffer,
      NeighborhoodProgram.popN base count
          (NeighborhoodProgram.restoreN
            base count word buffer) =
        word := by
  intro count
  induction count with
  | zero =>
      intro word buffer
      rfl
  | succ count ih =>
      intro word buffer
      rw [NeighborhoodProgram.restoreN,
        NeighborhoodProgram.popN]
      rw [ih]
      exact PackedDigits.pop_push hbase
        (PackedDigits.digit_lt hbase)

theorem drop_replaceAt_internal
    {base count word index replacement : ℕ}
    (hbase : 0 < base)
    (hindex : index < count)
    (hreplacement : replacement < base) :
    PackedDigits.drop base count
        (NeighborhoodProgram.replaceAt
          base word index replacement) =
      PackedDigits.drop base count word := by
  have hsplit :
      count = index + 1 + (count - (index + 1)) := by
    omega
  rw [drop_eq_popN, drop_eq_popN, hsplit]
  rw [popN_add, popN_add]
  unfold NeighborhoodProgram.replaceAt
  rw [popN_add]
  rw [popN_restoreN hbase]
  simp only [NeighborhoodProgram.popN]
  rw [PackedDigits.pop_push hbase hreplacement]
  rw [NeighborhoodProgram.Internal.popN_pop_internal]
  calc
    NeighborhoodProgram.popN base
          (count - (index + 1) + 1)
          (NeighborhoodProgram.popN base index word) =
        NeighborhoodProgram.popN base
          (index + (count - (index + 1) + 1)) word :=
      (popN_add base index
        (count - (index + 1) + 1) word).symm
    _ = NeighborhoodProgram.popN base
          (index + 1 + (count - (index + 1))) word := by
      congr 1
      omega

theorem replaceAt_represents_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg nextCfg : Cfg workTapeCount tm.Q)
    (suffix word index replacement : ℕ)
    (hrep :
      Represents tm order blockLength centers cfg suffix word)
    (hindex :
      index <
        PackedLocalConfiguration.digitCount
          workTapeCount blockLength)
    (hreplacement :
      replacement < PackedLocalConfiguration.radix tm)
    (hupdate :
      ∀ coordinate,
        coordinate <
            PackedLocalConfiguration.digitCount
              workTapeCount blockLength →
          PackedLocalConfiguration.configurationDigit
              tm order blockLength centers nextCfg coordinate =
            if coordinate = index then
              replacement
            else
              PackedLocalConfiguration.configurationDigit
                tm order blockLength centers cfg coordinate) :
    Represents tm order blockLength centers nextCfg suffix
      (NeighborhoodProgram.replaceAt
        (PackedLocalConfiguration.radix tm)
        word index replacement) := by
  constructor
  · intro coordinate hcoordinate
    by_cases heq : coordinate = index
    · subst coordinate
      rw [NeighborhoodProgram.replaceAt_digit_eq
        (PackedLocalConfiguration.radix_pos tm) hreplacement]
      simpa using (hupdate index hindex).symm
    · rw [NeighborhoodProgram.replaceAt_digit_ne
        (PackedLocalConfiguration.radix_pos tm)
        hreplacement heq]
      rw [hrep.digit_eq coordinate hcoordinate]
      simpa [heq] using (hupdate coordinate hcoordinate).symm
  · exact
      (drop_replaceAt_internal
        (PackedLocalConfiguration.radix_pos tm)
        hindex hreplacement).trans hrep.suffix_eq

theorem represents_state_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (hrep :
      Represents tm order blockLength centers cfg suffix word) :
    PackedDigits.digit
        (PackedLocalConfiguration.radix tm) word 0 =
      CompactValueCodeSemantics.stateCode order cfg.state := by
  rw [hrep.digit_eq 0 (by
    unfold PackedLocalConfiguration.digitCount
    omega)]
  simp [PackedLocalConfiguration.configurationDigit]

theorem represents_cell_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (hrep :
      Represents tm order blockLength centers cfg suffix word)
    (tape : TapeIndex workTapeCount)
    (localPosition : ℕ)
    (hlocal :
      localPosition <
        PackedLocalConfiguration.tapeSpan blockLength) :
    PackedDigits.digit
        (PackedLocalConfiguration.radix tm) word
        (PackedLocalConfiguration.cellIndex
          blockLength tape localPosition) =
      PackedLocalConfiguration.cellDigit
        cfg blockLength centers tape localPosition := by
  rw [hrep.digit_eq _ (
    PackedLocalConfiguration.cellIndex_lt_digitCount
      blockLength tape localPosition hlocal)]
  exact PackedLocalConfiguration.configurationDigit_cell
    tm order blockLength hpositive centers cfg tape
      localPosition hlocal

theorem findHeadOffset_represents_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (hrep :
      Represents tm order blockLength centers cfg suffix word)
    (tape : TapeIndex workTapeCount)
    (hlower :
      PackedLocalConfiguration.windowStart
          blockLength (centers tape) ≤
        (tapeAt cfg tape).head)
    (hupper :
      (tapeAt cfg tape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers tape) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    PackedLocalConfiguration.findHeadOffset
        tm blockLength tape word =
      PackedLocalConfiguration.localHead
        blockLength (centers tape) (tapeAt cfg tape).head := by
  let target :=
    PackedLocalConfiguration.localHead
      blockLength (centers tape) (tapeAt cfg tape).head
  have htarget :
      target <
        PackedLocalConfiguration.tapeSpan blockLength := by
    simp only [target, PackedLocalConfiguration.localHead]
    omega
  have habsolute :
      PackedLocalConfiguration.absolutePosition
          blockLength (centers tape) target =
        (tapeAt cfg tape).head := by
    simp only [PackedLocalConfiguration.absolutePosition,
      target, PackedLocalConfiguration.localHead]
    exact Nat.add_sub_of_le hlower
  unfold PackedLocalConfiguration.findHeadOffset
  change
    PackedLocalConfiguration.findMarkedFrom _ 0
        (PackedLocalConfiguration.tapeSpan blockLength) =
      target
  apply PackedLocalConfiguration.findMarkedFrom_eq
      (target := target)
  · omega
  · simpa only [Nat.zero_add] using htarget
  · intro index _ hindex
    rw [represents_cell_internal
      tm order blockLength hpositive centers cfg suffix word hrep
      tape index (by simpa only [Nat.zero_add] using hindex)]
    rw [PackedLocalConfiguration.markerPart_cellDigit]
    by_cases heq : index = target
    · subst index
      simp [habsolute]
    · have hposition :
          (tapeAt cfg tape).head ≠
            PackedLocalConfiguration.absolutePosition
              blockLength (centers tape) index := by
        intro hsame
        apply heq
        simp only [PackedLocalConfiguration.absolutePosition]
          at habsolute hsame
        omega
      simp [heq, hposition]

theorem outputBitFromWord_represents_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (hrep :
      Represents tm order blockLength centers cfg suffix word)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (coordinate : ℕ)
    (hlower :
      PackedLocalConfiguration.windowStart
          blockLength (centers targetTape) ≤
        (tapeAt cfg targetTape).head)
    (hupper :
      (tapeAt cfg targetTape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers targetTape) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    PackedLocalConfiguration.outputBitFromWord
        tm blockLength coordinate (centers targetTape)
          targetTape targetSlot word =
      CompactValueCodeSemantics.coordinateBit
        tm order blockLength coordinate
        (PackedLocalConfiguration.requestedContent
          cfg blockLength hpositive (centers targetTape)
            targetTape targetSlot) := by
  by_cases hstate : coordinate < Fintype.card tm.Q
  · simp only [PackedLocalConfiguration.outputBitFromWord,
      CompactValueCodeSemantics.coordinateBit, hstate, if_true]
    rw [represents_state_internal
      tm order blockLength centers cfg suffix word hrep]
    rfl
  · by_cases hhead :
        coordinate < Fintype.card tm.Q + blockLength
    · simp only [PackedLocalConfiguration.outputBitFromWord,
        CompactValueCodeSemantics.coordinateBit,
        hstate, if_false, hhead, if_true]
      rw [findHeadOffset_represents_internal
        tm order blockLength hpositive centers cfg suffix word hrep
          targetTape hlower hupper]
      simp only [PackedLocalConfiguration.requestedContent]
      have hdecomp :
          PackedLocalConfiguration.windowStart
                blockLength (centers targetTape) +
              PackedLocalConfiguration.localHead
                blockLength (centers targetTape)
                  (tapeAt cfg targetTape).head =
            (tapeAt cfg targetTape).head := by
        simp only [PackedLocalConfiguration.localHead]
        exact Nat.add_sub_of_le hlower
      have hmod :
          PackedLocalConfiguration.localHead
                  blockLength (centers targetTape)
                  (tapeAt cfg targetTape).head %
                blockLength =
            (tapeAt cfg targetTape).head % blockLength := by
        have hcongr :=
          congrArg (fun value => value % blockLength) hdecomp
        simpa [PackedLocalConfiguration.windowStart,
          Nat.add_mod] using hcongr
      simp only [hmod]
      rfl
    · by_cases hcell :
          Fintype.card tm.Q + blockLength ≤ coordinate ∧
            coordinate <
              Fintype.card tm.Q + blockLength + blockLength * 4
      · simp only [PackedLocalConfiguration.outputBitFromWord,
          CompactValueCodeSemantics.coordinateBit,
          hstate, if_false, hhead]
        rw [dif_pos hcell, dif_pos hcell]
        let cellCode :=
          coordinate - (Fintype.card tm.Q + blockLength)
        let offset : Fin blockLength :=
          ⟨cellCode / 4, by omega⟩
        let localPosition :=
          PackedLocalConfiguration.requestedLocalPosition
            blockLength (centers targetTape) targetSlot offset.val
        have hlocal :
            localPosition <
              PackedLocalConfiguration.tapeSpan blockLength := by
          apply PackedLocalConfiguration.requestedLocalPosition_lt
            blockLength (centers targetTape)
              offset.val targetSlot hpositive offset.isLt
        have hpacked :
            PackedLocalConfiguration.symbolPart
                (PackedDigits.digit
                  (PackedLocalConfiguration.radix tm) word
                  (PackedLocalConfiguration.cellIndex
                    blockLength targetTape localPosition)) =
              CompactValueCodeSemantics.gammaCode
                ((tapeAt cfg targetTape).cells
                  (PackedLocalConfiguration.absolutePosition
                    blockLength (centers targetTape)
                      localPosition)) := by
          rw [represents_cell_internal
            tm order blockLength hpositive centers cfg suffix word hrep
              targetTape localPosition hlocal]
          exact PackedLocalConfiguration.symbolPart_cellDigit
            cfg blockLength centers targetTape localPosition
        have habsolute :=
          PackedLocalConfiguration.absolutePosition_requested
            blockLength (centers targetTape)
              offset.val targetSlot
        dsimp only [localPosition, offset, cellCode]
          at hpacked habsolute
        simp only [PackedLocalConfiguration.requestedContent,
          blockContents]
        simp only [hpacked]
        rw [habsolute]
        rfl
      · simp only [PackedLocalConfiguration.outputBitFromWord,
          CompactValueCodeSemantics.coordinateBit,
          hstate, if_false, hhead]
        rw [dif_neg hcell, dif_neg hcell]

theorem packedOutputChunk_represents_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix word : ℕ)
    (hrep :
      Represents tm order blockLength centers cfg suffix word)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)))
    (hlower :
      PackedLocalConfiguration.windowStart
          blockLength (centers targetTape) ≤
        (tapeAt cfg targetTape).head)
    (hupper :
      (tapeAt cfg targetTape).head <
        PackedLocalConfiguration.windowStart
            blockLength (centers targetTape) +
          PackedLocalConfiguration.tapeSpan blockLength) :
    PackedOutputChunkSemantics.packedOutputChunk
        tm blockLength (centers targetTape)
          targetTape targetSlot word outputChunk.val
          (PrimeGrouped.Logarithmic.chunkBits
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount)) =
      PrimeGrouped.Logarithmic.chunkCodeNat
        (GroupedExtension.Layout.pack
          (b :=
            NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
          (chunkBits :=
            PrimeGrouped.Logarithmic.chunkBits
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount))
          (fun position =>
            CompactValueCodeSemantics.coordinateBit
              tm order blockLength position.val
              (PackedLocalConfiguration.requestedContent
                cfg blockLength hpositive (centers targetTape)
                  targetTape targetSlot))
          outputChunk) := by
  rw [PackedOutputChunkSemantics.packedOutputChunk_eq_chunkCodeNat]
  apply congrArg PrimeGrouped.Logarithmic.chunkCodeNat
  funext offset
  unfold GroupedExtension.Layout.pack
  split <;> rename_i hcoordinate
  · exact outputBitFromWord_represents_internal
      tm order blockLength hpositive centers cfg suffix word hrep
        targetTape targetSlot
        (outputChunk.val *
            PrimeGrouped.Logarithmic.chunkBits
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount) +
          offset.val)
        hlower hupper
  · rfl

theorem packedOutputChunk_assignmentFinal_represents_internal
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)))
    (code suffix word : ℕ)
    (hrep :
      Represents tm order blockLength
        (Guess.Consistency.guessedCenters guess interval.val)
        (GuessedLocalEvaluation.localTraceAtCenters
          tm blockLength
          (Guess.Consistency.guessedCenters guess interval.val)
          (LocalAssignmentSemantics.assignmentInputs
            tm order blockLength hpositive code))
        suffix word) :
    PackedOutputChunkSemantics.packedOutputChunk
        tm blockLength
          (Guess.Consistency.guessedCenters
            guess interval.val targetTape)
          targetTape targetSlot word outputChunk.val
          (PrimeGrouped.Logarithmic.chunkBits
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount)) =
      LocalAssignmentSemantics.outputChunkValue
        tm order blockLength hpositive guess interval
          targetTape targetSlot outputChunk code := by
  let centers :=
    Guess.Consistency.guessedCenters guess interval.val
  let inputs :=
    LocalAssignmentSemantics.assignmentInputs
      tm order blockLength hpositive code
  let final :=
    GuessedLocalEvaluation.localTraceAtCenters
      tm blockLength centers inputs
  have hwindow :=
    PackedLocalConfiguration.localTrace_head_window
      tm blockLength hpositive centers inputs targetTape
  rw [packedOutputChunk_represents_internal
    tm order blockLength hpositive centers final suffix word
      hrep targetTape targetSlot outputChunk hwindow.1 hwindow.2]
  rfl

end Internal
end PackedLocalRepresentation
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
