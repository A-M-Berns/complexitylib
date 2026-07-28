/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalConfiguration.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalConfiguration.Internal

/-!
# Packed finite configurations for one local transition

This module exposes the fixed-radix representation used by the uniform local
transition kernel. A finite state and three blocks per named tape occupy the
low-order digits of one word; an arbitrary suspended continuation remains
above them and is recovered exactly after the finite prefix is dropped.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalConfiguration

open NeighborhoodGraph

/-- The local configuration radix is positive. -/
theorem radix_pos (tm : TM workTapeCount) :
    0 < radix tm :=
  Internal.radix_pos_internal tm

/-- Every hardwired state code fits in the fixed local radix. -/
theorem stateCode_lt_radix
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (state : tm.Q) :
    CompactValueCodeSemantics.stateCode order state < radix tm :=
  Internal.stateCode_lt_radix_internal tm order state

/-- Every combined symbol/head-marker digit fits in the fixed local radix. -/
theorem cellDigit_lt_radix
    (tm : TM workTapeCount)
    (cfg : Cfg workTapeCount tm.Q)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (tape : TapeIndex workTapeCount)
    (localPosition : ℕ) :
    cellDigit cfg blockLength centers tape localPosition < radix tm :=
  Internal.cellDigit_lt_radix_internal
    tm cfg blockLength centers tape localPosition

/-- Every digit emitted by the total arithmetic layout fits in the radix. -/
theorem configurationDigit_lt_radix
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (index : ℕ) :
    configurationDigit tm order blockLength centers cfg index <
      radix tm :=
  Internal.configurationDigit_lt_radix_internal
    tm order blockLength centers cfg index

/-- Every in-range low-order coordinate decodes to its semantic digit. -/
theorem encodeAbove_digit
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
      configurationDigit tm order blockLength centers cfg index :=
  Internal.encodeAbove_digit_internal
    tm order blockLength centers cfg suffix index hindex

/-- Digit zero is exactly the source-state code. -/
theorem encodeAbove_state
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix : ℕ) :
    PackedDigits.digit (radix tm)
        (encodeAbove tm order blockLength centers cfg suffix) 0 =
      CompactValueCodeSemantics.stateCode order cfg.state :=
  Internal.encodeAbove_state_internal
    tm order blockLength centers cfg suffix

/-- Every valid named-tape cell coordinate lies in the packed prefix. -/
theorem cellIndex_lt_digitCount
    (blockLength : ℕ) (tape : TapeIndex workTapeCount)
    (localPosition : ℕ)
    (hlocal : localPosition < tapeSpan blockLength) :
    cellIndex blockLength tape localPosition <
      digitCount workTapeCount blockLength :=
  Internal.cellIndex_lt_digitCount_internal
    blockLength tape localPosition hlocal

/-- The arithmetic layout maps every valid cell coordinate to its cell
digit. -/
theorem configurationDigit_cell
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
      cellDigit cfg blockLength centers tape localPosition :=
  Internal.configurationDigit_cell_internal
    tm order blockLength hpositive centers cfg tape
      localPosition hlocal

/-- Every packed cell coordinate decodes to its exact symbol/head digit. -/
theorem encodeAbove_cell
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
      cellDigit cfg blockLength centers tape localPosition :=
  Internal.encodeAbove_cell_internal
    tm order blockLength hpositive centers cfg tape
      localPosition suffix hlocal

/-- Dropping the complete finite configuration restores the continuation. -/
theorem drop_encodeAbove
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
      suffix :=
  Internal.drop_encodeAbove_internal
    tm order blockLength centers cfg suffix

/-- Every requested output-block cell has an in-range local coordinate. -/
theorem requestedLocalPosition_lt
    (blockLength center offset : ℕ) (slot : Slot)
    (hpositive : 0 < blockLength)
    (hoffset : offset < blockLength) :
    requestedLocalPosition blockLength center slot offset <
      tapeSpan blockLength :=
  Internal.requestedLocalPosition_lt_internal
    blockLength center offset slot hpositive hoffset

/-- Translating a requested local cell back to the absolute tape gives the
exact requested block and offset. -/
theorem absolutePosition_requested
    (blockLength center offset : ℕ) (slot : Slot) :
    absolutePosition blockLength center
        (requestedLocalPosition blockLength center slot offset) =
      neighborBlock center slot * blockLength + offset :=
  Internal.absolutePosition_requested_internal
    blockLength center offset slot

/-- The low two bits of a cell digit are its exact alphabet code. -/
theorem symbolPart_cellDigit
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
            (centers tape) localPosition)) :=
  Internal.symbolPart_cellDigit_internal
    cfg blockLength centers tape localPosition

/-- Dividing a cell digit by four returns its exact head marker. -/
theorem markerPart_cellDigit
    (cfg : Cfg workTapeCount Q)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (tape : TapeIndex workTapeCount)
    (localPosition : ℕ) :
    markerPart
        (cellDigit cfg blockLength centers tape localPosition) =
      (decide ((tapeAt cfg tape).head =
        absolutePosition blockLength
          (centers tape) localPosition)).toNat :=
  Internal.markerPart_cellDigit_internal
    cfg blockLength centers tape localPosition

/-- A finite scan finds a unique marked target coordinate exactly. -/
theorem findMarkedFrom_eq
    (marker : ℕ → ℕ) (start count target : ℕ)
    (hlower : start ≤ target)
    (hupper : target < start + count)
    (hmarker :
      ∀ index, start ≤ index → index < start + count →
        marker index = if index = target then 1 else 0) :
    findMarkedFrom marker start count = target :=
  Internal.findMarkedFrom_eq_internal
    marker start count target hlower hupper hmarker

/-- Scanning a represented tape recovers its exact local head coordinate. -/
theorem findHeadOffset_encodeAbove
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
        (tapeAt cfg tape).head :=
  Internal.findHeadOffset_encodeAbove_internal
    tm order blockLength hpositive centers cfg tape suffix
      hlower hupper

/-- Decoding any numeric compact coordinate from a represented final word
returns the exact requested compact value bit. -/
theorem outputBitFromWord_encodeAbove
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
          (centers targetTape) targetTape targetSlot) :=
  Internal.outputBitFromWord_encodeAbove_internal
    tm order blockLength hpositive centers cfg
      targetTape targetSlot suffix coordinate hlower hupper

/-- The local start configuration places each named head in its supplied
center block at the chronological remainder. -/
theorem localStartCfg_head
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
        (inputs (.chronological, tape)).headRemainder.val :=
  Internal.localStartCfg_head_internal
    tm blockLength centers inputs tape

/-- The local start head lies in exactly the supplied center block. -/
theorem localStartCfg_headBlock
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
      centers tape :=
  Internal.localStartCfg_headBlock_internal
    tm blockLength hpositive centers inputs tape

/-- The genuine length-`blockLength` local trace keeps every named head
inside the represented finite window. -/
theorem localTrace_head_window
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
          tapeSpan blockLength :=
  Internal.localTrace_head_window_internal
    tm blockLength hpositive centers inputs tape

/-- Every compact coordinate decoded from the packed final trace is exactly
the streamed assignment's semantic output bit. -/
theorem outputBit_assignmentFinalWord
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
        targetTape targetSlot code coordinate :=
  Internal.outputBit_assignmentFinalWord_internal
    tm order blockLength hpositive guess interval
      targetTape targetSlot code suffix coordinate

end PackedLocalConfiguration
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
