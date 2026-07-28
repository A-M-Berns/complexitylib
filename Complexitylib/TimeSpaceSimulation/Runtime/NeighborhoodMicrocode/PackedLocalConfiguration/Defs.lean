/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.LocalAssignmentSemantics.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.PackedDigits.Defs

/-!
# Packed finite configurations for one local transition

A local interval of length `blockLength` only needs three consecutive blocks
around each named head. This file packs that complete finite configuration
into the low-order digits of one natural number while leaving an arbitrary
high-order continuation suffix untouched.

Digit zero stores the hardwired state code. Every remaining digit stores one
tape symbol together with a one-bit head marker. The radix is fixed by the
source machine, not by any runtime search parameter.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalConfiguration

open NeighborhoodGraph

/-- Fixed radix large enough for every state and marked alphabet symbol. -/
def radix (tm : TM workTapeCount) : ℕ :=
  max 16 (Fintype.card tm.Q + 1)

/-- Number of represented cells on one named tape. -/
def tapeSpan (blockLength : ℕ) : ℕ :=
  3 * blockLength

/-- Number of low-order digits in one packed local configuration. -/
def digitCount (workTapeCount blockLength : ℕ) : ℕ :=
  1 + (workTapeCount + 2) * tapeSpan blockLength

/-- First absolute tape position represented around one center block. -/
def windowStart (blockLength center : ℕ) : ℕ :=
  (center - 1) * blockLength

/-- Absolute position represented by one local tape coordinate. -/
def absolutePosition
    (blockLength center localPosition : ℕ) : ℕ :=
  windowStart blockLength center + localPosition

/-- Total named-tape decoder used by the arithmetic digit layout. -/
def tapeOfNat (workTapeCount tape : ℕ) :
    TapeIndex workTapeCount :=
  ⟨tape % (workTapeCount + 2), Nat.mod_lt _ (by omega)⟩

/-- Low-order digit coordinate of one represented tape cell. -/
def cellIndex
    (blockLength : ℕ) (tape : TapeIndex workTapeCount)
    (localPosition : ℕ) : ℕ :=
  1 + tape.val * tapeSpan blockLength + localPosition

/-- Local coordinate of a named head in its three-block window. -/
def localHead
    (blockLength center head : ℕ) : ℕ :=
  head - windowStart blockLength center

/-- Combined alphabet code and one-bit head marker at one local coordinate. -/
def cellDigit
    (cfg : Cfg workTapeCount Q)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (tape : TapeIndex workTapeCount)
    (localPosition : ℕ) : ℕ :=
  let position :=
    absolutePosition blockLength (centers tape) localPosition
  CompactValueCodeSemantics.gammaCode
      ((tapeAt cfg tape).cells position) +
    4 * (decide ((tapeAt cfg tape).head = position)).toNat

/-- Total digit function for one finite local configuration.

Only coordinates below `digitCount` are packed. The total definition is
convenient for the streaming radix interface.
-/
def configurationDigit
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (index : ℕ) : ℕ :=
  if index = 0 then
    CompactValueCodeSemantics.stateCode order cfg.state
  else
    let flat := index - 1
    let tapeNumber := flat / tapeSpan blockLength
    let localPosition := flat % tapeSpan blockLength
    let tape := tapeOfNat workTapeCount tapeNumber
    cellDigit cfg blockLength centers tape localPosition

/-- Pack a finite local configuration below an arbitrary continuation word. -/
def encodeAbove
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (suffix : ℕ) : ℕ :=
  PackedDigits.prepend (radix tm)
    (digitCount workTapeCount blockLength)
    (configurationDigit tm order blockLength centers cfg)
    suffix

/-- Packed local configuration with a zero high-order suffix. -/
def encode
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q) : ℕ :=
  encodeAbove tm order blockLength centers cfg 0

/-- Pure start word for one decoded Cook--Mertz assignment. -/
def assignmentStartWord
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (code suffix : ℕ) : ℕ :=
  let centers := Guess.Consistency.guessedCenters guess interval.val
  let inputs :=
    LocalAssignmentSemantics.assignmentInputs
      tm order blockLength hpositive code
  encodeAbove tm order blockLength centers
    (Guess.Consistency.localStartCfg tm blockLength centers inputs)
    suffix

/-- Pure final word after the genuine local interval trace. -/
def assignmentFinalWord
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (code suffix : ℕ) : ℕ :=
  let centers := Guess.Consistency.guessedCenters guess interval.val
  let inputs :=
    LocalAssignmentSemantics.assignmentInputs
      tm order blockLength hpositive code
  encodeAbove tm order blockLength centers
    (GuessedLocalEvaluation.localTraceAtCenters
      tm blockLength centers inputs)
    suffix

/-- Local coordinate of a requested output block cell. -/
def requestedLocalPosition
    (blockLength center : ℕ) (slot : Slot) (offset : ℕ) : ℕ :=
  neighborBlock center slot * blockLength + offset -
    windowStart blockLength center

/-- Extract the alphabet component from one combined cell digit. -/
def symbolPart (digit : ℕ) : ℕ :=
  digit % 4

/-- Extract the head-marker component from one combined cell digit. -/
def markerPart (digit : ℕ) : ℕ :=
  digit / 4

/-- First marked coordinate in a finite natural interval.

If no marked coordinate occurs, the exclusive end of the interval is
returned. The recursive shape matches the fixed-register linear scan.
-/
def findMarkedFrom (marker : ℕ → ℕ) : ℕ → ℕ → ℕ
  | start, 0 => start
  | start, count + 1 =>
      if marker start = 0 then
        findMarkedFrom marker (start + 1) count
      else
        start

/-- Recover one named head's local coordinate from its packed marker bits. -/
def findHeadOffset
    (tm : TM workTapeCount)
    (blockLength : ℕ)
    (tape : TapeIndex workTapeCount)
    (word : ℕ) : ℕ :=
  findMarkedFrom
    (fun localPosition =>
      markerPart
        (PackedDigits.digit (radix tm) word
          (cellIndex blockLength tape localPosition)))
    0 (tapeSpan blockLength)

/-- Compact value requested from one represented final configuration. -/
def requestedContent
    (cfg : Cfg workTapeCount Q)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (center : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot) :
    NeighborhoodContent.Content blockLength Q where
  state := cfg.state
  headRemainder :=
    ⟨(tapeAt cfg targetTape).head % blockLength,
      Nat.mod_lt _ hpositive⟩
  cells :=
    blockContents (tapeAt cfg targetTape) blockLength
      (neighborBlock center targetSlot)

/-- Numeric compact-output coordinate decoded directly from a packed word. -/
def outputBitFromWord
    (tm : TM workTapeCount)
    (blockLength coordinate : ℕ)
    (center : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (word : ℕ) : Bool :=
  let stateCount := Fintype.card tm.Q
  if coordinate < stateCount then
    decide
      (coordinate =
        PackedDigits.digit (radix tm) word 0)
  else if coordinate < stateCount + blockLength then
    decide
      (coordinate - stateCount =
        findHeadOffset tm blockLength targetTape word % blockLength)
  else if hcell :
      stateCount + blockLength ≤ coordinate ∧
        coordinate <
          stateCount + blockLength + blockLength * 4 then
    let cellCode := coordinate - (stateCount + blockLength)
    let offset : Fin blockLength :=
      ⟨cellCode / 4, by omega⟩
    let localPosition :=
      requestedLocalPosition blockLength center
        targetSlot offset.val
    decide
      (cellCode % 4 =
        symbolPart
          (PackedDigits.digit (radix tm) word
            (cellIndex blockLength targetTape localPosition)))
  else
    false

end PackedLocalConfiguration
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
