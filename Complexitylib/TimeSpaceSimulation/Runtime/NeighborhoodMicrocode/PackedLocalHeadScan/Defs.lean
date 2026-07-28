/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalConfiguration.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineValue.Defs

/-!
# Fixed-register packed local-head scan

This definitions layer scans the `3 * blockLength` packed cells belonging to
one compile-time named tape. Dynamic digit reads use only direct registers
and restore the packed local-configuration word exactly.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalHeadScan

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Dynamic packed-word reader allocation.

The order is word, buffer, base, base predecessor, quotient, test, one,
value, dynamic index, completed count, result, and replacement. Physical
slot 32 is the local-configuration word; slot 33 remains the untouched
catalytic word. -/
def bankMap : Fin 12 → Fin 34 :=
  ![32, 0, 1, 4, 5, 6, 9, 11, 12, 17, 20, 29]

theorem bankMap_injective :
    Function.Injective bankMap := by
  decide

/-- Packed-word reader view over the combine scratch allocation. -/
def bankRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    NeighborhoodProgram.BankRegisters where
  index := fun slot => regs.index (bankMap slot)
  injective := regs.injective.comp bankMap_injective

/-- Number of local coordinates not yet inspected. -/
abbrev countdown
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 30

/-- Returned local head coordinate. The packed reader preserves this
replacement cell across each dynamic read. -/
abbrev headOffset
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  (bankRegisters regs).replacement

/-- Returned alphabet code at the marked local head coordinate. -/
abbrev symbolCode
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  (bankRegisters regs).result

/-- Quotient/remainder view used to split a packed cell digit into its
alphabet remainder and marker quotient. -/
def cellDivision
    (regs : NeighborhoodTrial.Registers controller) :
    ControlDecode.DivisionRegisters where
  index := fun slot =>
    (bankRegisters regs).index (![10, 1, 5, 6, 2] slot)
  injective := (bankRegisters regs).injective.comp (by decide)

/-- Exact mutable footprint of the packed local-head scan. -/
def footprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  (bankRegisters regs).footprint ∪ {countdown regs}

/-- Prepare the dynamic packed digit coordinate
`1 + tape * (3 * blockLength) + localPosition`. -/
def prepareCellIndex
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.basics
    [.imm bank.indexCount 0,
      .add bank.indexCount (Layout.blockLength regs) bank.indexCount,
      .add bank.indexCount (Layout.blockLength regs) bank.indexCount,
      .add bank.indexCount (Layout.blockLength regs) bank.indexCount,
      .imm bank.result tape.val,
      .mul bank.indexCount bank.result bank.indexCount,
      .add bank.indexCount bank.replacement bank.indexCount,
      .add bank.indexCount bank.one bank.indexCount]

/-- Read the packed cell at the current local coordinate. -/
def readCell
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (prepareCellIndex tape regs)
    (NeighborhoodProgram.bankRead (bankRegisters regs))

/-- Divide the packed cell digit by four. The remainder stays in
`symbolCode`; the quotient in the reader buffer is the marker bit. -/
def decodeCell
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (.basic (.imm (bankRegisters regs).base 4))
    (ControlDecode.divRem (cellDivision regs))

/-- Restore the packed-word radix and advance to the next local coordinate. -/
def advance
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.basics
    [.imm bank.base (PackedLocalConfiguration.radix tm),
      .imm bank.basePred (PackedLocalConfiguration.radix tm - 1),
      .add bank.replacement bank.replacement bank.one,
      .sub (countdown regs) (countdown regs) bank.one]

/-- Inspect one cell, stopping at a nonzero marker and otherwise advancing. -/
def step
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [readCell tape regs,
      decodeCell regs,
      .ifZero (cellDivision regs).quotient
        (advance tm regs)
        (.basic (.imm (countdown regs) 0))]

/-- Initialize the dynamic packed-word reader and the `3 * blockLength`
coordinate countdown. -/
def initializeScan
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.basics
    [.imm bank.base (PackedLocalConfiguration.radix tm),
      .imm bank.basePred (PackedLocalConfiguration.radix tm - 1),
      .imm bank.one 1,
      .imm bank.replacement 0,
      .imm (countdown regs) 0,
      .add (countdown regs) (Layout.blockLength regs)
        (countdown regs),
      .add (countdown regs) (Layout.blockLength regs)
        (countdown regs),
      .add (countdown regs) (Layout.blockLength regs)
        (countdown regs)]

/-- Scan one compile-time tape for its unique packed head marker.

The final write restores the enclosing range driver's canonical one cell,
which is time-multiplexed as the packed reader's completed-count scratch. -/
def scan
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [initializeScan tm regs,
      .whileNonzero (countdown regs) (step tm tape regs),
      .basic
        (.imm (CombineValue.rangeRegisters regs).one 1)]

/-- Exact semantic result on a represented local configuration. -/
structure Post
    (tm : TM workTapeCount)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount tm.Q)
    (tape : TapeIndex workTapeCount)
    (word : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- Exact local offset of the represented named head. -/
  head_eq :
    final (headOffset regs) =
      PackedLocalConfiguration.localHead blockLength
        (centers tape) (tapeAt cfg tape).head
  /-- Exact alphabet code under that head. -/
  symbol_eq :
    final (symbolCode regs) =
      CompactValueCodeSemantics.gammaCode
        ((tapeAt cfg tape).cells (tapeAt cfg tape).head)
  /-- Packed configuration and its high continuation suffix are unchanged. -/
  word_eq : final (bankRegisters regs).word = word
  /-- The scan countdown is exhausted. -/
  countdown_eq : final (countdown regs) = 0
  /-- The enclosing range constant is restored. -/
  rangeOne_eq :
    final (CombineValue.rangeRegisters regs).one =
      initial (CombineValue.rangeRegisters regs).one
  /-- Every address outside the finite direct-register footprint is
  preserved. -/
  eq_outside :
    ∀ address, address ∉ footprint regs →
      final address = initial address

/-- Live combine and computation-context fields preserved by the scan. -/
structure PreservesCombine
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- Outer modular-sum accumulator is preserved. -/
  accumulator_eq :
    final (CombineValue.rangeRegisters regs).accumulator =
      initial (CombineValue.rangeRegisters regs).accumulator
  /-- Current assignment code is preserved. -/
  assignment_eq :
    final (CombineValue.rangeRegisters regs).remaining =
      initial (CombineValue.rangeRegisters regs).remaining
  /-- Outer term cell is preserved. -/
  term_eq :
    final (CombineValue.rangeRegisters regs).term =
      initial (CombineValue.rangeRegisters regs).term
  /-- Immutable assignment count is preserved. -/
  count_eq :
    final (CombineValue.rangeRegisters regs).count =
      initial (CombineValue.rangeRegisters regs).count
  /-- Outer range one is restored under its canonical-entry invariant. -/
  one_eq :
    final (CombineValue.rangeRegisters regs).one =
      initial (CombineValue.rangeRegisters regs).one
  /-- Caller-owned physical slot 31 is untouched. -/
  codecScratch_eq :
    final (Layout.codecScratch regs) =
      initial (Layout.codecScratch regs)
  /-- Packed catalytic word 33 is untouched. -/
  catalyticWord_eq :
    final regs.layout.bank = initial regs.layout.bank
  /-- Stable parameter and active-frame ABI fields are preserved. -/
  abi : ControlDecode.PreservesABI regs initial final

end PackedLocalHeadScan
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
