/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentPayloadBit.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineSafeCenter.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalHeadScan.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalStep.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedOutputChunkSemantics.Defs

/-!
# Executable grouped output from a packed local configuration

This definitions layer decodes one active computation node, selects its named
tape and requested block slot through finite hardwired dispatch, and streams
one runtime-width grouped output chunk from a represented packed local trace.

The runtime chunk cursor remains in `Layout.active`. The command recovers
`chunkBits` from the preserved radix, evaluates coordinates in increasing
order, and performs the same big-endian binary fold as
`PackedOutputChunkSemantics.packedOutputChunk`.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalOutputChunk

open RAM Structured
open NeighborhoodGraph

variable {controller : SearchProgram.Registers}

/-- Reuse the packed local reader allocation. -/
abbrev bankRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    NeighborhoodProgram.BankRegisters :=
  PackedLocalHeadScan.bankRegisters regs

/-- Recovered runtime grouped-coordinate width, retained across bit reads. -/
abbrev chunkBits
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  (CombineValue.rangeRegisters regs).term

/-- Number of grouped-coordinate bits not yet folded. -/
abbrev remaining
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  (CombineValue.rangeRegisters regs).count

/-- Big-endian chunk accumulator. -/
abbrev accumulator
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  Layout.codecScratch regs

/-- Dynamic compact coordinate supplied to one bit evaluator. -/
abbrev coordinate
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  (bankRegisters regs).replacement

/-- Numeric Boolean result of one compact coordinate. -/
abbrev bitValue
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  (bankRegisters regs).result

/-- Direct-register copy. -/
def copy (destination source : ℕ) : Cmd :=
  Cmd.seq
    (.basic (.imm destination 0))
    (.basic (.add destination source destination))

/-- Compare two runtime values, returning one in `output` exactly on equality. -/
def equalValues
    (regs : NeighborhoodTrial.Registers controller)
    (left right output : ℕ) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [.basic (.sub bank.test left right),
      .basic (.sub bank.quotient right left),
      .basic (.add output bank.test bank.quotient),
      .ifZero output
        (.basic (.imm output 1))
        (.basic (.imm output 0))]

/-- Compare one runtime value with a hardwired natural, returning zero on
equality. The scratch cells avoid every decoded node payload. -/
def compareImmediate
    (regs : NeighborhoodTrial.Registers controller)
    (value output constant : ℕ) : Cmd :=
  Cmd.seqList
    [.basic (.imm (regs.index 0) constant),
      .basic (.sub (regs.index 4) value (regs.index 0)),
      .basic (.sub (regs.index 5) (regs.index 0) value),
      .basic (.add output (regs.index 4) (regs.index 5))]

/-- Restore the range driver's canonical one cell. -/
def restoreRangeOne
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  .basic (.imm (CombineValue.rangeRegisters regs).one 1)

/-- Initialize the fixed local-configuration radix interface. -/
def initializeBank
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.basics
    [.imm bank.base (PackedLocalConfiguration.radix tm),
      .imm bank.basePred (PackedLocalConfiguration.radix tm - 1),
      .imm bank.one 1]

/-- Recompute the current global compact coordinate from the immutable chunk
cursor, recovered width, and descending remaining-bit count. -/
def prepareCoordinate
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [.basic (.imm (coordinate regs) 0),
      .basic
        (.add (coordinate regs) (Layout.active regs)
          (coordinate regs)),
      .basic
        (.mul (coordinate regs) (coordinate regs)
          (chunkBits regs)),
      .basic
        (.add (coordinate regs) (coordinate regs)
          (chunkBits regs)),
      .basic
        (.sub (coordinate regs) (coordinate regs)
          (remaining regs))]

/-- Read packed state digit zero. -/
def readState
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [initializeBank tm regs,
      .basic (.imm bank.indexCount 0),
      NeighborhoodProgram.bankRead bank,
      restoreRangeOne regs]

/-- Evaluate a state coordinate already known to lie below the state width. -/
def stateBit
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (readState tm regs)
    (equalValues regs (coordinate regs) (bitValue regs)
      (bitValue regs))

/-- Reduce the scanned local head coordinate modulo the runtime block length. -/
def reduceHeadOffset
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [copy bank.result (PackedLocalHeadScan.headOffset regs),
      copy bank.base (Layout.blockLength regs),
      ControlDecode.divRem (PackedLocalHeadScan.cellDivision regs)]

/-- Compare the current head remainder with the recomputed compact coordinate. -/
def compareHeadCoordinate
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [prepareCoordinate regs,
      .basic (.imm bank.value (Fintype.card tm.Q)),
      .basic
        (.sub (coordinate regs) (coordinate regs) bank.value),
      equalValues regs (coordinate regs) bank.result bank.result,
      restoreRangeOne regs]

/-- Evaluate one chronological head-remainder coordinate. -/
def headBit
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [PackedLocalHeadScan.scan tm tape regs,
      reduceHeadOffset regs,
      compareHeadCoordinate tm regs]

/-- Split an in-range compact cell coordinate into symbol code and cell
offset. -/
def decodeCellCoordinate
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [.basic (.imm bank.value (Fintype.card tm.Q)),
      .basic
        (.add bank.value bank.value (Layout.blockLength regs)),
      .basic
        (.sub (coordinate regs) (coordinate regs) bank.value),
      copy bank.result (coordinate regs),
      .basic (.imm bank.base 4),
      ControlDecode.divRem (PackedLocalHeadScan.cellDivision regs)]

/-- Read and decode the packed cell selected by one local block and offset. -/
def readSelectedCell
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [.basic (.imm (coordinate regs) localBlock),
      .basic
        (.mul (coordinate regs) (coordinate regs)
          (Layout.blockLength regs)),
      .basic
        (.add (coordinate regs) bank.buffer (coordinate regs)),
      initializeBank tm regs,
      PackedLocalHeadScan.readCell tape regs,
      PackedLocalHeadScan.decodeCell regs,
      copy bank.indexCount bank.result]

/-- Recompute and compare the compact cell-symbol coordinate with the decoded
packed symbol. -/
def compareCellCoordinate
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [prepareCoordinate regs,
      decodeCellCoordinate tm regs,
      equalValues regs bank.result bank.indexCount bank.result,
      restoreRangeOne regs]

/-- Evaluate one in-range compact cell coordinate.

`localBlock` is the selected block's zero-based offset inside the represented
three-block packed window. -/
def cellBit
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [decodeCellCoordinate tm regs,
      readSelectedCell tm tape localBlock regs,
      compareCellCoordinate tm regs]

/-- Check the compact payload's strict upper bound before evaluating a cell
coordinate. -/
def payloadBit
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seq
    (Cmd.basics
      [.imm bank.value 5,
        .mul bank.buffer bank.value (Layout.blockLength regs),
        .imm bank.value (Fintype.card tm.Q),
        .add bank.buffer bank.value bank.buffer,
        .sub bank.test bank.buffer (coordinate regs)])
    (.ifZero bank.test
        (.basic (.imm (bitValue regs) 0))
        (cellBit tm tape localBlock regs))

/-- Evaluate a non-state coordinate as a head bit, cell bit, or padding zero. -/
def nonStateBit
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seq
    (Cmd.basics
      [.imm bank.value (Fintype.card tm.Q),
        .add bank.value bank.value (Layout.blockLength regs),
        .sub bank.test bank.value (coordinate regs)])
    (.ifZero bank.test
        (payloadBit tm tape localBlock regs)
        (headBit tm tape regs))

/-- Evaluate one bounded compact coordinate from the represented packed word. -/
def outputBit
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seq
    (prepareCoordinate regs)
    (Cmd.seq
      (Cmd.basics
        [.imm bank.value (Fintype.card tm.Q),
          .sub bank.test bank.value (coordinate regs)])
      (.ifZero bank.test
        (nonStateBit tm tape localBlock regs)
        (stateBit tm regs)))

/-- Consume one bit and extend the big-endian output accumulator. -/
def chunkBody
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seq
    (outputBit tm tape localBlock regs)
    (Cmd.basics
      [.imm bank.base 2,
        .mul (accumulator regs) (accumulator regs) bank.base,
        .add (accumulator regs) (bitValue regs)
          (accumulator regs),
        .imm bank.one 1,
        .sub (remaining regs) (remaining regs) bank.one])

/-- Compute one grouped output chunk for a compile-time tape and local block. -/
def computeSelected
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (localBlock : ℕ)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [AssignmentPayloadBit.recoverChunkBits regs,
      copy (chunkBits regs)
        (AssignmentPayloadBit.recoveredChunkBits regs),
      copy (remaining regs)
        (AssignmentPayloadBit.recoveredChunkBits regs),
      .basic (.imm (accumulator regs) 0),
      .whileNonzero (remaining regs)
        (chunkBody tm tape localBlock regs),
      copy (CombineTerm.packedValue regs) (accumulator regs),
      restoreRangeOne regs]

/-- Local block offset for a requested slot at guessed center zero. -/
def boundaryLocalBlock : Slot → ℕ
  | .lower => 0
  | .center => 0
  | .upper => 1

/-- Local block offset for a requested slot at a positive guessed center. -/
def regularLocalBlock : Slot → ℕ
  | .lower => 0
  | .center => 1
  | .upper => 2

/-- Derive the selected tape center and choose its boundary-aware local block. -/
def computeTapeSlot
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (tape : TapeIndex workTapeCount)
    (slot : Slot)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (CombineSafeCenter.deriveCenter workTapeCount controller regs)
    (.ifZero (CombineSafeCenter.centerValue regs)
      (computeSelected tm tape (boundaryLocalBlock slot) regs)
      (computeSelected tm tape (regularLocalBlock slot) regs))

/-- Dispatch the decoded slot through the fixed lower-center-upper order. -/
def dispatchSlots
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) :
    List Slot → Cmd
  | [] => .skip
  | slot :: slots =>
      Cmd.seq
        (compareImmediate regs (ControlDecode.nodePayload0 regs)
          (CombineTerm.packedValue regs) slot.toFin.val)
        (.ifZero (CombineTerm.packedValue regs)
          (computeTapeSlot tm controller tape slot regs)
          (dispatchSlots tm controller tape regs slots))

/-- Dispatch the decoded named tape through the fixed finite tape family. -/
def dispatchTapes
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    List (TapeIndex workTapeCount) → Cmd
  | [] => .skip
  | tape :: tapes =>
      Cmd.seq
        (compareImmediate regs (ControlDecode.nodeTape regs)
          (CombineTerm.packedValue regs) tape.val)
        (.ifZero (CombineTerm.packedValue regs)
          (dispatchSlots tm controller tape regs
            [.lower, .center, .upper])
          (dispatchTapes tm controller regs tapes))

/-- Decode the active computation node and emit its selected grouped chunk. -/
def build
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [copy (chunkBits regs)
      (CombineValue.rangeRegisters regs).accumulator,
      ControlDecode.decodeNode regs,
      copy (CombineValue.rangeRegisters regs).accumulator
        (chunkBits regs),
      dispatchTapes tm controller regs
        (List.finRange (workTapeCount + 2))]

/-- Observable endpoint of executable packed output-chunk extraction. -/
structure Post
    (tm : TM workTapeCount)
    (blockLength center : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (targetSlot : Slot)
    (word chunkCursor chunkWidth : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- Exact grouped packed output value. -/
  packed_eq :
    final (CombineTerm.packedValue regs) =
      PackedOutputChunkSemantics.packedOutputChunk
        tm blockLength center targetTape targetSlot word
          chunkCursor chunkWidth
  /-- The represented packed local word is restored exactly. -/
  word_eq : final (bankRegisters regs).word = word
  /-- The borrowed remaining-bit counter is exhausted. -/
  remaining_eq : final (remaining regs) = 0
  /-- Current assignment code is preserved. -/
  assignment_eq :
    final (CombineValue.rangeRegisters regs).remaining =
      initial (CombineValue.rangeRegisters regs).remaining
  /-- Outer modular-sum accumulator is restored exactly. -/
  outerAccumulator_eq :
    final (CombineValue.rangeRegisters regs).accumulator =
      initial (CombineValue.rangeRegisters regs).accumulator
  /-- The range driver's canonical one cell is restored. -/
  one_eq : final (CombineValue.rangeRegisters regs).one = 1
  /-- Packed catalytic bank word is untouched. -/
  catalyticWord_eq :
    final regs.layout.bank = initial regs.layout.bank
  /-- Stable parameter and active-frame ABI fields are preserved. -/
  abi : ControlDecode.PreservesABI regs initial final
  /-- Every address outside packed output scratch is preserved. -/
  eq_outside :
    ∀ address, address ∉ PackedLocalStep.footprint regs →
      final address = initial address

end PackedLocalOutputChunk
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
