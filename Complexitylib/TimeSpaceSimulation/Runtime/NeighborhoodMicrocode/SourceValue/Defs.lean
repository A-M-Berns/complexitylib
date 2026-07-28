/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation.FiniteEncoding
import Complexitylib.TimeSpaceSimulation.Runtime.InputLookup.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ControlDecode.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Layout.Defs

/-!
# Concrete source-leaf values for neighborhood microcode

An initial neighborhood block has an especially small executable
description.  Its state is the hardwired start state, every head remainder
is zero, and its tape symbols are either the public input block or the
hardwired initialized blank tape.  This module lowers that description to a
fixed first-order RAM command.

`sourceChunk` consumes the node decoder's tape and block fields and the
grouped-coordinate cursor in `Layout.codecScratch`.  It writes one exact
natural residue to the ordinary residue operand cell.  Low public-input
addresses are read from a workspace copy of the controller's collision-safe
prefix cache, so the controller cache itself is never written.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace SourceValue

open RAM Structured
open TreeEval CookMertz

variable {controller : SearchProgram.Registers}

/-- The fixed number of named tapes of the source machine. -/
def tapeCount (workTapeCount : ℕ) : ℕ :=
  workTapeCount + 2

/-- A source tape/block pair packed with the fixed named-tape radix. -/
def tapeBlockCode (workTapeCount tape block : ℕ) : ℕ :=
  tape + tapeCount workTapeCount * block

/-- Numeric alphabet code used by `FiniteEncoding.gammaEquiv` for one
initial tape cell. -/
def initialGammaCode
    (input : List Bool) (tape position : ℕ) : ℕ :=
  if position = 0 then
    3
  else if tape = 0 then
    if position ≤ input.length then
      RAM.initRegs input position
    else
      2
  else
    2

/-- The Boolean source coordinate at one unbounded natural index.

Indices beyond the compact payload are false, matching the trailing padding
of grouped chunks. -/
def coordinateBit
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (blockLength tape block coordinate : ℕ) : Bool :=
  let stateCount := Fintype.card tm.Q
  let startCode := (order.state tm.qstart).val
  if coordinate = startCode then
    true
  else if coordinate = stateCount then
    true
  else if stateCount + blockLength ≤ coordinate ∧
      coordinate < stateCount + 5 * blockLength then
    let cellCode := coordinate - (stateCount + blockLength)
    decide
      (cellCode % 4 =
        initialGammaCode input tape
          (block * blockLength + cellCode / 4))
  else
    false

/-- Numeric form of `coordinateBit`. -/
def coordinateBitValue
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (blockLength tape block coordinate : ℕ) : ℕ :=
  Input.bitValue
    (coordinateBit tm order input blockLength tape block coordinate)

/-- Big-endian binary fold used by the source RAM loop. -/
def forwardChunk
    (bit : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0, accumulator => accumulator
  | coordinate, remaining + 1, accumulator =>
      forwardChunk bit (coordinate + 1) remaining
        (2 * accumulator + bit coordinate)

/-- Pure endpoint of the concrete per-chunk source loop. -/
def sourceChunkValue
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (input : List Bool) (blockLength tape block chunk chunkBits : ℕ) : ℕ :=
  forwardChunk
    (coordinateBitValue tm order input blockLength tape block)
    (chunk * chunkBits) chunkBits 0

/-- Canonical numeric cap for every source-leaf transient of one candidate.

The exponent is the shared fixed-register trial envelope.  The quantitative
invariant theorem proves that the concrete microcode stays below this cap;
its binary width is therefore exactly the budget consumed by the enclosing
residue evaluator. -/
def sourceTransientValueBound
    (tm : TM workTapeCount) (candidate : ℕ) : ℕ :=
  2 ^
      (NeighborhoodProgram.fixedRegisterCount *
        NeighborhoodGraph.WorkspaceAccounting.trialEnvelopeBits
          tm.Q workTapeCount candidate) -
    1

/-- The twelve-register collision-safe input reader used by `sourceChunk`.

The packed input prefix lives in the transient frame-code cell.  Every other
field is reusable scalar scratch.  In particular, neither the continuation
word nor the catalytic-bank word is repurposed. -/
def inputMap : Fin 12 → Fin 34 :=
  ![29, 0, 1, 4, 5, 6, 9, 10, 11, 12, 17, 18]

theorem inputMap_injective :
    Function.Injective inputMap := by
  decide

/-- The exact sixteen physical workspace cells that source evaluation may
write.  The grouped-coordinate cursor and every active scheduler field are
deliberately absent. -/
def writeMap : Fin 16 → Fin 34 :=
  ![29, 0, 1, 4, 5, 6, 9, 10, 11, 12, 17, 18, 19, 20, 21, 30]

theorem writeMap_injective :
    Function.Injective writeMap := by
  decide

/-- Exact direct-write footprint of source evaluation. -/
def writeFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  Finset.univ.image fun slot => regs.index (writeMap slot)

/-- The twelve-register collision-safe input reader used by `sourceChunk`. -/
def inputRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    NeighborhoodProgram.BankRegisters where
  index := fun slot => regs.index (inputMap slot)
  injective := regs.injective.comp inputMap_injective

/-- Packed tape/block pair preserved across collision-safe input reads. -/
abbrev packedTapeBlock
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 20

/-- Recovered grouped-coordinate width. -/
abbrev recoveredChunkBits
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 21

/-- Number of bits still to consume in the active grouped coordinate. -/
abbrev remaining
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 30

/-- Output cell shared with the residue-bank update interface. -/
abbrev operand
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  (Layout.residueScaleRegisters regs).bank.operand

/-- Direct-register copy in the first-order RAM instruction set. -/
def copy (destination source : ℕ) : Cmd :=
  Cmd.seq
    (.basic (.imm destination 0))
    (.basic (.add destination source destination))

/-- Set `output` to one exactly when `value` equals a hardwired constant. -/
def equalImmediate
    (regs : NeighborhoodTrial.Registers controller)
    (value output : ℕ) (constant : ℕ) : Cmd :=
  let inputRegs := inputRegisters regs
  Cmd.seqList
    [.basic (.imm inputRegs.buffer constant),
      .basic (.sub inputRegs.test value inputRegs.buffer),
      .basic (.sub inputRegs.completed inputRegs.buffer value),
      .basic
        (.add inputRegs.test inputRegs.test inputRegs.completed),
      .ifZero inputRegs.test
        (.basic (.imm output 1))
        (.basic (.imm output 0))]

/-- One logarithm iteration while recovering `q` from the runtime radix
`2 ^ q`. -/
def recoverChunkBitsBody
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let inputRegs := inputRegisters regs
  Cmd.seqList
    [NeighborhoodProgram.pop inputRegs.mainStack,
      .basic
        (.add (recoveredChunkBits regs)
          (recoveredChunkBits regs) inputRegs.one),
      .basic
        (.sub inputRegs.test inputRegs.word inputRegs.one)]

/-- Recover the grouped-coordinate width from the preserved chunk radix. -/
def recoverChunkBits
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let inputRegs := inputRegisters regs
  Cmd.seqList
    [copy inputRegs.word (Layout.chunkRadix regs),
      .basic (.imm inputRegs.base 2),
      .basic (.imm inputRegs.basePred 1),
      .basic (.imm inputRegs.one 1),
      .basic (.imm (recoveredChunkBits regs) 0),
      .basic
        (.sub inputRegs.test inputRegs.word inputRegs.one),
      .whileNonzero inputRegs.test (recoverChunkBitsBody regs)]

/-- Recover the decoded tape and block from their preserved fixed-radix
pair.  The tape is returned in `inputRegs.value` and the block in
`inputRegs.buffer`. -/
def decodeTapeBlock
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let inputRegs := inputRegisters regs
  Cmd.seqList
    [copy inputRegs.buffer (packedTapeBlock regs),
      .basic (.imm inputRegs.base (tapeCount workTapeCount)),
      .basic (.imm inputRegs.basePred (tapeCount workTapeCount - 1)),
      .basic (.imm inputRegs.one 1),
      NeighborhoodProgram.peek inputRegs.bufferStack,
      NeighborhoodProgram.pop inputRegs.bufferStack,
      copy inputRegs.indexCount inputRegs.value]

/-- Compare the decoded cell-symbol coordinate with the fixed start-marker
code. -/
def startCellBit
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  equalImmediate regs (inputRegisters regs).value
    (inputRegisters regs).result 3

/-- Compare the decoded cell-symbol coordinate with the fixed blank code. -/
def blankCellBit
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  equalImmediate regs (inputRegisters regs).value
    (inputRegisters regs).result 2

/-- Collision-safe lookup of the positive public-input address held in the
input reader's replacement cell. -/
def lookupInput
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  InputLookup.command (inputRegisters regs)
    (SearchProgram.footprintLimit controller regs.footprint)

/-- Compare an in-range public input bit with the decoded gamma code.

Gamma zero and one are split before lookup, so no gamma scratch needs to
survive the packed-prefix streaming command. -/
def inputCellBit
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let inputRegs := inputRegisters regs
  Cmd.seq
    (equalImmediate regs inputRegs.value inputRegs.result 0)
    (.ifZero inputRegs.result
      (Cmd.seq
        (equalImmediate regs inputRegs.value inputRegs.result 1)
        (.ifZero inputRegs.result
          (.basic (.imm inputRegs.result 0))
          (Cmd.seq
            (lookupInput regs)
            (.ifZero inputRegs.result
              (.basic (.imm inputRegs.result 0))
              (.basic (.imm inputRegs.result 1))))))
      (Cmd.seq
        (lookupInput regs)
        (.ifZero inputRegs.result
          (.basic (.imm inputRegs.result 1))
          (.basic (.imm inputRegs.result 0)))))

/-- Select the initialized tape symbol at the decoded positive-or-zero cell
address in `inputRegs.result`. -/
def initialCellBit
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let inputRegs := inputRegisters regs
  .ifZero inputRegs.result
    (startCellBit regs)
    (.ifZero inputRegs.indexCount
      (Cmd.seq
        (.basic
          (.sub inputRegs.test inputRegs.result
            controller.inputLength))
        (.ifZero inputRegs.test
          (inputCellBit regs)
          (blankCellBit regs)))
      (blankCellBit regs))

/-- Decode a compact cell coordinate and install its absolute initial-tape
address in `result` and `replacement`. -/
def prepareCellBit
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let inputRegs := inputRegisters regs
  Cmd.seqList
    [.basic
      (.mul inputRegs.result inputRegs.buffer
        (Layout.blockLength regs)),
      copy inputRegs.buffer inputRegs.replacement,
      .basic (.imm inputRegs.base 4),
      .basic (.imm inputRegs.basePred 3),
      .basic (.imm inputRegs.one 1),
      NeighborhoodProgram.peek inputRegs.bufferStack,
      NeighborhoodProgram.pop inputRegs.bufferStack,
      .basic
        (.add inputRegs.result inputRegs.result inputRegs.buffer),
      copy inputRegs.replacement inputRegs.result]

/-- Compute one initial tape-cell encoding bit after the compact cell
coordinate has been isolated in `inputRegs.replacement`.

The decoded tape is in `indexCount`; the decoded block is in `buffer`.
-/
def cellBit
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq (prepareCellBit regs) (initialCellBit regs)

/-- Decode the source tape/block and evaluate one already range-checked
compact cell coordinate. -/
def sourceCellBit
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let inputRegs := inputRegisters regs
  let stateCount := Fintype.card tm.Q
  Cmd.seqList
    [decodeTapeBlock workTapeCount regs,
      .basic (.imm inputRegs.value stateCount),
      .basic
        (.add inputRegs.value inputRegs.value
          (Layout.blockLength regs)),
      .basic
        (.sub inputRegs.replacement
          inputRegs.replacement inputRegs.value),
      cellBit regs]

/-- Check the strict upper payload bound and evaluate an in-range cell. -/
def sourceUpperBit
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let inputRegs := inputRegisters regs
  let stateCount := Fintype.card tm.Q
  Cmd.seqList
    [.basic (.imm inputRegs.value 5),
      .basic
        (.mul inputRegs.buffer inputRegs.value
          (Layout.blockLength regs)),
      .basic (.imm inputRegs.value stateCount),
      .basic
        (.add inputRegs.buffer inputRegs.value
          inputRegs.buffer),
      .basic
        (.sub inputRegs.test inputRegs.buffer
          inputRegs.replacement),
      .ifZero inputRegs.test
        (.basic (.imm inputRegs.result 0))
        (sourceCellBit tm regs)]

/-- Compute every non-state/non-head compact source coordinate. -/
def sourcePayloadBit
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let inputRegs := inputRegisters regs
  let stateCount := Fintype.card tm.Q
  Cmd.seqList
    [.basic (.imm inputRegs.buffer stateCount),
      .basic
        (.add inputRegs.buffer inputRegs.buffer
          (Layout.blockLength regs)),
      .basic
        (.sub inputRegs.test inputRegs.buffer
          inputRegs.replacement),
      .ifZero inputRegs.test
        (sourceUpperBit tm regs)
        (.basic (.imm inputRegs.result 0))]

/-- Compute one compact source-coordinate bit.

The global coordinate is supplied in `inputRegs.replacement`, the decoded
tape in `indexCount`, and the decoded block in `buffer`.  The resulting
Boolean natural is returned in `inputRegs.result`. -/
def sourceBit
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let inputRegs := inputRegisters regs
  let stateCount := Fintype.card tm.Q
  let startCode := (order.state tm.qstart).val
  Cmd.seq
    (equalImmediate regs inputRegs.replacement
      inputRegs.result startCode)
    (.ifZero inputRegs.result
      (Cmd.seq
        (equalImmediate regs inputRegs.replacement
          inputRegs.result stateCount)
        (.ifZero inputRegs.result
          (sourcePayloadBit tm regs)
          .skip))
      .skip)

/-- One bit-consumption step of the concrete grouped source encoder. -/
def sourceChunkBody
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let inputRegs := inputRegisters regs
  Cmd.seqList
    [decodeTapeBlock workTapeCount regs,
      .basic
        (.mul inputRegs.replacement
          (Layout.codecScratch regs) (recoveredChunkBits regs)),
      .basic
        (.add inputRegs.replacement inputRegs.replacement
          (recoveredChunkBits regs)),
      .basic
        (.sub inputRegs.replacement inputRegs.replacement
          (remaining regs)),
      sourceBit tm order regs,
      .basic (.imm inputRegs.base 2),
      .basic (.mul (operand regs) (operand regs) inputRegs.base),
      .basic (.add (operand regs) inputRegs.result (operand regs)),
      .basic
        (.sub (remaining regs) (remaining regs) inputRegs.one)]

/-- Fixed first-order computation of one grouped source residue.

Entry ABI:

* `ControlDecode.nodeTape` and `nodePayload0` contain a decoded source node;
* `Layout.codecScratch` is the grouped-coordinate cursor;
* the controller input frame is valid.

Exit ABI: `operand` contains the exact natural source residue. -/
def sourceChunk
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let inputRegs := inputRegisters regs
  Cmd.seqList
    [.basic
      (.imm (packedTapeBlock regs) (tapeCount workTapeCount)),
      .basic
        (.mul (packedTapeBlock regs)
          (ControlDecode.nodePayload0 regs) (packedTapeBlock regs)),
      .basic
        (.add (packedTapeBlock regs)
          (ControlDecode.nodeTape regs) (packedTapeBlock regs)),
      recoverChunkBits regs,
      copy (remaining regs) (recoveredChunkBits regs),
      copy inputRegs.word controller.prefixCache,
      .basic (.imm (operand regs) 0),
      .whileNonzero (remaining regs)
        (sourceChunkBody tm order regs)]

/-- The canonical failure value has zero in every residue coordinate. -/
def failureChunk
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  .basic (.imm (operand regs) 0)

/-- Observable endpoint of source-leaf evaluation.

Besides the exact residue operand, this records every field consumed by the
immediately following catalytic-bank update. -/
structure SourceChunkPost
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (expected : ℕ)
    (initial final : Store) : Prop where
  /-- The requested natural source residue is installed exactly. -/
  operand_eq : final (operand regs) = expected
  /-- Collision-safe public-input access remains valid. -/
  inputFrame :
    SearchProgram.InputFrame controller regs.footprint input final
  /-- Active scheduler fields are read-only. -/
  fuel_eq : final (Layout.fuel regs) = initial (Layout.fuel regs)
  nodeCode_eq :
    final (Layout.nodeCode regs) = initial (Layout.nodeCode regs)
  scalar_eq : final (Layout.scalar regs) = initial (Layout.scalar regs)
  out_eq : final (Layout.out regs) = initial (Layout.out regs)
  phaseCode_eq :
    final (Layout.phaseCode regs) = initial (Layout.phaseCode regs)
  active_eq : final (Layout.active regs) = initial (Layout.active regs)
  /-- The grouped-coordinate cursor remains available to the update. -/
  cursor_eq :
    final (Layout.codecScratch regs) =
      initial (Layout.codecScratch regs)
  /-- Packed-bank state and arithmetic constants remain available to the
  update. -/
  bankWord_eq :
    final (Layout.residueScaleRegisters regs).bank.bank.word =
      initial (Layout.residueScaleRegisters regs).bank.bank.word
  bankBase_eq :
    final (Layout.residueScaleRegisters regs).bank.bank.base =
      initial (Layout.residueScaleRegisters regs).bank.bank.base
  modulus_eq :
    final (Layout.residueScaleRegisters regs).bank.modulus =
      initial (Layout.residueScaleRegisters regs).bank.modulus
  modulusPred_eq :
    final (Layout.residueScaleRegisters regs).bank.modulusPred =
      initial (Layout.residueScaleRegisters regs).bank.modulusPred

end SourceValue
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
