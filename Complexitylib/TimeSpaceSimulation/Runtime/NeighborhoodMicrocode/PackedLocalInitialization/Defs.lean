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

/-!
# Fixed-source initialization of a packed local configuration

This definitions layer decodes one streamed Boolean assignment into the
packed finite configuration used by the local transition kernel. The source
command depends only on the fixed simulated machine, its state order, and
the register allocation. Block length, assignment code, guessed centers,
interval, and continuation suffix are runtime register values.

Each named tape is emitted from high coordinates to low coordinates. A
runtime guessed-center test handles the truncated block-zero neighborhood:
at center zero the represented blocks are lower, upper, and blank, because
the lower and center slots both name block zero and `matchingSlot` selects
the lower slot first.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalInitialization

open RAM Structured
open NeighborhoodGraph

variable {controller : SearchProgram.Registers}

/-- Reuse the packed local-head reader's collision-free bank allocation. -/
abbrev bankRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    NeighborhoodProgram.BankRegisters :=
  PackedLocalHeadScan.bankRegisters regs

/-- Runtime loop counter and decoded head remainder. -/
abbrev cursor
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  (CombineValue.rangeRegisters regs).term

/-- Runtime semantic payload coordinate, also used for an encoded head
selection between payload reads. -/
abbrev payloadPosition
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  AssignmentPayloadBit.payloadPosition regs

/-- Boolean lookup result and decoded finite symbol/state code. -/
abbrev decodedValue
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  CombineTerm.packedValue regs

/-- The local configuration word being built below its suspended suffix. -/
abbrev packedWord
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  (bankRegisters regs).word

/-- Exact physical slots written by packed initialization.

The streamed assignment in slot 21 and the catalytic bank in slot 33 are
read-only throughout the initializer.
-/
def writeMap : Fin 17 → Fin 34 :=
  ![0, 1, 4, 5, 6, 9, 10, 11, 12, 17, 18, 19, 20, 29, 30, 31, 32]

theorem writeMap_injective :
    Function.Injective writeMap := by
  decide

/-- Complete exact fixed write footprint of packed initialization. -/
def footprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  Finset.univ.image fun slot => regs.index (writeMap slot)

/-- Direct-register copy. -/
def copy (destination source : ℕ) : Cmd :=
  Cmd.seq
    (.basic (.imm destination 0))
    (.basic (.add destination source destination))

/-- Initialize the fixed local-configuration radix interface. -/
def initializeBank
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.basics
    [.imm bank.base (PackedLocalConfiguration.radix tm),
      .imm bank.basePred (PackedLocalConfiguration.radix tm - 1),
      .imm bank.one 1]

/-- Restore the range driver's time-multiplexed constant-one cell. -/
def restoreRangeOne
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  .basic (.imm (CombineValue.rangeRegisters regs).one 1)

/-- Fixed child coordinate for one semantic predecessor role. -/
def childIndex
    (workTapeCount : ℕ)
    (index : PredecessorIndex workTapeCount) :
    Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) :=
  predecessorIndexEquiv workTapeCount index

/-- Compute the semantic payload coordinate of one alphabet bit at the
current block offset. -/
def prepareCellPosition
    (tm : TM workTapeCount)
    (symbol : Γ)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [.basic
        (.imm (payloadPosition regs) (Fintype.card tm.Q)),
      .basic
        (.add (payloadPosition regs) (payloadPosition regs)
          (Layout.blockLength regs)),
      .basic (.imm bank.value 4),
      .basic (.mul bank.value (cursor regs) bank.value),
      .basic
        (.add (payloadPosition regs) (payloadPosition regs)
          bank.value),
      .basic
        (.imm bank.value
          (NeighborhoodExecutableEvaluation.FiniteEncoding.gammaEquiv
            symbol).val),
      .basic
        (.add (payloadPosition regs) (payloadPosition regs)
          bank.value)]

/-- Read one fixed alphabet coordinate of one fixed content child. -/
def readCellBit
    (tm : TM workTapeCount)
    (slot : Slot)
    (tape : TapeIndex workTapeCount)
    (symbol : Γ)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (prepareCellPosition tm symbol regs)
    (AssignmentPayloadBit.read workTapeCount regs
      (childIndex workTapeCount (.content slot, tape)))

/-- Decode one tape symbol with exactly the total priority order used by
`NeighborhoodExecutableEvaluation.decodeGamma`. -/
def decodeCell
    (tm : TM workTapeCount)
    (slot : Slot)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (readCellBit tm slot tape .zero regs)
    (.ifZero (decodedValue regs)
      (Cmd.seq
        (readCellBit tm slot tape .one regs)
        (.ifZero (decodedValue regs)
          (Cmd.seq
            (readCellBit tm slot tape .blank regs)
            (.ifZero (decodedValue regs)
              (Cmd.seq
                (readCellBit tm slot tape .start regs)
                (.ifZero (decodedValue regs)
                  (.basic
                    (.imm (decodedValue regs)
                      (CompactValueCodeSemantics.gammaCode .blank)))
                  (.basic
                    (.imm (decodedValue regs)
                      (CompactValueCodeSemantics.gammaCode .start)))))
              (.basic
                (.imm (decodedValue regs)
                  (CompactValueCodeSemantics.gammaCode .blank)))))
          (.basic
            (.imm (decodedValue regs)
              (CompactValueCodeSemantics.gammaCode .one)))))
      (.basic
        (.imm (decodedValue regs)
          (CompactValueCodeSemantics.gammaCode .zero))))

/-- Push the decoded code as a new least-significant packed digit. -/
def pushDecoded
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [initializeBank tm regs,
      copy bank.value (decodedValue regs),
      NeighborhoodProgram.push bank.mainStack]

/-- Decode and push one content cell at the current block offset. -/
def pushCell
    (tm : TM workTapeCount)
    (slot : Slot)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (decodeCell tm slot tape regs)
    (pushDecoded tm regs)

/-- One descending-offset content-block iteration. -/
def pushBlockBody
    (tm : TM workTapeCount)
    (slot : Slot)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (.basic
      (.sub (cursor regs) (cursor regs)
        (CombineValue.rangeRegisters regs).one))
    (pushCell tm slot tape regs)

/-- Push one runtime-length content block from high offset to low offset. -/
def pushBlock
    (tm : TM workTapeCount)
    (slot : Slot)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [.basic (.imm (CombineValue.rangeRegisters regs).one 1),
      copy (cursor regs) (Layout.blockLength regs),
      .whileNonzero (cursor regs)
        (pushBlockBody tm slot tape regs)]

/-- One descending-offset constant-blank block iteration. -/
def pushBlankBody
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [.basic
      (.sub (cursor regs) (cursor regs)
        (CombineValue.rangeRegisters regs).one),
      .basic
        (.imm (decodedValue regs)
          (CompactValueCodeSemantics.gammaCode .blank)),
      pushDecoded tm regs]

/-- Push one runtime-length blank block from high offset to low offset. -/
def pushBlankBlock
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [.basic (.imm (CombineValue.rangeRegisters regs).one 1),
      copy (cursor regs) (Layout.blockLength regs),
      .whileNonzero (cursor regs) (pushBlankBody tm regs)]

/-- Re-decode the active computation node and derive one tape's guessed
center. -/
def deriveTapeCenter
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [ControlDecode.decodeNode regs,
      .basic (.imm (ControlDecode.nodeTape regs) tape.val),
      CombineSafeCenter.deriveCenter workTapeCount controller regs]

/-- Compute the chronological head-remainder coordinate at the current
ascending offset. -/
def prepareHeadPosition
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [.basic
      (.imm (payloadPosition regs) (Fintype.card tm.Q)),
      .basic
        (.add (payloadPosition regs) (payloadPosition regs)
          (Layout.blockLength regs)),
      .basic
        (.sub (payloadPosition regs) (payloadPosition regs)
          (cursor regs)),
      .basic (.imm bank.value 0)]

/-- One first-true head-remainder scan iteration.

The payload cell stores zero after a false bit. After a true bit it stores
the selected remainder plus one and the loop counter is cleared. Thus an
all-false vector canonically decodes to remainder zero.
-/
def decodeHeadBody
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [prepareHeadPosition tm regs,
      AssignmentPayloadBit.read workTapeCount regs
        (childIndex workTapeCount (.chronological, tape)),
      .ifZero (decodedValue regs)
        (Cmd.seq
          (.basic (.imm (payloadPosition regs) 0))
          (.basic
            (.sub (cursor regs) (cursor regs)
              (CombineValue.rangeRegisters regs).one)))
        (Cmd.seqList
          [.basic (.imm bank.value (Fintype.card tm.Q)),
            .basic
              (.sub (payloadPosition regs) (payloadPosition regs)
                bank.value),
            .basic
              (.add (payloadPosition regs) (payloadPosition regs)
                (CombineValue.rangeRegisters regs).one),
            .basic (.imm (cursor regs) 0)])]

/-- Decode the first true chronological head-remainder coordinate. -/
def decodeHead
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [.basic (.imm (CombineValue.rangeRegisters regs).one 1),
      copy (cursor regs) (Layout.blockLength regs),
      .basic (.imm (payloadPosition regs) 0),
      .whileNonzero (cursor regs) (decodeHeadBody tm tape regs),
      .basic
        (.sub (cursor regs) (payloadPosition regs)
          (CombineValue.rangeRegisters regs).one)]

/-- Mark the decoded named head in the just-emitted low-order tape block.

`centerOffsetBlocks` is zero at the truncated left boundary and one at every
positive center.
-/
def markHead
    (tm : TM workTapeCount)
    (centerOffsetBlocks : ℕ)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [.basic (.imm bank.value centerOffsetBlocks),
      .basic
        (.mul bank.value bank.value (Layout.blockLength regs)),
      .basic (.add (cursor regs) (cursor regs) bank.value),
      initializeBank tm regs,
      copy bank.indexCount (cursor regs),
      NeighborhoodProgram.bankRead bank,
      .basic (.imm bank.value 4),
      .basic (.add bank.replacement bank.result bank.value),
      copy bank.indexCount (cursor regs),
      NeighborhoodProgram.bankReplace bank,
      restoreRangeOne regs]

/-- Emit one named tape at the truncated center-zero boundary. -/
def initializeBoundaryTape
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [pushBlankBlock tm regs,
      pushBlock tm .upper tape regs,
      pushBlock tm .lower tape regs,
      decodeHead tm tape regs,
      markHead tm 0 regs]

/-- Emit one named tape at a positive guessed center. -/
def initializeRegularTape
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [pushBlock tm .upper tape regs,
      pushBlock tm .center tape regs,
      pushBlock tm .lower tape regs,
      decodeHead tm tape regs,
      markHead tm 1 regs]

/-- Decode one tape center, emit its three finite blocks, and mark its head.

Control decoding time-multiplexes the outer accumulator and immutable count.
The two values are therefore saved in initializer scratch, restored before
emission, and then left untouched by both emission branches.
-/
def initializeTape
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [copy (cursor regs)
      (CombineValue.rangeRegisters regs).accumulator,
      copy (payloadPosition regs)
        (CombineValue.rangeRegisters regs).count,
      deriveTapeCenter workTapeCount controller tape regs,
      copy (CombineValue.rangeRegisters regs).accumulator
        (cursor regs),
      copy (CombineValue.rangeRegisters regs).count
        (payloadPosition regs),
      .ifZero (CombineSafeCenter.centerValue regs)
        (initializeBoundaryTape tm tape regs)
        (initializeRegularTape tm tape regs)]

/-- Initialize a compile-time list of named tapes in the supplied order. -/
def initializeTapes
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    List (TapeIndex workTapeCount) → Cmd
  | [] => .skip
  | tape :: tapes =>
      Cmd.seq
        (initializeTape tm controller tape regs)
        (initializeTapes tm controller regs tapes)

/-- Descending named-tape order needed for little-endian prefix emission. -/
def tapes (workTapeCount : ℕ) :
    List (TapeIndex workTapeCount) :=
  (List.finRange (workTapeCount + 2)).reverse

/-- Read one fixed state coordinate of the chronological input child. -/
def readStateBit
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (state : tm.Q)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (.basic
      (.imm (payloadPosition regs)
        (CompactValueCodeSemantics.stateCode order state)))
    (AssignmentPayloadBit.read workTapeCount regs
      (childIndex workTapeCount
        (.chronological, TapeIndex.input workTapeCount)))

/-- Decode the first true state in the hardwired source-state order. -/
def decodeStates
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) :
    List tm.Q → Cmd
  | [] =>
      .basic
        (.imm (decodedValue regs)
          (CompactValueCodeSemantics.stateCode order tm.qstart))
  | state :: states =>
      Cmd.seq
        (readStateBit tm order state regs)
        (.ifZero (decodedValue regs)
          (decodeStates tm order regs states)
          (.basic
            (.imm (decodedValue regs)
              (CompactValueCodeSemantics.stateCode order state))))

/-- Fixed state enumeration induced by the simulator's hardwired order. -/
def states
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm) :
    List tm.Q :=
  (List.finRange (Fintype.card tm.Q)).map order.state.symm

/-- Decode and push the low-order packed state digit. -/
def initializeState
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (decodeStates tm order regs (states tm order))
    (pushDecoded tm regs)

/-- Build the complete packed local start configuration below the caller's
existing continuation suffix.

The descending tape traversal and descending within-block traversal make
the final state digit coordinate zero, followed by tape-major local cells.
-/
def build
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (initializeTapes tm controller regs (tapes workTapeCount))
    (initializeState tm order regs)

/-- Observable endpoint and stable frame of packed initialization. -/
structure Post
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (guess : Guess.CenterGuess workTapeCount horizon)
    (interval : Fin horizon)
    (code suffix : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- Exact packed local start configuration below the input suffix. -/
  word_eq :
    final (packedWord regs) =
      PackedLocalConfiguration.assignmentStartWord
        tm order blockLength hpositive guess interval code suffix
  /-- The streamed assignment code is preserved. -/
  assignment_eq :
    final (CombineValue.rangeRegisters regs).remaining = code
  /-- The outer modular-sum accumulator is preserved. -/
  accumulator_eq :
    final (CombineValue.rangeRegisters regs).accumulator =
      initial (CombineValue.rangeRegisters regs).accumulator
  /-- The field modulus is preserved. -/
  modulus_eq :
    final (CombineValue.rangeRegisters regs).modulus =
      initial (CombineValue.rangeRegisters regs).modulus
  /-- The field-modulus predecessor is preserved. -/
  modulusPred_eq :
    final (CombineValue.rangeRegisters regs).modulusPred =
      initial (CombineValue.rangeRegisters regs).modulusPred
  /-- The range driver's constant one is restored. -/
  one_eq :
    final (CombineValue.rangeRegisters regs).one = 1
  /-- The immutable assignment count is preserved. -/
  count_eq :
    final (CombineValue.rangeRegisters regs).count =
      initial (CombineValue.rangeRegisters regs).count
  /-- The packed catalytic bank remains untouched. -/
  catalyticWord_eq :
    final regs.layout.bank = initial regs.layout.bank
  /-- Every active-frame and runtime-parameter ABI field is preserved. -/
  abi : ControlDecode.PreservesABI regs initial final
  /-- Every address outside combine scratch is preserved. -/
  eq_outside :
    ∀ address, address ∉ footprint regs →
      final address = initial address

end PackedLocalInitialization
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
