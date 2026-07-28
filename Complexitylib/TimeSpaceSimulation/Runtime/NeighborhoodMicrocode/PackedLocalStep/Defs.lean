/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineSafeCenter
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalHeadScan.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalRepresentation.Defs

/-!
# Fixed-source transition on a packed local configuration

This definitions layer lowers one transition of a fixed source Turing
machine to direct-register RAM microcode. The source state and every symbol
under a named head are selected by finite, hardwired dispatch trees. Dynamic
packed coordinates are read and replaced by the shared twelve-register bank
interface.

The command depends on the fixed source machine, its state order, and the
fixed number of named tapes. Runtime block length, centers, assignment,
interval, and output coordinate occur only in registers.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalStep

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The exact set of physical scalar slots that may be written by one packed
local step. Live range cells in slots ten and eighteen are saved and restored;
slots twenty-one and thirty-three are genuinely read-only. -/
def writeMap : Fin 17 → Fin 34 :=
  ![0, 1, 4, 5, 6, 9, 10, 11, 12, 17, 18, 19, 20, 29, 30, 31, 32]

theorem writeMap_injective :
    Function.Injective writeMap := by
  decide

/-- Exact finite source-write footprint of the packed local step. -/
def footprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  Finset.univ.image fun slot => regs.index (writeMap slot)

/-- Reuse the local-head scanner's dynamic packed-word allocation. -/
abbrev bankRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    NeighborhoodProgram.BankRegisters :=
  PackedLocalHeadScan.bankRegisters regs

/-- Persistent local-head scratch outside every packed-reader operation. -/
abbrev savedHead
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  (CombineValue.rangeRegisters regs).term

/-- Scratch flag recording whether a writable head is at absolute cell zero. -/
abbrev originFlag
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  Layout.codecScratch regs

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

/-- Compare `value` with a hardwired natural, returning zero in `output`
exactly on equality. -/
def equalImmediate
    (regs : NeighborhoodTrial.Registers controller)
    (value output : ℕ) (constant : ℕ) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [.basic (.imm bank.value constant),
      .basic (.sub bank.test value bank.value),
      .basic (.sub bank.quotient bank.value value),
      .basic (.add output bank.test bank.quotient)]

/-- Read packed state digit zero into the bank result cell. -/
def readState
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [initializeBank tm regs,
      .basic (.imm bank.indexCount 0),
      NeighborhoodProgram.bankRead bank,
      restoreRangeOne regs]

/-- Replace packed state digit zero by a hardwired next-state code. -/
def replaceState
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (nextState : tm.Q)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [initializeBank tm regs,
      .basic (.imm bank.indexCount 0),
      .basic
        (.imm bank.replacement
          (CompactValueCodeSemantics.stateCode order nextState)),
      NeighborhoodProgram.bankReplace bank,
      restoreRangeOne regs]

/-- Dispatch the numeric alphabet code returned by a packed-head scan. -/
def dispatchGamma
    (regs : NeighborhoodTrial.Registers controller)
    (next : Γ → Cmd) : Cmd :=
  let bank := bankRegisters regs
  .ifZero bank.result
    (next .zero)
    (Cmd.seq
      (.basic (.sub bank.test bank.result bank.one))
      (.ifZero bank.test
        (next .one)
        (Cmd.seq
          (.basic (.sub bank.test bank.test bank.one))
          (.ifZero bank.test
            (next .blank)
            (next .start)))))

/-- Scan one compile-time named tape and dispatch on its head symbol. -/
def scanAndDispatch
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (next : Γ → Cmd) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [PackedLocalHeadScan.scan tm tape regs,
      .basic (.imm bank.one 1),
      dispatchGamma regs next]

/-- Recursively scan the fixed work-tape family and accumulate its hardwired
symbol branch. -/
def dispatchWorkHeads
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (next : (Fin workTapeCount → Γ) → Cmd) :
    List (Fin workTapeCount) → (Fin workTapeCount → Γ) → Cmd
  | [], workHeads => next workHeads
  | tape :: tapes, workHeads =>
      scanAndDispatch tm (TapeIndex.work tape) regs fun symbol =>
        dispatchWorkHeads tm regs next tapes
          (Function.update workHeads tape symbol)

/-- Re-decode the computation node and derive the guessed center of one
compile-time tape. -/
def deriveTapeCenter
    (workTapeCount : ℕ)
    (controller : SearchProgram.Registers)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [ControlDecode.decodeNode regs,
      .basic (.imm (ControlDecode.nodeTape regs) tape.val),
      CombineSafeCenter.deriveCenter workTapeCount controller regs]

/-- Save the two live range cells clobbered by node decoding.

The range-one cell temporarily retains the immutable count. Its canonical
entry value is restored after center reconstruction. -/
def saveRangeContext
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (copy (originFlag regs)
      (CombineValue.rangeRegisters regs).accumulator)
    (copy (CombineValue.rangeRegisters regs).one
      (CombineValue.rangeRegisters regs).count)

/-- Restore the live range cells saved across node decoding. -/
def restoreRangeContext
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [copy (CombineValue.rangeRegisters regs).accumulator
        (originFlag regs),
      copy (CombineValue.rangeRegisters regs).count
        (CombineValue.rangeRegisters regs).one,
      restoreRangeOne regs]

/-- Record whether the selected tape head is absolute cell zero.

The exact absolute position is
`(center - 1) * blockLength + savedHead`; testing only whether the center
itself is zero would misclassify the left edge of center block one. -/
def recordOrigin
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [.basic (.imm bank.one 1),
      .basic
        (.sub bank.test
          (CombineSafeCenter.centerValue regs) bank.one),
      .basic
        (.mul bank.test bank.test (Layout.blockLength regs)),
      .basic (.add bank.test bank.test (savedHead regs)),
      .ifZero bank.test
        (.basic (.imm (originFlag regs) 1))
        (.basic (.imm (originFlag regs) 0))]

/-- Prepare the packed coordinate of `savedHead` on one compile-time tape. -/
def prepareSavedCellIndex
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
      .add bank.indexCount (savedHead regs) bank.indexCount,
      .add bank.indexCount bank.indexCount bank.one]

/-- Read the packed cell at the persistent saved local-head coordinate. -/
def readSavedCell
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [initializeBank tm regs,
      prepareSavedCellIndex tape regs,
      NeighborhoodProgram.bankRead bank,
      restoreRangeOne regs]

/-- Replace the packed cell at the persistent saved local-head coordinate. -/
def replaceSavedCell
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [initializeBank tm regs,
      prepareSavedCellIndex tape regs,
      NeighborhoodProgram.bankReplace bank,
      restoreRangeOne regs]

/-- Select the unmarked symbol left at the old head coordinate.

`none` denotes the read-only input tape. A writable tape applies its
hardwired write except at absolute cell zero, where `Tape.write` is a no-op.
-/
def prepareOldCell
    (write : Option Γw)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  let preserveOld :=
    Cmd.seq
      (.basic (.imm bank.value 4))
      (.basic (.sub bank.replacement bank.result bank.value))
  match write with
  | none => preserveOld
  | some symbol =>
      .ifZero (originFlag regs)
        (.basic
          (.imm bank.replacement
            (CompactValueCodeSemantics.gammaCode symbol.toΓ)))
        preserveOld

/-- Update the persistent local-head coordinate by one hardwired direction. -/
def moveSavedHead
    (direction : Dir3)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  match direction with
  | .left =>
      .basic (.sub (savedHead regs) (savedHead regs) bank.one)
  | .right =>
      .basic (.add (savedHead regs) (savedHead regs) bank.one)
  | .stay => .skip

/-- Mark the current saved coordinate while preserving its existing symbol. -/
def markSavedCell
    (tm : TM workTapeCount)
    (tape : TapeIndex workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [readSavedCell tm tape regs,
      .basic (.imm bank.value 4),
      .basic (.add bank.replacement bank.result bank.value),
      replaceSavedCell tm tape regs]

/-- Apply one hardwired write/move action to a named packed tape. -/
def updateTape
    (tm : TM workTapeCount)
    (controller : SearchProgram.Registers)
    (tape : TapeIndex workTapeCount)
    (write : Option Γw)
    (direction : Dir3)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  Cmd.seqList
    [PackedLocalHeadScan.scan tm tape regs,
      copy (savedHead regs) (PackedLocalHeadScan.headOffset regs),
      saveRangeContext regs,
      deriveTapeCenter workTapeCount controller tape regs,
      restoreRangeContext regs,
      recordOrigin regs,
      readSavedCell tm tape regs,
      prepareOldCell write regs,
      replaceSavedCell tm tape regs,
      initializeBank tm regs,
      moveSavedHead direction regs,
      markSavedCell tm tape regs,
      .basic (.imm bank.one 1),
      restoreRangeOne regs]

/-- Apply one completely hardwired transition leaf. -/
def transitionAction
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (state : tm.Q) (inputSymbol : Γ)
    (workSymbols : Fin workTapeCount → Γ)
    (outputSymbol : Γ) : Cmd :=
  match tm.δ state inputSymbol workSymbols outputSymbol with
  | (nextState, workWrites, outputWrite, inputDirection,
      workDirections, outputDirection) =>
      Cmd.seqList
        ([updateTape tm controller (TapeIndex.input workTapeCount)
            none inputDirection regs] ++
          ((List.finRange workTapeCount).map fun tape =>
            updateTape tm controller (TapeIndex.work tape)
              (some (workWrites tape)) (workDirections tape) regs) ++
          [updateTape tm controller (TapeIndex.output workTapeCount)
              (some outputWrite) outputDirection regs,
            replaceState tm order nextState regs])

/-- Apply a hardwired optional write followed by one head movement. -/
def tapeAction
    (tape : Tape) (write : Option Γw) (direction : Dir3) : Tape :=
  match write with
  | none => tape.move direction
  | some symbol => tape.writeAndMove symbol.toΓ direction

/-- Update exactly one named tape of a configuration. -/
def updateNamedTape
    (cfg : Cfg workTapeCount Q)
    (tape : TapeIndex workTapeCount)
    (write : Option Γw) (direction : Dir3) :
    Cfg workTapeCount Q :=
  if hinput : tape.val = 0 then
    { cfg with
      input := tapeAction cfg.input write direction }
  else if houtput : tape.val = workTapeCount + 1 then
    { cfg with
      output := tapeAction cfg.output write direction }
  else
    let index : Fin workTapeCount :=
      ⟨tape.val - 1, by omega⟩
    { cfg with
      work :=
        Function.update cfg.work index
          (tapeAction (cfg.work index) write direction) }

/-- Every named head lies inside its represented three-block window. -/
def HeadsInWindow
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (cfg : Cfg workTapeCount Q) : Prop :=
  ∀ tape,
    PackedLocalConfiguration.windowStart
        blockLength (centers tape) ≤
      (tapeAt cfg tape).head ∧
    (tapeAt cfg tape).head <
      PackedLocalConfiguration.windowStart
          blockLength (centers tape) +
        PackedLocalConfiguration.tapeSpan blockLength

/-- Live caller state preserved even though node decoding time-multiplexes
the physical accumulator and count cells. The term cell is intentionally
absent: it is the persistent local-head scratch during this command. -/
structure PreservesContext
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- Current assignment code is preserved. -/
  assignment_eq :
    final (CombineValue.rangeRegisters regs).remaining =
      initial (CombineValue.rangeRegisters regs).remaining
  /-- Outer modular-sum accumulator is restored exactly. -/
  accumulator_eq :
    final (CombineValue.rangeRegisters regs).accumulator =
      initial (CombineValue.rangeRegisters regs).accumulator
  /-- Immutable assignment count is restored exactly. -/
  count_eq :
    final (CombineValue.rangeRegisters regs).count =
      initial (CombineValue.rangeRegisters regs).count
  /-- The range driver's canonical one cell is restored exactly. -/
  one_eq :
    final (CombineValue.rangeRegisters regs).one =
      initial (CombineValue.rangeRegisters regs).one
  /-- Packed catalytic bank word is untouched. -/
  catalyticWord_eq :
    final regs.layout.bank = initial regs.layout.bank
  /-- Stable parameter and active-frame ABI fields are preserved. -/
  abi : ControlDecode.PreservesABI regs initial final

/-- Exact semantic endpoint of one packed local step. -/
structure Post
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (nextCfg : Cfg workTapeCount tm.Q)
    (suffix : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- The mutable low digits represent the exact frozen next configuration,
  with the suspended high suffix unchanged. -/
  represents :
    PackedLocalRepresentation.Represents
      tm order blockLength centers nextCfg suffix
        (final (bankRegisters regs).word)
  /-- Live caller state is preserved. -/
  context : PreservesContext regs initial final
  /-- Every address outside the exact finite source footprint is preserved. -/
  eq_outside :
    ∀ address, address ∉ footprint regs →
      final address = initial address

/-- Read every hardwired symbol needed by the transition table at one state. -/
def dispatchTransition
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (state : tm.Q) : Cmd :=
  if state = tm.qhalt then
    .skip
  else
    scanAndDispatch tm (TapeIndex.input workTapeCount) regs fun inputSymbol =>
      dispatchWorkHeads tm regs
        (fun workSymbols =>
          scanAndDispatch tm (TapeIndex.output workTapeCount) regs
            (transitionAction tm order controller regs state inputSymbol
              workSymbols))
        (List.finRange workTapeCount)
        (fun _ => Γ.blank)

/-- Dispatch the packed state code through the fixed source-state order. -/
def dispatchStates
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) :
    List tm.Q → Cmd
  | [] => .skip
  | state :: states =>
      let bank := bankRegisters regs
      Cmd.seq
        (equalImmediate regs bank.result bank.buffer
          (CompactValueCodeSemantics.stateCode order state))
        (.ifZero bank.buffer
          (dispatchTransition tm order controller regs state)
          (dispatchStates tm order controller regs states))

/-- Fixed state enumeration induced by the simulator's hardwired order. -/
def states
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm) :
    List tm.Q :=
  (List.finRange (Fintype.card tm.Q)).map order.state.symm

/-- Perform one frozen deterministic source transition on the packed local
configuration. -/
def step
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (readState tm regs)
    (dispatchStates tm order controller regs (states tm order))

end PackedLocalStep
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
