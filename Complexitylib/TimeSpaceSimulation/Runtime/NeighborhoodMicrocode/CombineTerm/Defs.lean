/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Structured.RuntimeArithmetic.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.Arithmetic.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineValue.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation.Defs

/-!
# Fixed-register assignment digits and combine-term composition

This definitions layer implements two uniform pieces below
`CombineTermKernelSpecAt`.

* `seekDigit` extracts an arbitrary runtime radix digit by repeatedly taking
  quotients; its source command is independent of the digit index and radix.
* `combineTerm` composes separately generated packed-node and tensor-basis
  factors, then performs their concrete modular multiplication into the range
  fold's term register.

The two factor generators remain explicit contracts.  In particular, no
nonuniform truth table for the arbitrary Boolean callback is hidden here.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CombineTerm

open RAM Structured
open TreeEval CookMertz

variable {controller : SearchProgram.Registers}

/-- Six pairwise-distinct registers for one dynamic radix-digit lookup. -/
structure DigitRegisters where
  /-- Allocation order: word/remainder, quotient, test, one, divisor,
  and digit-index countdown. -/
  index : Fin 6 → ℕ
  /-- Logical digit registers are physically distinct. -/
  injective : Function.Injective index

namespace DigitRegisters

/-- Word on entry and selected radix digit on exit. -/
abbrev value (regs : DigitRegisters) : ℕ := regs.index 0

/-- Quotient scratch. -/
abbrev quotient (regs : DigitRegisters) : ℕ := regs.index 1

/-- Division-loop test scratch. -/
abbrev test (regs : DigitRegisters) : ℕ := regs.index 2

/-- Constant one established by quotient/remainder division. -/
abbrev one (regs : DigitRegisters) : ℕ := regs.index 3

/-- Positive read-only runtime radix. -/
abbrev divisor (regs : DigitRegisters) : ℕ := regs.index 4

/-- Number of low-order digits skipped before the selected digit. -/
abbrev cursor (regs : DigitRegisters) : ℕ := regs.index 5

/-- Reuse the verified quotient/remainder interface. -/
def division (regs : DigitRegisters) :
    ControlDecode.DivisionRegisters where
  index := fun slot => regs.index ⟨slot.val, by omega⟩
  injective := by
    intro first second heq
    apply Fin.ext
    have hindex := regs.injective heq
    simpa using congrArg Fin.val hindex

/-- Exact mutable footprint of dynamic radix-digit lookup. -/
def writeFootprint (regs : DigitRegisters) : Finset ℕ :=
  {regs.value, regs.quotient, regs.test, regs.one, regs.cursor}

end DigitRegisters

/-- Direct-register copy used between destructive division stages. -/
def copy (destination source : ℕ) : Cmd :=
  Cmd.seq
    (.basic (.imm destination 0))
    (.basic (.add destination source destination))

/-- Quotient after skipping `index` low-order radix digits. -/
def radixQuotient (radix : ℕ) : ℕ → ℕ → ℕ
  | 0, word => word
  | index + 1, word =>
      radixQuotient radix index (word / radix)

/-- The natural radix digit at a zero-based low-order index. -/
def radixDigit (radix word index : ℕ) : ℕ :=
  word / radix ^ index % radix

/-- Skip one low-order digit and decrement the dynamic cursor. -/
def seekBody (regs : DigitRegisters) : Cmd :=
  Cmd.seqList
    [ControlDecode.divRem regs.division,
      copy regs.value regs.quotient,
      .basic (.sub regs.cursor regs.cursor regs.one)]

/-- Extract the radix digit selected by the dynamic cursor.

The loop first skips `cursor` digits.  One final quotient/remainder stage
leaves the selected digit in `value`.
-/
def seekDigit (regs : DigitRegisters) : Cmd :=
  Cmd.seq
    (.whileNonzero regs.cursor (seekBody regs))
    (ControlDecode.divRem regs.division)

/-- Exact observable result of one dynamic radix-digit lookup. -/
structure DigitPost
    (regs : DigitRegisters) (radix word index : ℕ)
    (initial final : Store) : Prop where
  /-- Exact selected low-order radix digit. -/
  value_eq :
    final regs.value = radixDigit radix word index
  /-- The dynamic cursor is exhausted. -/
  cursor_eq : final regs.cursor = 0
  /-- The radix is preserved. -/
  divisor_eq : final regs.divisor = radix
  /-- The reusable constant one is established. -/
  one_eq : final regs.one = 1
  /-- Every address outside the five direct destinations is preserved. -/
  eq_outside :
    ∀ address, address ∉ regs.writeFootprint →
      final address = initial address

/-- Physical digit-lookup view inside combine scratch.

The digit is returned directly in the range term cell.  The divisor reuses
the read-only frame-code radix `2 ^ chunkBits`.
-/
def assignmentDigitRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    DigitRegisters where
  index := fun slot =>
    regs.index (![19, 20, 4, 17, 8, 29] slot)
  injective := regs.injective.comp (by decide)

/-- Dynamic low-order digit index supplied to assignment lookup. -/
abbrev assignmentDigitIndex
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 30

/-- Copy the current assignment code and requested digit index, then extract
that radix digit into the range term register. -/
def assignmentDigit
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let digit := assignmentDigitRegisters regs
  let range := CombineValue.rangeRegisters regs
  Cmd.seqList
    [copy digit.value range.remaining,
      copy digit.cursor (assignmentDigitIndex regs),
      seekDigit digit]

/-- Assignment-digit lookup preserves the enclosing range-fold interface. -/
structure AssignmentDigitPost
    (regs : NeighborhoodTrial.Registers controller)
    (radix code index : ℕ)
    (initial final : Store) : Prop where
  /-- Exact arithmetic digit returned in the range term cell. -/
  term_eq :
    final (CombineValue.rangeRegisters regs).term =
      radixDigit radix code index
  /-- Fold accumulator is preserved. -/
  accumulator_eq :
    final (CombineValue.rangeRegisters regs).accumulator =
      initial (CombineValue.rangeRegisters regs).accumulator
  /-- Current assignment code is preserved. -/
  remaining_eq :
    final (CombineValue.rangeRegisters regs).remaining = code
  /-- Field modulus is preserved. -/
  modulus_eq :
    final (CombineValue.rangeRegisters regs).modulus =
      initial (CombineValue.rangeRegisters regs).modulus
  /-- Field-modulus predecessor is preserved. -/
  modulusPred_eq :
    final (CombineValue.rangeRegisters regs).modulusPred =
      initial (CombineValue.rangeRegisters regs).modulusPred
  /-- Fold constant one is preserved. -/
  one_eq :
    final (CombineValue.rangeRegisters regs).one =
      initial (CombineValue.rangeRegisters regs).one
  /-- Immutable assignment count is preserved. -/
  count_eq :
    final (CombineValue.rangeRegisters regs).count =
      initial (CombineValue.rangeRegisters regs).count
  /-- Requested digit index is preserved at its source cell. -/
  index_eq : final (assignmentDigitIndex regs) = index

/-- Scratch register holding the packed Boolean-node factor. -/
abbrev packedValue
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 6

/-- Scratch register holding the tensor-product basis factor. -/
abbrev basisValue
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 32

/-- Modular-reduction view whose output is the range term register. -/
def termReduceRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    RuntimeArithmetic.ReduceRegisters where
  value := (CombineValue.rangeRegisters regs).term
  modulus := (CombineValue.rangeRegisters regs).modulus
  modulusPred := (CombineValue.rangeRegisters regs).modulusPred
  test := (CombineValue.rangeRegisters regs).test
  value_ne_modulus := regs.injective.ne (by decide)
  value_ne_modulusPred := regs.injective.ne (by decide)
  value_ne_test := regs.injective.ne (by decide)
  modulus_ne_modulusPred := regs.injective.ne (by decide)
  modulus_ne_test := regs.injective.ne (by decide)
  modulusPred_ne_test := regs.injective.ne (by decide)

/-- Observable contract for a packed-node-factor kernel. -/
structure PackedPost
    (regs : NeighborhoodTrial.Registers controller)
    (value index : ℕ) (initial final : Store) : Prop where
  /-- Exact packed Boolean-node factor. -/
  packed_eq : final (packedValue regs) = value
  /-- Fold accumulator is preserved. -/
  accumulator_eq :
    final (CombineValue.rangeRegisters regs).accumulator =
      initial (CombineValue.rangeRegisters regs).accumulator
  /-- Assignment code is preserved. -/
  remaining_eq :
    final (CombineValue.rangeRegisters regs).remaining = index
  /-- Modulus is preserved. -/
  modulus_eq :
    final (CombineValue.rangeRegisters regs).modulus =
      initial (CombineValue.rangeRegisters regs).modulus
  /-- Modulus predecessor is preserved. -/
  modulusPred_eq :
    final (CombineValue.rangeRegisters regs).modulusPred =
      initial (CombineValue.rangeRegisters regs).modulusPred
  /-- Constant one is preserved. -/
  one_eq :
    final (CombineValue.rangeRegisters regs).one =
      initial (CombineValue.rangeRegisters regs).one
  /-- Immutable assignment count is preserved. -/
  count_eq :
    final (CombineValue.rangeRegisters regs).count =
      initial (CombineValue.rangeRegisters regs).count

/-- Observable contract for a basis-factor kernel, including preservation of
the packed factor computed immediately before it. -/
structure BasisPost
    (regs : NeighborhoodTrial.Registers controller)
    (value index : ℕ) (initial final : Store) : Prop where
  /-- Exact tensor-product basis factor. -/
  basis_eq : final (basisValue regs) = value
  /-- Previously generated packed factor is preserved. -/
  packed_eq :
    final (packedValue regs) = initial (packedValue regs)
  /-- Fold accumulator is preserved. -/
  accumulator_eq :
    final (CombineValue.rangeRegisters regs).accumulator =
      initial (CombineValue.rangeRegisters regs).accumulator
  /-- Assignment code is preserved. -/
  remaining_eq :
    final (CombineValue.rangeRegisters regs).remaining = index
  /-- Modulus is preserved. -/
  modulus_eq :
    final (CombineValue.rangeRegisters regs).modulus =
      initial (CombineValue.rangeRegisters regs).modulus
  /-- Modulus predecessor is preserved. -/
  modulusPred_eq :
    final (CombineValue.rangeRegisters regs).modulusPred =
      initial (CombineValue.rangeRegisters regs).modulusPred
  /-- Constant one is preserved. -/
  one_eq :
    final (CombineValue.rangeRegisters regs).one =
      initial (CombineValue.rangeRegisters regs).one
  /-- Immutable assignment count is preserved. -/
  count_eq :
    final (CombineValue.rangeRegisters regs).count =
      initial (CombineValue.rangeRegisters regs).count

/-- Correctness contract for the packed-node factor under field invariants. -/
def PackedKernelSpecAt
    (regs : NeighborhoodTrial.Registers controller)
    (kernel : Cmd) (modulus : ℕ) (value : ℕ → ℕ) : Prop :=
  ∀ (store : Store) (index : ℕ),
    store (CombineValue.rangeRegisters regs).remaining = index →
    store (CombineValue.rangeRegisters regs).modulus = modulus →
    store (CombineValue.rangeRegisters regs).modulusPred =
      modulus - 1 →
    store (CombineValue.rangeRegisters regs).one = 1 →
    ∃ final,
      Runs kernel store final ∧
      PackedPost regs (value index) index store final

/-- Correctness contract for the tensor-basis factor under field
invariants. -/
def BasisKernelSpecAt
    (regs : NeighborhoodTrial.Registers controller)
    (kernel : Cmd) (modulus : ℕ) (value : ℕ → ℕ) : Prop :=
  ∀ (store : Store) (index : ℕ),
    store (CombineValue.rangeRegisters regs).remaining = index →
    store (CombineValue.rangeRegisters regs).modulus = modulus →
    store (CombineValue.rangeRegisters regs).modulusPred =
      modulus - 1 →
    store (CombineValue.rangeRegisters regs).one = 1 →
    ∃ final,
      Runs kernel store final ∧
      BasisPost regs (value index) index store final

/-- A packed-factor contract relative to a semantic representation of the
concrete store.  The representation is available to the factor kernel and
must be restored on exit. -/
def PackedKernelSpecAtContext
    (regs : NeighborhoodTrial.Registers controller)
    (kernel : Cmd) (modulus : ℕ) (value : ℕ → ℕ)
    (context : Store → Prop) : Prop :=
  ∀ (store : Store) (index : ℕ),
    context store →
    store (CombineValue.rangeRegisters regs).remaining = index →
    store (CombineValue.rangeRegisters regs).modulus = modulus →
    store (CombineValue.rangeRegisters regs).modulusPred =
      modulus - 1 →
    store (CombineValue.rangeRegisters regs).one = 1 →
    ∃ final,
      Runs kernel store final ∧
      PackedPost regs (value index) index store final ∧
      context final

/-- A basis-factor contract relative to a semantic representation of the
concrete store.  In particular, a packed-bank representation can justify
dynamic coordinate reads without requiring the kernel to work on arbitrary
garbage stores. -/
def BasisKernelSpecAtContext
    (regs : NeighborhoodTrial.Registers controller)
    (kernel : Cmd) (modulus : ℕ) (value : ℕ → ℕ)
    (context : Store → Prop) : Prop :=
  ∀ (store : Store) (index : ℕ),
    context store →
    store (CombineValue.rangeRegisters regs).remaining = index →
    store (CombineValue.rangeRegisters regs).modulus = modulus →
    store (CombineValue.rangeRegisters regs).modulusPred =
      modulus - 1 →
    store (CombineValue.rangeRegisters regs).one = 1 →
    ∃ final,
      Runs kernel store final ∧
      BasisPost regs (value index) index store final ∧
      context final

/-- Generate both semantic factors and multiply them modulo the runtime
field into the range term register. -/
def combineTerm
    (regs : NeighborhoodTrial.Registers controller)
    (packedKernel basisKernel : Cmd) : Cmd :=
  Cmd.seqList
    [packedKernel,
      basisKernel,
      RuntimeArithmetic.mulMod (termReduceRegisters regs)
        (packedValue regs) (basisValue regs)]

/-- Exact packed-node factor for one assignment code. -/
def packedAssignmentValue
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn))
    (code : ℕ) : ℕ :=
  let assignment :=
    GroupedExtension.Evaluation.chunkAssignmentOfCode
      finProdFinEquiv
      (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
      code
  NeighborhoodExecutableEvaluation.Residue.packedNodeValue
    payloadWidth fanIn combine assignment outputChunk

/-- Exact tensor-product basis factor for one assignment code. -/
def basisAssignmentValue
    (payloadWidth fanIn : ℕ)
    (args :
      Fin fanIn →
        Fin
          (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn) →
          ℕ)
    (code : ℕ) : ℕ :=
  let assignment :=
    GroupedExtension.Evaluation.chunkAssignmentOfCode
      finProdFinEquiv
      (PrimeGrouped.Logarithmic.chunkBits payloadWidth fanIn)
      code
  NeighborhoodExecutableEvaluation.Residue.basisValue
    payloadWidth fanIn assignment
    (fun input => args input.1 input.2)

/-- Stable concrete representation available while combining one computation
node.

The active node remains in its packed ABI cell because decoded node fields
alias range-loop scratch.  `ControlDecode.decodeNode` can re-establish those
fields from `nodeCode` at any iteration.  The catalytic bank word is related
pointwise to the logical residue family read by the basis factor.
-/
structure ComputationContext
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store) : Prop where
  /-- Runtime sizes, radices, and the searched field are exact. -/
  parameters :
    Representation.Parameters regs instanceData store
  /-- The active ABI cell encodes this exact computation node. -/
  nodeCode_eq :
    store (Layout.nodeCode regs) =
      FrameCodec.encodeNode (Representation.digitBase instanceData)
        (show
          NeighborhoodEvaluator.QueryNode
            workTapeCount instanceData.horizon
          from .graph (.computation tape slot interval))
  /-- Packed bank word 33 has its exact row-major logical meaning. -/
  bank :
    NeighborhoodProgram.RepresentsResidueBank
      tm instanceData.blockLength
      (Representation.fieldBase instanceData)
      (store regs.layout.bank) logicalBank

/-- The stable computation representation together with the active frame
output coordinate.

The weaker `ComputationContext` is sufficient for decoding and direct packed
bank reads.  A basis-factor command additionally needs to derive each child
row from the runtime output cell, so its contextual contract uses this
frame-aware refinement.
-/
structure ComputationFrameContext
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store) : Prop where
  /-- Stable runtime parameters, node code, and catalytic-bank
  representation. -/
  computation :
    ComputationContext regs instanceData tape slot interval logicalBank store
  /-- The active output cell names the parent frame's output coordinate. -/
  out_eq : store (Layout.out regs) = frame.out.val

/-- Semantic computation-node fields recovered into decoder scratch while
the stable packed-node and bank representation remains valid. -/
structure DecodedComputationPost
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (final : Store) : Prop where
  /-- Stable encoded-node and packed-bank representation. -/
  context :
    ComputationContext regs instanceData tape slot interval
      logicalBank final
  /-- Exact decoded tag, tape, slot, and interval fields. -/
  decoded :
    ControlDecode.EncodedNodePost regs
      (show
        NeighborhoodEvaluator.QueryNode
          workTapeCount instanceData.horizon
        from .graph (.computation tape slot interval))
      final

/-- Logical children read from the catalytic rows owned by one active frame. -/
def computationArguments
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) →
      NeighborhoodExecutableEvaluation.ResidueValue
        tm instanceData.blockLength :=
  fun child => logicalBank (frame.childTarget child)

/-- Concrete packed-factor specification for the active computation node. -/
def ComputationPackedKernelSpecAt
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (kernel : Cmd) : Prop :=
  PackedKernelSpecAtContext regs kernel
    (NeighborhoodScheduler.fieldModulus instanceData)
    (packedAssignmentValue
      (NeighborhoodExecutableEvaluation.payloadWidth
        tm instanceData.blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
      (NeighborhoodExecutableEvaluation.booleanCombine
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        tape slot interval)
      outputChunk)
    (ComputationFrameContext regs instanceData frame tape slot interval
      logicalBank)

/-- Concrete tensor-basis specification for the catalytic child rows of the
active computation frame. -/
def ComputationBasisKernelSpecAt
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (kernel : Cmd) : Prop :=
  BasisKernelSpecAtContext regs kernel
    (NeighborhoodScheduler.fieldModulus instanceData)
    (basisAssignmentValue
      (NeighborhoodExecutableEvaluation.payloadWidth
        tm instanceData.blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
      (computationArguments frame logicalBank))
    (ComputationFrameContext regs instanceData frame tape slot interval
      logicalBank)

/-- Physical packed-bank reader view inherited from the shared
residue-scaling allocation. -/
def coordinateBankMap : Fin 12 → Fin 34 :=
  ![33, 0, 14, 1, 4, 5, 17, 9, 10, 11, 12, 18]

theorem coordinateBankMap_injective :
    Function.Injective coordinateBankMap := by
  decide

/-- Packed-bank reader registers inside combine scratch and the preserved
bank-radix parameter cell. -/
def coordinateBankRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    NeighborhoodProgram.BankRegisters where
  index := fun slot => regs.index (coordinateBankMap slot)
  injective := regs.injective.comp coordinateBankMap_injective

/-- Dynamic row-major coordinate supplied by a basis-factor loop. -/
abbrev coordinateIndex
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 30

/-- Scratch cell used to restore the immutable outer assignment count after
the packed-bank reader temporarily reuses its physical register. -/
abbrev savedRangeCount
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 31

/-- Save the outer count, stream one dynamic catalytic-bank coordinate, and
restore the count.  The selected residue is returned in `bank.result`. -/
def readResidueCoordinate
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let range := CombineValue.rangeRegisters regs
  let bank := coordinateBankRegisters regs
  Cmd.seqList
    [copy (savedRangeCount regs) range.count,
      copy bank.indexCount (coordinateIndex regs),
      .basic (.sub bank.basePred bank.base bank.one),
      NeighborhoodProgram.bankRead bank,
      copy range.count (savedRangeCount regs)]

/-- Fixed write overapproximation of one catalytic-coordinate read.  The
bank radix belongs to this inherited interface but is preserved exactly by
`bankRead`. -/
def coordinateReadFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  (coordinateBankRegisters regs).footprint ∪
    {savedRangeCount regs, (CombineValue.rangeRegisters regs).count}

/-- Exact observable result of one logical catalytic-bank coordinate read. -/
structure ResidueCoordinatePost
    (regs : NeighborhoodTrial.Registers controller)
    (value coordinate : ℕ) (initial final : Store) : Prop where
  /-- Selected logical residue in the packed reader's result cell. -/
  result_eq :
    final (coordinateBankRegisters regs).result = value
  /-- Packed bank word is restored exactly. -/
  bank_eq :
    final (coordinateBankRegisters regs).word =
      initial (coordinateBankRegisters regs).word
  /-- Fold accumulator is preserved. -/
  accumulator_eq :
    final (CombineValue.rangeRegisters regs).accumulator =
      initial (CombineValue.rangeRegisters regs).accumulator
  /-- Current assignment code is preserved. -/
  remaining_eq :
    final (CombineValue.rangeRegisters regs).remaining =
      initial (CombineValue.rangeRegisters regs).remaining
  /-- Field modulus is preserved. -/
  modulus_eq :
    final (CombineValue.rangeRegisters regs).modulus =
      initial (CombineValue.rangeRegisters regs).modulus
  /-- Field-modulus predecessor is preserved. -/
  modulusPred_eq :
    final (CombineValue.rangeRegisters regs).modulusPred =
      initial (CombineValue.rangeRegisters regs).modulusPred
  /-- Constant one is preserved. -/
  one_eq :
    final (CombineValue.rangeRegisters regs).one =
      initial (CombineValue.rangeRegisters regs).one
  /-- Immutable outer assignment count is restored. -/
  count_eq :
    final (CombineValue.rangeRegisters regs).count =
      initial (CombineValue.rangeRegisters regs).count
  /-- Dynamic coordinate source is preserved. -/
  coordinate_eq : final (coordinateIndex regs) = coordinate

/-- Inner product range used for one univariate Lagrange basis factor.

The enclosing assignment code, outer sum accumulator, packed-node value,
coordinate point, and final tensor accumulator remain in separate cells.
-/
def basisChunkRangeRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    CombineValue.RangeRegisters where
  index := fun slot =>
    regs.index (![31, 24, 16, 5, 0, 20, 17, 1] slot)
  injective := regs.injective.comp (by decide)

/-- Modular-reduction view for the selected-minus-other denominator. -/
def basisDenominatorRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    RuntimeArithmetic.ReduceRegisters where
  value := regs.index 9
  modulus := regs.index 24
  modulusPred := regs.index 16
  test := regs.index 4
  value_ne_modulus := regs.injective.ne (by decide)
  value_ne_modulusPred := regs.injective.ne (by decide)
  value_ne_test := regs.injective.ne (by decide)
  modulus_ne_modulusPred := regs.injective.ne (by decide)
  modulus_ne_test := regs.injective.ne (by decide)
  modulusPred_ne_test := regs.injective.ne (by decide)

/-- Modular-reduction view for the point-minus-other numerator. -/
def basisNumeratorRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    RuntimeArithmetic.ReduceRegisters where
  value := regs.index 11
  modulus := regs.index 24
  modulusPred := regs.index 16
  test := regs.index 4
  value_ne_modulus := regs.injective.ne (by decide)
  value_ne_modulusPred := regs.injective.ne (by decide)
  value_ne_test := regs.injective.ne (by decide)
  modulus_ne_modulusPred := regs.injective.ne (by decide)
  modulus_ne_test := regs.injective.ne (by decide)
  modulusPred_ne_test := regs.injective.ne (by decide)

/-- Fixed-register exponentiation view used for one Lagrange denominator
inverse.  Its accumulator is the inner range's term cell. -/
def basisInverseRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    RuntimeArithmetic.PowRegisters where
  index := fun slot =>
    regs.index (![20, 24, 16, 4, 9, 29, 17] slot)
  injective := regs.injective.comp (by decide)

/-- Modular-reduction view on the inner Lagrange-factor term. -/
def basisFactorRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    RuntimeArithmetic.ReduceRegisters where
  value := regs.index 20
  modulus := regs.index 24
  modulusPred := regs.index 16
  test := regs.index 4
  value_ne_modulus := regs.injective.ne (by decide)
  value_ne_modulusPred := regs.injective.ne (by decide)
  value_ne_test := regs.injective.ne (by decide)
  modulus_ne_modulusPred := regs.injective.ne (by decide)
  modulus_ne_test := regs.injective.ne (by decide)
  modulusPred_ne_test := regs.injective.ne (by decide)

/-- Modular-reduction view on the final tensor-product accumulator. -/
def basisAccumulatorRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    RuntimeArithmetic.ReduceRegisters where
  value := basisValue regs
  modulus := regs.index 24
  modulusPred := regs.index 16
  test := regs.index 4
  value_ne_modulus := regs.injective.ne (by decide)
  value_ne_modulusPred := regs.injective.ne (by decide)
  value_ne_test := regs.injective.ne (by decide)
  modulus_ne_modulusPred := regs.injective.ne (by decide)
  modulus_ne_test := regs.injective.ne (by decide)
  modulusPred_ne_test := regs.injective.ne (by decide)

/-- Runtime natural-residue Lagrange factor written only in terms of numeric
chunk codes. -/
def numericLagrangeFactor
    (modulus selected other point : ℕ) : ℕ :=
  if selected = other then
    PrimeField.Runtime.normalize modulus 1
  else
    PrimeField.Runtime.mul modulus
      (PrimeField.Runtime.inverse modulus
        (PrimeField.Runtime.sub modulus selected other))
      (PrimeField.Runtime.sub modulus point other)

/-- Nontrivial branch of one numeric Lagrange-factor computation. -/
def basisNontrivialFactor
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let inner := basisChunkRangeRegisters regs
  let inverse := basisInverseRegisters regs
  Cmd.seqList
    [RuntimeArithmetic.subMod (basisDenominatorRegisters regs)
        (CombineValue.rangeRegisters regs).term inner.remaining,
      Runtime.inverseMod inverse,
      copy (basisNumeratorRegisters regs).value
        (coordinateBankRegisters regs).result,
      RuntimeArithmetic.reduce (basisNumeratorRegisters regs),
      RuntimeArithmetic.subMod (basisNumeratorRegisters regs)
        (basisNumeratorRegisters regs).value inner.remaining,
      RuntimeArithmetic.mulMod (basisFactorRegisters regs)
        inverse.accumulator (basisNumeratorRegisters regs).value]

/-- Generate one numeric Lagrange factor for the inner chunk-code range.

The sum of the two one-sided natural differences is zero exactly when the
selected chunk code equals the current other code.
-/
def basisLagrangeTerm
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let inner := basisChunkRangeRegisters regs
  Cmd.seq
    (Cmd.seqList
      [copy (regs.index 4) (CombineValue.rangeRegisters regs).term,
      .basic (.sub (regs.index 4) (regs.index 4) inner.remaining),
      copy (regs.index 29) inner.remaining,
      .basic (.sub (regs.index 29) (regs.index 29)
        (CombineValue.rangeRegisters regs).term),
      .basic (.add (regs.index 4) (regs.index 4) (regs.index 29))])
    (.ifZero (regs.index 4)
      (.basic (.imm inner.term 1))
      (basisNontrivialFactor regs))

/-- Dynamic countdown for the chunks belonging to one fixed child slot.

This cell is reused as the inner Lagrange range's immutable count after the
current chunk cursor has been saved elsewhere.
-/
abbrev basisChunkCursor
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  (basisChunkRangeRegisters regs).count

/-- Reverse rank of a fixed child slot.  The runtime visits child slots from
high to low, so the largest slot has low-order assignment-digit rank zero. -/
def reverseChildRank (fanIn : ℕ) (child : Fin fanIn) : ℕ :=
  fanIn - 1 - child.val

/-- Low-order assignment-digit index corresponding to one semantic grouped
coordinate.

This is a pure specification function, not source-code specialization.  The
uniform command below computes the same value from a fixed child slot and a
runtime chunk cursor.
-/
def basisCoordinateDigitIndex
    (payloadWidth fanIn : ℕ)
    (coordinate :
      Fin fanIn ×
        Fin
          (PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn)) :
    ℕ :=
  fanIn * PrimeGrouped.Logarithmic.chunkCount payloadWidth fanIn -
    1 - (finProdFinEquiv coordinate).val

/-- Compute the low-order assignment digit for a runtime chunk cursor.

For reverse child rank `r`, runtime chunk count `k`, and current descending
chunk `c`, the low-order digit index is `r * k + (k - 1 - c)`.  All
instance-dependent quantities are read from runtime cells.
-/
def prepareAssignmentDigitIndex
    (regs : NeighborhoodTrial.Registers controller)
    (reverseRank : ℕ) : Cmd :=
  let range := CombineValue.rangeRegisters regs
  Cmd.seqList
    [.basic (.imm (coordinateIndex regs) reverseRank),
      .basic (.mul (coordinateIndex regs) (coordinateIndex regs)
        (Layout.chunkCount regs)),
      copy (regs.index 29) (Layout.chunkCount regs),
      .basic (.sub (regs.index 29) (regs.index 29) range.one),
      .basic (.sub (regs.index 29) (regs.index 29)
        (basisChunkCursor regs)),
      .basic (.add (coordinateIndex regs) (coordinateIndex regs)
        (regs.index 29))]

/-- Derive one child row and row-major chunk coordinate from runtime state.

The branch computes the natural representative of
`out.succAbove child`.  It then multiplies by the runtime chunk count and
adds the current runtime chunk cursor.
-/
def prepareBankCoordinate
    (regs : NeighborhoodTrial.Registers controller)
    {fanIn : ℕ} (child : Fin fanIn) : Cmd :=
  let range := CombineValue.rangeRegisters regs
  Cmd.seqList
    [.basic (.imm (regs.index 29) child.val),
      .basic (.sub range.test (Layout.out regs) (regs.index 29)),
      .ifZero range.test
        (.basic (.imm (coordinateIndex regs) (child.val + 1)))
        (.basic (.imm (coordinateIndex regs) child.val)),
      .basic (.mul (coordinateIndex regs) (coordinateIndex regs)
        (Layout.chunkCount regs)),
      .basic (.add (coordinateIndex regs) (coordinateIndex regs)
        (basisChunkCursor regs))]

/-- Prepare one dynamic chunk factor for a fixed child slot.

The driver first decrements `basisChunkCursor` to the current zero-based
chunk.  The command extracts the corresponding assignment digit, derives
and reads the matching child-bank coordinate, saves the chunk cursor in
`coordinateIndex`, and installs the runtime chunk radix as the inner
Lagrange range count.
-/
def basisChunkPrepare
    (regs : NeighborhoodTrial.Registers controller)
    {fanIn : ℕ} (child : Fin fanIn) : Cmd :=
  let inner := basisChunkRangeRegisters regs
  Cmd.seqList
    [.basic (.sub (basisChunkCursor regs) (basisChunkCursor regs)
      (CombineValue.rangeRegisters regs).one),
      prepareAssignmentDigitIndex regs (reverseChildRank fanIn child),
      assignmentDigit regs,
      prepareBankCoordinate regs child,
      copy (regs.index 29) (basisChunkCursor regs),
      readResidueCoordinate regs,
      copy (coordinateIndex regs) (regs.index 29),
      copy inner.count (Layout.chunkRadix regs)]

/-- Preparation followed by the inner Lagrange range for one dynamic
chunk. -/
def basisChunkRangeStage
    (regs : NeighborhoodTrial.Registers controller)
    {fanIn : ℕ} (child : Fin fanIn) : Cmd :=
  let inner := basisChunkRangeRegisters regs
  Cmd.seq
    (basisChunkPrepare regs child)
    (CombineValue.rangeFold .mul inner (basisLagrangeTerm regs))

/-- Dynamic chunk range followed by multiplication into the tensor
accumulator. -/
def basisChunkCore
    (regs : NeighborhoodTrial.Registers controller)
    {fanIn : ℕ} (child : Fin fanIn) : Cmd :=
  let inner := basisChunkRangeRegisters regs
  Cmd.seq
    (basisChunkRangeStage regs child)
    (RuntimeArithmetic.mulMod (basisAccumulatorRegisters regs)
      inner.accumulator (basisValue regs))

/-- One complete dynamic chunk iteration for a fixed child slot.

After preparation, the command computes the univariate Lagrange factor over
the runtime chunk radix, multiplies it into the tensor accumulator, and
restores the dynamic chunk cursor before returning to the loop driver.
-/
def basisChunkBody
    (regs : NeighborhoodTrial.Registers controller)
    {fanIn : ℕ} (child : Fin fanIn) : Cmd :=
  Cmd.seq
    (basisChunkCore regs child)
    (copy (basisChunkCursor regs) (coordinateIndex regs))

/-- Visit all runtime chunks of one fixed child slot in descending order. -/
def basisChildCommand
    (regs : NeighborhoodTrial.Registers controller)
    {fanIn : ℕ} (child : Fin fanIn) : Cmd :=
  Cmd.seq
    (copy (basisChunkCursor regs) (Layout.chunkCount regs))
    (.whileNonzero (basisChunkCursor regs) (basisChunkBody regs child))

/-- Fixed-fan-in reverse child schedule.

Only the simulator machine's fixed child slots are unrolled into the source
command.  The chunk count and every coordinate value remain runtime data.
-/
def basisChildFold
    (regs : NeighborhoodTrial.Registers controller)
    {fanIn : ℕ} : List (Fin fanIn) → Cmd
  | [] => .skip
  | child :: children =>
      .seq (basisChildFold regs children)
        (basisChildCommand regs child)

/-- Uniform tensor-basis command for a fixed fan-in.

The command source depends on `fanIn` and the shared register allocation
only.  Payload width, chunk count, chunk radix, active output, and catalytic
bank contents are all consumed from runtime cells.
-/
def basisKernel
    (regs : NeighborhoodTrial.Registers controller)
    (fanIn : ℕ) : Cmd :=
  Cmd.seq
    (Cmd.seq
      (.basic (.imm (basisValue regs) 1))
      (RuntimeArithmetic.reduce (basisAccumulatorRegisters regs)))
    (basisChildFold regs (List.finRange fanIn))

/-- Uniform tensor-basis kernel for the neighborhood machine's fixed
computation fan-in. -/
def computationBasisKernel
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  basisKernel regs
    (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)

end CombineTerm
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
