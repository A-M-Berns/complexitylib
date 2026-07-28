/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Structured.Footprint.Defs
import
  Complexitylib.Models.RandomAccessMachine.Structured.RuntimeArithmetic.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ControlDecode.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Layout.Defs

/-!
# Fixed-register range folds for local residue combination

The expensive arithmetic core of `combineResidues` is a nest of modular
range folds: products form Lagrange factors and the outer assignment-code
range is summed.  This module reifies the reusable loop driver as concrete
structured RAM commands.

A caller supplies a first-order term command satisfying `TermKernelSpec`.
The driver owns the countdown, accumulator, and modular reduction.  This
keeps the remaining lowering boundary precise: Boolean local-transition
packing and Lagrange-term generation must fill one fixed term register, but
the exponentially long sum/product traversal itself is already concrete.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CombineValue

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Modular operation performed by one range fold. -/
inductive FoldOp where
  /-- Modular sum. -/
  | add
  /-- Modular product. -/
  | mul
  deriving DecidableEq

namespace FoldOp

/-- Pure natural-residue update performed by one fold iteration. -/
def apply (op : FoldOp) (modulus term accumulator : ℕ) : ℕ :=
  match op with
  | .add =>
      TreeEval.CookMertz.PrimeField.Runtime.add
        modulus term accumulator
  | .mul =>
      TreeEval.CookMertz.PrimeField.Runtime.mul
        modulus term accumulator

/-- Canonical modular identity of one fold operation. -/
def identity (op : FoldOp) (modulus : ℕ) : ℕ :=
  match op with
  | .add =>
      TreeEval.CookMertz.PrimeField.Runtime.normalize modulus 0
  | .mul =>
      TreeEval.CookMertz.PrimeField.Runtime.normalize modulus 1

/-- Tail-recursive pure semantics shared with the residue evaluator. -/
def fold (op : FoldOp) (modulus : ℕ) (term : ℕ → ℕ) :
    ℕ → ℕ → ℕ
  | 0, accumulator =>
      accumulator
  | count + 1, accumulator =>
      fold op modulus term count
        (apply op modulus (term count) accumulator)

/-- Pure range semantics from the canonical operation identity. -/
def range (op : FoldOp) (modulus : ℕ)
    (term : ℕ → ℕ) (count : ℕ) : ℕ :=
  fold op modulus term count (identity op modulus)

end FoldOp

/-- Eight pairwise-distinct fixed registers for one modular range fold. -/
structure RangeRegisters where
  /-- Allocation order: accumulator, modulus, modulus predecessor,
  reduction test, remaining count, term, one, immutable initial count. -/
  index : Fin 8 → ℕ
  /-- Logical range registers are physically distinct. -/
  injective : Function.Injective index

namespace RangeRegisters

/-- Fold accumulator. -/
abbrev accumulator (regs : RangeRegisters) : ℕ := regs.index 0

/-- Positive runtime modulus. -/
abbrev modulus (regs : RangeRegisters) : ℕ := regs.index 1

/-- Preserved value `modulus - 1`. -/
abbrev modulusPred (regs : RangeRegisters) : ℕ := regs.index 2

/-- Modular-reduction loop test. -/
abbrev test (regs : RangeRegisters) : ℕ := regs.index 3

/-- Number of range elements not yet processed. -/
abbrev remaining (regs : RangeRegisters) : ℕ := regs.index 4

/-- Term generated for the current range index. -/
abbrev term (regs : RangeRegisters) : ℕ := regs.index 5

/-- Constant one used by the countdown. -/
abbrev one (regs : RangeRegisters) : ℕ := regs.index 6

/-- Immutable initial range cardinality. -/
abbrev count (regs : RangeRegisters) : ℕ := regs.index 7

/-- Modular-reduction view on the accumulator. -/
def reduceRegisters (regs : RangeRegisters) :
    RuntimeArithmetic.ReduceRegisters where
  value := regs.accumulator
  modulus := regs.modulus
  modulusPred := regs.modulusPred
  test := regs.test
  value_ne_modulus := regs.injective.ne (by decide)
  value_ne_modulusPred := regs.injective.ne (by decide)
  value_ne_test := regs.injective.ne (by decide)
  modulus_ne_modulusPred := regs.injective.ne (by decide)
  modulus_ne_test := regs.injective.ne (by decide)
  modulusPred_ne_test := regs.injective.ne (by decide)

/-- All logical registers read or written by the range interface. -/
def footprint (regs : RangeRegisters) : Finset ℕ :=
  Finset.univ.image regs.index

/-- Direct destinations owned by the range driver, excluding the
caller-supplied term command. -/
def driverWriteFootprint (regs : RangeRegisters) : Finset ℕ :=
  {regs.accumulator, regs.test, regs.remaining, regs.one}

end RangeRegisters

/-- Physical range-fold view inside the shared neighborhood workspace.

The modulus and its predecessor reuse preserved parameter cells 24 and 16.
The other six cells are setup/packed-bank scratch after parameter selection.
-/
def rangeRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    RangeRegisters where
  index := fun slot =>
    regs.index (![18, 24, 16, 5, 21, 19, 17, 10] slot)
  injective := regs.injective.comp (by decide)

/-- Mutable cells available to combine-term lowering while preserving the
active frame and the parameter ABI. -/
def combineScratchMap : Fin 19 → Fin 34 :=
  ![0, 1, 4, 5, 6, 9, 10, 11, 12, 17, 18, 19, 20, 21, 29, 30,
    31, 32, 33]

theorem combineScratchMap_injective :
    Function.Injective combineScratchMap := by
  decide

/-- Exact workspace allowed to the range driver and its term kernel. -/
def combineScratchFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  Finset.univ.image fun slot => regs.index (combineScratchMap slot)

/-- Direct-register copy used during fold initialization. -/
def copy (destination source : ℕ) : Cmd :=
  Cmd.seq
    (.basic (.imm destination 0))
    (.basic (.add destination source destination))

/-- Concrete modular update of the range accumulator. -/
def foldCommand (op : FoldOp) (regs : RangeRegisters) : Cmd :=
  match op with
  | .add =>
      RuntimeArithmetic.addMod regs.reduceRegisters
        regs.term regs.accumulator
  | .mul =>
      RuntimeArithmetic.mulMod regs.reduceRegisters
        regs.term regs.accumulator

/-- One range iteration: decrement to the current zero-based index, generate
its term, then update the modular accumulator. -/
def foldBody
    (op : FoldOp) (regs : RangeRegisters) (termKernel : Cmd) : Cmd :=
  Cmd.seq
    (.basic (.sub regs.remaining regs.remaining regs.one))
    (Cmd.seq termKernel (foldCommand op regs))

/-- Fold from a prepared accumulator and remaining-count register. -/
def rangeFoldFrom
    (op : FoldOp) (regs : RangeRegisters) (termKernel : Cmd) : Cmd :=
  .whileNonzero regs.remaining (foldBody op regs termKernel)

/-- Initialize one canonical range fold.

The immutable `count` register is copied into `remaining`; the accumulator
is reduced from raw zero or one to the canonical modular identity.
-/
def initializeFold (op : FoldOp) (regs : RangeRegisters) : Cmd :=
  let rawIdentity :=
    match op with
    | .add => 0
    | .mul => 1
  Cmd.seqList
    [.basic (.imm regs.one 1),
      copy regs.remaining regs.count,
      .basic (.imm regs.accumulator rawIdentity),
      RuntimeArithmetic.reduce regs.reduceRegisters]

/-- Complete concrete modular range fold. -/
def rangeFold
    (op : FoldOp) (regs : RangeRegisters) (termKernel : Cmd) : Cmd :=
  Cmd.seq (initializeFold op regs)
    (rangeFoldFrom op regs termKernel)

/-- Observable preservation and output of one term-kernel invocation. -/
structure TermPost
    (regs : RangeRegisters) (termValue index : ℕ)
    (initial final : Store) : Prop where
  /-- Exact generated term. -/
  term_eq : final regs.term = termValue
  /-- Accumulator is untouched by term generation. -/
  accumulator_eq :
    final regs.accumulator = initial regs.accumulator
  /-- Current range index is preserved. -/
  remaining_eq : final regs.remaining = index
  /-- Modulus is preserved. -/
  modulus_eq : final regs.modulus = initial regs.modulus
  /-- Modulus predecessor is preserved. -/
  modulusPred_eq :
    final regs.modulusPred = initial regs.modulusPred
  /-- Constant one is preserved. -/
  one_eq : final regs.one = initial regs.one
  /-- Immutable initial range count is preserved. -/
  count_eq : final regs.count = initial regs.count

/-- Correctness contract at the remaining combine-term lowering boundary. -/
def TermKernelSpec
    (regs : RangeRegisters) (termKernel : Cmd)
    (term : ℕ → ℕ) : Prop :=
  ∀ (store : Store) (index : ℕ),
    store regs.remaining = index →
    ∃ final,
      Runs termKernel store final ∧
      TermPost regs (term index) index store final

/-- Term-kernel correctness under the runtime field invariants established
by the enclosing range fold.

Unlike `TermKernelSpec`, this contextual contract does not require a kernel
to work for arbitrary garbage in the modulus interface.  It is therefore the
appropriate compositional boundary for concrete modular term generation.
-/
def TermKernelSpecAt
    (regs : RangeRegisters) (termKernel : Cmd)
    (modulus : ℕ) (term : ℕ → ℕ) : Prop :=
  ∀ (store : Store) (index : ℕ),
    store regs.remaining = index →
    store regs.modulus = modulus →
    store regs.modulusPred = modulus - 1 →
    store regs.one = 1 →
    ∃ final,
      Runs termKernel store final ∧
      TermPost regs (term index) index store final

/-- Context-preserving term-kernel correctness under the runtime field
invariants established by the enclosing range fold.

The additional predicate records semantic store representations, such as a
packed catalytic bank and active computation node, that a concrete term
kernel may read and must restore before returning.
-/
def TermKernelSpecAtContext
    (regs : RangeRegisters) (termKernel : Cmd)
    (modulus : ℕ) (term : ℕ → ℕ)
    (context : Store → Prop) : Prop :=
  ∀ (store : Store) (index : ℕ),
    context store →
    store regs.remaining = index →
    store regs.modulus = modulus →
    store regs.modulusPred = modulus - 1 →
    store regs.one = 1 →
    ∃ final,
      Runs termKernel store final ∧
      TermPost regs (term index) index store final ∧
      context final

/-- A semantic store representation is insensitive to the direct
destinations owned by the range driver.

Term kernels may temporarily use a larger workspace, but must preserve the
representation explicitly through `TermKernelSpecAtContext`.
-/
def StableUnderDriverWrites
    (regs : RangeRegisters) (context : Store → Prop) : Prop :=
  ∀ {initial final : Store},
    context initial →
    (∀ address, address ∉ regs.driverWriteFootprint →
      final address = initial address) →
    context final

/-- Exact observable result of a prepared range fold. -/
structure RangeFromPost
    (op : FoldOp) (regs : RangeRegisters)
    (modulus count initialAccumulator : ℕ)
    (term : ℕ → ℕ) (initial final : Store) : Prop where
  /-- Exact tail-recursive modular fold result. -/
  accumulator_eq :
    final regs.accumulator =
      op.fold modulus term count initialAccumulator
  /-- Countdown is exhausted. -/
  remaining_eq : final regs.remaining = 0
  /-- Runtime modulus is preserved. -/
  modulus_eq : final regs.modulus = modulus
  /-- Runtime modulus predecessor is preserved. -/
  modulusPred_eq : final regs.modulusPred = modulus - 1
  /-- Constant one is preserved. -/
  one_eq : final regs.one = 1
  /-- Initial range count is preserved. -/
  count_eq : final regs.count = initial regs.count

/-- Exact observable result of a fully initialized range fold. -/
structure RangePost
    (op : FoldOp) (regs : RangeRegisters)
    (modulus count : ℕ) (term : ℕ → ℕ)
    (initial final : Store) : Prop where
  /-- Exact modular range result. -/
  accumulator_eq :
    final regs.accumulator = op.range modulus term count
  /-- Countdown is exhausted. -/
  remaining_eq : final regs.remaining = 0
  /-- Runtime modulus is preserved. -/
  modulus_eq : final regs.modulus = modulus
  /-- Runtime modulus predecessor is preserved. -/
  modulusPred_eq : final regs.modulusPred = modulus - 1
  /-- Constant one is established. -/
  one_eq : final regs.one = 1
  /-- Immutable initial range count is preserved. -/
  count_eq : final regs.count = count

/-- Number of encoded Boolean-chunk assignments in one local combine. -/
def assignmentCount (payloadWidth fanIn : ℕ) : ℕ :=
  2 ^
    ((fanIn *
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          payloadWidth fanIn) *
      TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkBits
        payloadWidth fanIn)

/-- Exact outer-sum term of natural-residue grouped evaluation. -/
def assignmentTerm
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (args :
      Fin fanIn →
        Fin
          (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            payloadWidth fanIn) →
          ℕ)
    (outputChunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          payloadWidth fanIn))
    (code : ℕ) : ℕ :=
  let assignment :=
    TreeEval.CookMertz.GroupedExtension.Evaluation.chunkAssignmentOfCode
        finProdFinEquiv
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkBits
          payloadWidth fanIn)
        code
  TreeEval.CookMertz.PrimeField.Runtime.mul
    (NeighborhoodExecutableEvaluation.Residue.fieldModulus
      payloadWidth fanIn)
    (NeighborhoodExecutableEvaluation.Residue.packedNodeValue
      payloadWidth fanIn combine assignment outputChunk)
    (NeighborhoodExecutableEvaluation.Residue.basisValue
      payloadWidth fanIn assignment
      (fun input => args input.1 input.2))

/-- Precise missing first-order lowering boundary for full
`combineResidues`: generate one exact assignment summand at the current
countdown index. -/
def CombineTermKernelSpec
    (regs : RangeRegisters) (termKernel : Cmd)
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (args :
      Fin fanIn →
        Fin
          (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            payloadWidth fanIn) →
          ℕ)
    (outputChunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          payloadWidth fanIn)) : Prop :=
  TermKernelSpec regs termKernel
    (assignmentTerm payloadWidth fanIn combine args outputChunk)

/-- Contextual assignment-term contract under the searched field modulus.
This is the exact boundary consumed by concrete modular term generators. -/
def CombineTermKernelSpecAt
    (regs : RangeRegisters) (termKernel : Cmd)
    (payloadWidth fanIn : ℕ)
    (combine :
      (Fin fanIn → Fin payloadWidth → Bool) →
        Fin payloadWidth → Bool)
    (args :
      Fin fanIn →
        Fin
          (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            payloadWidth fanIn) →
          ℕ)
    (outputChunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          payloadWidth fanIn)) : Prop :=
  TermKernelSpecAt regs termKernel
    (NeighborhoodExecutableEvaluation.Residue.fieldModulus
      payloadWidth fanIn)
    (assignmentTerm payloadWidth fanIn combine args outputChunk)

end CombineValue
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
