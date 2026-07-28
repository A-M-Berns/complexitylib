/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Structured.RuntimeArithmetic.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.Invariant.Defs
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Footprint.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.Footprint.Defs
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.WorkspaceAccounting.Defs
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Search.Defs
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.PackedDigits

/-!
# Fixed-register packed runtime for neighborhood evaluation

This definitions layer begins the first-order RAM reification of the streamed
neighborhood evaluator. The routines here implement the packed-word
operations needed by an explicit DFS stack. They use only fixed register
destinations and contain no indirect store.

The stack radix is supplied at runtime. `peek` returns its least-significant
digit without changing the packed word, `pop` removes that digit, and `push`
installs a new least-significant digit. A twelve-register packed-bank
interface then composes those primitives into dynamic digit reads and
replacements without dynamic register addressing.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace NeighborhoodProgram

open RAM Structured
open NeighborhoodGraph

/-- A pointwise numeric bound on the mutable registers advertised by a
runtime routine. Unlike the sparse-store resource counter, this predicate
can be required at every source and compiled program point. -/
def ValuesWithin
    (allowed : Finset ℕ) (bound : ℕ) (store : Store) : Prop :=
  ∀ address, address ∈ allowed → store address ≤ bound

/-- One reusable numeric envelope for packed-word and modular-arithmetic
transients. `packedCapacity` bounds each packed word and reversal buffer.
The two products cover packed pushes and modular multiplication; the sums
cover the corresponding additions. -/
def transientValueBound
    (packedCapacity base modulus operand counter : ℕ) : ℕ :=
  max counter
    (max base
      (max modulus
        (max operand
          (max packedCapacity
            (max (base * packedCapacity)
              (max (operand + base * packedCapacity)
                (max (packedCapacity + operand)
                  (packedCapacity * operand))))))))

/-- Seven pairwise-distinct fixed registers used by packed stack routines. -/
structure StackRegisters where
  /-- Register allocation in the order word, base, base predecessor,
  quotient, loop test, one, and value. -/
  index : Fin 7 → ℕ
  /-- Distinct logical fields occupy distinct physical registers. -/
  injective : Function.Injective index

namespace StackRegisters

/-- The finite mutable-address footprint of the seven-register stack
interface. -/
def footprint (regs : StackRegisters) : Finset ℕ :=
  Finset.univ.image regs.index

/-- Every logical stack register belongs to its advertised footprint. -/
@[simp]
theorem index_mem_footprint (regs : StackRegisters) (index : Fin 7) :
    regs.index index ∈ regs.footprint := by
  exact Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩

/-- Distinct logical fields occupy distinct concrete registers. -/
theorem index_ne (regs : StackRegisters) {first second : Fin 7}
    (hne : first ≠ second) :
    regs.index first ≠ regs.index second :=
  fun heq => hne (regs.injective heq)

/-- Packed stack word. -/
abbrev word (regs : StackRegisters) : ℕ := regs.index 0

/-- Runtime stack radix. -/
abbrev base (regs : StackRegisters) : ℕ := regs.index 1

/-- Preserved value `base - 1`. -/
abbrev basePred (regs : StackRegisters) : ℕ := regs.index 2

/-- Quotient accumulator and push scratch. -/
abbrev quotient (regs : StackRegisters) : ℕ := regs.index 3

/-- Division-loop test and modular-reduction scratch. -/
abbrev test (regs : StackRegisters) : ℕ := regs.index 4

/-- Preserved constant one. -/
abbrev one (regs : StackRegisters) : ℕ := regs.index 5

/-- Pushed value on entry and peeked value on exit. -/
abbrev value (regs : StackRegisters) : ℕ := regs.index 6

/-- Modular-reduction view used to compute digit zero. -/
def reduceRegisters (regs : StackRegisters) :
    RuntimeArithmetic.ReduceRegisters where
  value := regs.value
  modulus := regs.base
  modulusPred := regs.basePred
  test := regs.test
  value_ne_modulus := regs.index_ne (by decide)
  value_ne_modulusPred := regs.index_ne (by decide)
  value_ne_test := regs.index_ne (by decide)
  modulus_ne_modulusPred := regs.index_ne (by decide)
  modulus_ne_test := regs.index_ne (by decide)
  modulusPred_ne_test := regs.index_ne (by decide)

end StackRegisters

/-- Recompute whether the current word is at least the radix. -/
def popTestOp (regs : StackRegisters) : Basic :=
  .sub regs.test regs.word regs.basePred

/-- Subtract one radix unit and increment the quotient. -/
def popBody (regs : StackRegisters) : Cmd :=
  Cmd.seqList
    [.basic (.sub regs.word regs.word regs.base),
      .basic (.add regs.quotient regs.quotient regs.one),
      .basic (popTestOp regs)]

/-- Divide the packed word by the runtime radix.

The quotient replaces `word`; the temporary quotient and loop test are
cleared. The caller supplies `basePred = base - 1` and `one = 1`. -/
def pop (regs : StackRegisters) : Cmd :=
  Cmd.seqList
    [.basic (.imm regs.quotient 0),
      .basic (popTestOp regs),
      .whileNonzero regs.test (popBody regs),
      .basic (.imm regs.word 0),
      .basic (.add regs.word regs.word regs.quotient),
      .basic (.imm regs.quotient 0)]

/-- Final store advertised by `pop`. -/
def popResultStore (regs : StackRegisters)
    (quotient : ℕ) (store : Store) : Store :=
  Function.update
    (Function.update
      (Function.update store regs.word quotient)
      regs.quotient 0)
    regs.test 0

/-- Read digit zero without changing the packed stack word. -/
def peek (regs : StackRegisters) : Cmd :=
  Cmd.seqList
    [.basic (.imm regs.value 0),
      .basic (.add regs.value regs.word regs.value),
      RuntimeArithmetic.reduce regs.reduceRegisters]

/-- Final store advertised by `peek`. -/
def peekResultStore (regs : StackRegisters)
    (digit : ℕ) (store : Store) : Store :=
  Function.update
    (Function.update store regs.value digit)
    regs.test 0

/-- Push `value` as a new least-significant radix digit. -/
def push (regs : StackRegisters) : Cmd :=
  Cmd.seqList
    [.basic (.mul regs.quotient regs.base regs.word),
      .basic (.add regs.word regs.value regs.quotient),
      .basic (.imm regs.quotient 0)]

/-- Final store advertised by `push`. -/
def pushResultStore (regs : StackRegisters)
    (word : ℕ) (store : Store) : Store :=
  Function.update
    (Function.update store regs.word word)
    regs.quotient 0

/-- Twelve pairwise-distinct fixed registers used to stream one coordinate
of a packed catalytic bank. -/
structure BankRegisters where
  /-- Register allocation in the order bank word, reversal buffer, radix,
  radix predecessor, quotient, loop test, one, digit scratch, index
  countdown, completed count, result, and replacement value. -/
  index : Fin 12 → ℕ
  /-- Distinct logical fields occupy distinct physical registers. -/
  injective : Function.Injective index

namespace BankRegisters

/-- Finite mutable-address footprint of the packed-bank interface. -/
def footprint (regs : BankRegisters) : Finset ℕ :=
  Finset.univ.image regs.index

@[simp]
theorem index_mem_footprint (regs : BankRegisters) (index : Fin 12) :
    regs.index index ∈ regs.footprint := by
  exact Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩

/-- Distinct logical bank fields occupy distinct concrete registers. -/
theorem index_ne (regs : BankRegisters) {first second : Fin 12}
    (hne : first ≠ second) :
    regs.index first ≠ regs.index second :=
  fun heq => hne (regs.injective heq)

/-- Packed catalytic-bank word. -/
abbrev word (regs : BankRegisters) : ℕ := regs.index 0

/-- Reversal buffer used while streaming to a dynamic digit. -/
abbrev buffer (regs : BankRegisters) : ℕ := regs.index 1

/-- Runtime bank radix. -/
abbrev base (regs : BankRegisters) : ℕ := regs.index 2

/-- Preserved value `base - 1`. -/
abbrev basePred (regs : BankRegisters) : ℕ := regs.index 3

/-- Quotient scratch shared by the two stack views. -/
abbrev quotient (regs : BankRegisters) : ℕ := regs.index 4

/-- Loop-test scratch shared by the two stack views. -/
abbrev test (regs : BankRegisters) : ℕ := regs.index 5

/-- Preserved constant one. -/
abbrev one (regs : BankRegisters) : ℕ := regs.index 6

/-- Current streamed digit. -/
abbrev value (regs : BankRegisters) : ℕ := regs.index 7

/-- Number of low-order digits still to stream. -/
abbrev indexCount (regs : BankRegisters) : ℕ := regs.index 8

/-- Number of buffered digits still to restore. -/
abbrev completed (regs : BankRegisters) : ℕ := regs.index 9

/-- Result register containing the old selected digit. -/
abbrev result (regs : BankRegisters) : ℕ := regs.index 10

/-- Preserved replacement digit for `bankReplace`. -/
abbrev replacement (regs : BankRegisters) : ℕ := regs.index 11

/-- Logical-to-physical map for the main packed word stack view. -/
def mainMap (index : Fin 7) : Fin 12 :=
  if index.val = 0 then ⟨0, by omega⟩
  else ⟨index.val + 1, by omega⟩

/-- Logical-to-physical map for the reversal-buffer stack view. -/
def bufferMap (index : Fin 7) : Fin 12 :=
  ⟨index.val + 1, by omega⟩

theorem mainMap_injective : Function.Injective mainMap := by
  intro first second heq
  have hval := congrArg Fin.val heq
  simp only [mainMap] at hval
  split_ifs at hval <;>
    apply Fin.ext <;>
    simp_all

theorem bufferMap_injective : Function.Injective bufferMap := by
  intro first second heq
  apply Fin.ext
  have hval := congrArg Fin.val heq
  simpa [bufferMap] using hval

/-- Stack-register view whose packed word is the catalytic bank. -/
def mainStack (regs : BankRegisters) : StackRegisters where
  index := fun index => regs.index (mainMap index)
  injective := regs.injective.comp mainMap_injective

/-- Stack-register view whose packed word is the reversal buffer. -/
def bufferStack (regs : BankRegisters) : StackRegisters where
  index := fun index => regs.index (bufferMap index)
  injective := regs.injective.comp bufferMap_injective

@[simp] theorem mainStack_word (regs : BankRegisters) :
    regs.mainStack.word = regs.word := rfl

@[simp] theorem bufferStack_word (regs : BankRegisters) :
    regs.bufferStack.word = regs.buffer := rfl

@[simp] theorem mainStack_base (regs : BankRegisters) :
    regs.mainStack.base = regs.base := rfl

@[simp] theorem bufferStack_base (regs : BankRegisters) :
    regs.bufferStack.base = regs.base := rfl

@[simp] theorem mainStack_basePred (regs : BankRegisters) :
    regs.mainStack.basePred = regs.basePred := rfl

@[simp] theorem bufferStack_basePred (regs : BankRegisters) :
    regs.bufferStack.basePred = regs.basePred := rfl

@[simp] theorem mainStack_quotient (regs : BankRegisters) :
    regs.mainStack.quotient = regs.quotient := rfl

@[simp] theorem bufferStack_quotient (regs : BankRegisters) :
    regs.bufferStack.quotient = regs.quotient := rfl

@[simp] theorem mainStack_test (regs : BankRegisters) :
    regs.mainStack.test = regs.test := rfl

@[simp] theorem bufferStack_test (regs : BankRegisters) :
    regs.bufferStack.test = regs.test := rfl

@[simp] theorem mainStack_one (regs : BankRegisters) :
    regs.mainStack.one = regs.one := rfl

@[simp] theorem bufferStack_one (regs : BankRegisters) :
    regs.bufferStack.one = regs.one := rfl

@[simp] theorem mainStack_value (regs : BankRegisters) :
    regs.mainStack.value = regs.value := rfl

@[simp] theorem bufferStack_value (regs : BankRegisters) :
    regs.bufferStack.value = regs.value := rfl

end BankRegisters

/-- Move one least-significant bank digit into the reversal buffer. -/
def bankForwardBody (regs : BankRegisters) : Cmd :=
  Cmd.seqList
    [peek regs.mainStack,
      pop regs.mainStack,
      push regs.bufferStack,
      .basic (.sub regs.indexCount regs.indexCount regs.one),
      .basic (.add regs.completed regs.completed regs.one)]

/-- Stream the requested low-order prefix into a packed reversal buffer. -/
def bankForward (regs : BankRegisters) : Cmd :=
  .whileNonzero regs.indexCount (bankForwardBody regs)

/-- Restore one buffered digit to the main packed bank. -/
def bankRestoreBody (regs : BankRegisters) : Cmd :=
  Cmd.seqList
    [peek regs.bufferStack,
      pop regs.bufferStack,
      push regs.mainStack,
      .basic (.sub regs.completed regs.completed regs.one)]

/-- Restore every digit moved into the packed reversal buffer. -/
def bankRestore (regs : BankRegisters) : Cmd :=
  .whileNonzero regs.completed (bankRestoreBody regs)

/-- Seek one dynamically indexed packed-bank digit.

The low-order prefix remains in `buffer`, the selected suffix remains in
`word`, the old digit is copied to `result`, and `completed` records how many
digits must subsequently be restored. -/
def bankSeek (regs : BankRegisters) : Cmd :=
  Cmd.seqList
    [.basic (.imm regs.buffer 0),
      .basic (.imm regs.completed 0),
      bankForward regs,
      peek regs.mainStack,
      .basic (.imm regs.result 0),
      .basic (.add regs.result regs.value regs.result)]

/-- Read one dynamically indexed packed-bank digit, preserving the bank.

The dynamic index is a value in the fixed `indexCount` register. Both packed
words remain direct-register values; the command performs no indirect store. -/
def bankRead (regs : BankRegisters) : Cmd :=
  Cmd.seq (bankSeek regs) (bankRestore regs)

/-- Replace one dynamically indexed packed-bank digit.

The old digit is returned in `result`; the new digit is supplied in the
preserved `replacement` register. -/
def bankReplace (regs : BankRegisters) : Cmd :=
  Cmd.seqList
    [bankSeek regs,
      pop regs.mainStack,
      .basic (.imm regs.value 0),
      .basic (.add regs.value regs.replacement regs.value),
      push regs.mainStack,
      bankRestore regs]

/-- Repeatedly remove `count` least-significant digits. -/
def popN (base : ℕ) : ℕ → ℕ → ℕ
  | 0, word => word
  | count + 1, word => PackedDigits.pop base (popN base count word)

/-- Packed reverse of the first `count` digits of `word`. -/
def reversedPrefix (base word : ℕ) : ℕ → ℕ
  | 0 => 0
  | count + 1 =>
      PackedDigits.push base (PackedDigits.digit base word count)
        (reversedPrefix base word count)

/-- Restore `count` buffered digits to a main word. -/
def restoreN (base : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, word, _ => word
  | count + 1, word, buffer =>
      restoreN base count
        (PackedDigits.push base
          (PackedDigits.digit base buffer 0) word)
        (PackedDigits.pop base buffer)

/-- Pure packed-word effect of `bankReplace`. -/
def replaceAt (base word index value : ℕ) : ℕ :=
  restoreN base index
    (PackedDigits.push base value (popN base (index + 1) word))
    (reversedPrefix base word index)

/-- Sixteen pairwise-distinct fixed registers used for one modular
coordinate update of the packed catalytic bank. -/
structure ResidueBankRegisters where
  /-- Register allocation. The first twelve slots are the packed-bank
  interface; the last four hold the field modulus, its predecessor, the
  update operand, and a saved dynamic coordinate. -/
  index : Fin 16 → ℕ
  /-- Distinct logical fields occupy distinct physical registers. -/
  injective : Function.Injective index

namespace ResidueBankRegisters

/-- Distinct logical residue-bank fields occupy distinct registers. -/
theorem index_ne (regs : ResidueBankRegisters) {first second : Fin 16}
    (hne : first ≠ second) :
    regs.index first ≠ regs.index second :=
  fun heq => hne (regs.injective heq)

/-- Embed one packed-bank slot into the residue-bank allocation. -/
def bankSlot (slot : Fin 12) : Fin 16 :=
  ⟨slot.val, by omega⟩

/-- The first twelve registers, viewed as a packed-bank interface. -/
def bank (regs : ResidueBankRegisters) : BankRegisters where
  index := fun slot => regs.index (bankSlot slot)
  injective := by
    intro first second heq
    apply Fin.ext
    have hslot := regs.injective heq
    simpa [bankSlot] using congrArg Fin.val hslot

@[simp] theorem bank_word (regs : ResidueBankRegisters) :
    regs.bank.word = regs.index 0 := rfl

@[simp] theorem bank_buffer (regs : ResidueBankRegisters) :
    regs.bank.buffer = regs.index 1 := rfl

@[simp] theorem bank_base (regs : ResidueBankRegisters) :
    regs.bank.base = regs.index 2 := rfl

@[simp] theorem bank_basePred (regs : ResidueBankRegisters) :
    regs.bank.basePred = regs.index 3 := rfl

@[simp] theorem bank_quotient (regs : ResidueBankRegisters) :
    regs.bank.quotient = regs.index 4 := rfl

@[simp] theorem bank_test (regs : ResidueBankRegisters) :
    regs.bank.test = regs.index 5 := rfl

@[simp] theorem bank_one (regs : ResidueBankRegisters) :
    regs.bank.one = regs.index 6 := rfl

@[simp] theorem bank_value (regs : ResidueBankRegisters) :
    regs.bank.value = regs.index 7 := rfl

@[simp] theorem bank_indexCount (regs : ResidueBankRegisters) :
    regs.bank.indexCount = regs.index 8 := rfl

@[simp] theorem bank_completed (regs : ResidueBankRegisters) :
    regs.bank.completed = regs.index 9 := rfl

@[simp] theorem bank_result (regs : ResidueBankRegisters) :
    regs.bank.result = regs.index 10 := rfl

@[simp] theorem bank_replacement (regs : ResidueBankRegisters) :
    regs.bank.replacement = regs.index 11 := rfl

/-- Runtime field modulus. -/
abbrev modulus (regs : ResidueBankRegisters) : ℕ := regs.index 12

/-- Preserved value `modulus - 1`. -/
abbrev modulusPred (regs : ResidueBankRegisters) : ℕ := regs.index 13

/-- Preserved scalar or vector coordinate used by the update. -/
abbrev operand (regs : ResidueBankRegisters) : ℕ := regs.index 14

/-- Saved dynamic bank coordinate. -/
abbrev savedIndex (regs : ResidueBankRegisters) : ℕ := regs.index 15

/-- Modular-arithmetic view whose result is the bank replacement register. -/
def reduceRegisters (regs : ResidueBankRegisters) :
    RuntimeArithmetic.ReduceRegisters where
  value := regs.bank.replacement
  modulus := regs.modulus
  modulusPred := regs.modulusPred
  test := regs.bank.test
  value_ne_modulus := by
    exact regs.injective.ne
      (by decide :
        (ResidueBankRegisters.bankSlot 11 : Fin 16) ≠ 12)
  value_ne_modulusPred := by
    exact regs.injective.ne
      (by decide :
        (ResidueBankRegisters.bankSlot 11 : Fin 16) ≠ 13)
  value_ne_test := by
    exact regs.injective.ne
      (by decide :
        (ResidueBankRegisters.bankSlot 11 : Fin 16) ≠
          ResidueBankRegisters.bankSlot 5)
  modulus_ne_modulusPred := by
    exact regs.injective.ne (by decide : (12 : Fin 16) ≠ 13)
  modulus_ne_test := by
    exact regs.injective.ne
      (by decide :
        (12 : Fin 16) ≠ ResidueBankRegisters.bankSlot 5)
  modulusPred_ne_test := by
    exact regs.injective.ne
      (by decide :
        (13 : Fin 16) ≠ ResidueBankRegisters.bankSlot 5)

/-- Finite mutable-address footprint of the residue-bank interface. -/
def footprint (regs : ResidueBankRegisters) : Finset ℕ :=
  Finset.univ.image regs.index

/-- Every residue-bank register belongs to its advertised footprint. -/
@[simp]
theorem index_mem_footprint (regs : ResidueBankRegisters)
    (slot : Fin 16) :
    regs.index slot ∈ regs.footprint :=
  Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

end ResidueBankRegisters

/-- The two modular packed-bank updates needed by the Cook--Mertz register
machine. -/
inductive ResidueBankOp where
  /-- Add one residue into the selected bank coordinate. -/
  | add
  /-- Multiply the selected bank coordinate by one residue. -/
  | mul
  deriving DecidableEq

namespace ResidueBankOp

/-- Unreduced arithmetic transient produced before modular reduction. -/
def rawApply : ResidueBankOp → ℕ → ℕ → ℕ
  | .add, current, operand => current + operand
  | .mul, current, operand => current * operand

/-- Pure natural-residue semantics of a bank update. -/
def apply : ResidueBankOp → ℕ → ℕ → ℕ → ℕ
  | .add, modulus, current, operand => (current + operand) % modulus
  | .mul, modulus, current, operand => (current * operand) % modulus

/-- Fixed-register runtime arithmetic implementing one update operation. -/
def command (op : ResidueBankOp)
    (regs : ResidueBankRegisters) : Cmd :=
  match op with
  | .add =>
      RuntimeArithmetic.addMod regs.reduceRegisters
        regs.bank.result regs.operand
  | .mul =>
      RuntimeArithmetic.mulMod regs.reduceRegisters
        regs.bank.result regs.operand

end ResidueBankOp

/-- Copy the dynamic coordinate into its fixed save register. -/
def saveBankIndex (regs : ResidueBankRegisters) : Cmd :=
  Cmd.seq
    (.basic (.imm regs.savedIndex 0))
    (.basic
      (.add regs.savedIndex regs.bank.indexCount regs.savedIndex))

/-- Restore the saved coordinate into the packed-bank countdown register. -/
def restoreBankIndex (regs : ResidueBankRegisters) : Cmd :=
  Cmd.seq
    (.basic (.imm regs.bank.indexCount 0))
    (.basic
      (.add regs.bank.indexCount regs.savedIndex
        regs.bank.indexCount))

/-- Read, modularly update, and replace one dynamically selected catalytic
bank coordinate using only sixteen fixed destinations. -/
def bankUpdateAt
    (regs : ResidueBankRegisters) (op : ResidueBankOp) : Cmd :=
  Cmd.seqList
    [saveBankIndex regs,
      bankRead regs.bank,
      op.command regs,
      restoreBankIndex regs,
      bankReplace regs.bank]

/-- Add `operand` modulo `modulus` into one dynamic bank coordinate. -/
def bankAddAt (regs : ResidueBankRegisters) : Cmd :=
  bankUpdateAt regs .add

/-- Multiply one dynamic bank coordinate by `operand` modulo `modulus`. -/
def bankScaleAt (regs : ResidueBankRegisters) : Cmd :=
  bankUpdateAt regs .mul

/-- Seventeen pairwise-distinct fixed registers used to scale every chunk
of one logical catalytic register. The first sixteen implement one modular
coordinate update; the final register counts unprocessed chunks. -/
structure ResidueScaleRegisters where
  /-- Fixed physical allocation. -/
  index : Fin 17 → ℕ
  /-- Distinct logical fields occupy distinct physical registers. -/
  injective : Function.Injective index

namespace ResidueScaleRegisters

/-- Embed one modular-bank slot into the register-scaling allocation. -/
def bankSlot (slot : Fin 16) : Fin 17 :=
  ⟨slot.val, by omega⟩

/-- The first sixteen registers, viewed as one modular-bank update
interface. -/
def bank (regs : ResidueScaleRegisters) : ResidueBankRegisters where
  index := fun slot => regs.index (bankSlot slot)
  injective := by
    intro first second heq
    apply Fin.ext
    have hslot := regs.injective heq
    simpa [bankSlot] using congrArg Fin.val hslot

/-- Number of logical chunks not yet scaled. -/
abbrev remaining (regs : ResidueScaleRegisters) : ℕ :=
  regs.index 16

/-- Finite footprint of the whole-register scaling interface. -/
def footprint (regs : ResidueScaleRegisters) : Finset ℕ :=
  Finset.univ.image regs.index

/-- Every scaling register belongs to its advertised footprint. -/
@[simp]
theorem index_mem_footprint
    (regs : ResidueScaleRegisters) (slot : Fin 17) :
    regs.index slot ∈ regs.footprint :=
  Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

end ResidueScaleRegisters

/-- After one modular scaling update, decrement the remaining chunk count
and advance the packed-bank coordinate saved by `bankUpdateAt`. -/
def advanceScaleChunk (regs : ResidueScaleRegisters) : Cmd :=
  Cmd.seq
    (.basic
      (.sub regs.remaining regs.remaining regs.bank.bank.one))
    (.basic
      (.add regs.bank.bank.indexCount regs.bank.savedIndex
        regs.bank.bank.one))

/-- Scale one selected chunk and advance to the next row-major coordinate. -/
def bankScaleRegisterBody (regs : ResidueScaleRegisters) : Cmd :=
  Cmd.seq (bankScaleAt regs.bank) (advanceScaleChunk regs)

/-- Stream modular scaling across every remaining chunk of one logical
catalytic register. -/
def bankScaleRegister (regs : ResidueScaleRegisters) : Cmd :=
  .whileNonzero regs.remaining (bankScaleRegisterBody regs)

/-- Syntactic guarantee that a basic operation never performs an indirect
write. -/
def basicNoStore : Basic → Prop
  | .store _ _ => False
  | _ => True

/-- Syntactic guarantee that a structured command never performs an
indirect write. Immutable indirect reads remain permitted. -/
def cmdNoStore : Cmd → Prop
  | .skip => True
  | .basic op => basicNoStore op
  | .seq first second => cmdNoStore first ∧ cmdNoStore second
  | .ifZero _ onZero onNonzero =>
      cmdNoStore onZero ∧ cmdNoStore onNonzero
  | .whileNonzero _ body => cmdNoStore body

/-- Runtime radix for one packed continuation frame. The active frame lives
in fixed registers; only suspended continuations occupy this word. -/
def frameRadix (Q : Type*) [Fintype Q]
    (workTapeCount candidate : ℕ) : ℕ :=
  2 ^ WorkspaceAccounting.frameBits Q workTapeCount candidate

/-- Runtime radix for one canonical field residue in the catalytic bank. -/
def bankRadix (Q : Type*) [Fintype Q]
    (workTapeCount candidate : ℕ) : ℕ :=
  2 ^ WorkspaceAccounting.fieldBits Q workTapeCount candidate

/-- Number of field-residue digits in the complete catalytic bank. -/
def bankDigitCount (Q : Type*) [Fintype Q]
    (workTapeCount candidate : ℕ) : ℕ :=
  (WorkspaceAccounting.fanIn workTapeCount + 1) *
    WorkspaceAccounting.chunkCount Q workTapeCount candidate

/-- Row-major packed-bank coordinate of one Cook--Mertz catalytic register
and grouped residue chunk. -/
def residueBankIndex
    (tm : TM workTapeCount) (blockLength : ℕ)
    (register :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1))
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))) :
    ℕ :=
  register.val *
      TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
        (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) +
    chunk.val

/-- Exact logical interpretation of a packed catalytic-bank word. -/
def RepresentsResidueBank
    (tm : TM workTapeCount) (blockLength base word : ℕ)
    (regs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength) : Prop :=
  ∀ register chunk,
    PackedDigits.digit base word
        (residueBankIndex tm blockLength register chunk) =
      regs register chunk

/-- Replace one logical register/chunk coordinate while preserving every
other natural-residue coordinate. -/
def updateResidueCoordinate
    (tm : TM workTapeCount) (blockLength : ℕ)
    (regs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1))
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (value : ℕ) :
    NeighborhoodExecutableEvaluation.Residue.Registers
      tm blockLength :=
  Function.update regs register
    (Function.update (regs register) chunk value)

/-- Logical state after scaling the first `processed` chunks of one
catalytic register. The definition is total; values of `processed` above
the chunk count simply scale every available chunk. -/
def scaleResiduePrefix
    (tm : TM workTapeCount) (blockLength scalar : ℕ)
    (regs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1))
    (processed : ℕ) :
    NeighborhoodExecutableEvaluation.Residue.Registers
      tm blockLength :=
  fun currentRegister chunk =>
    if currentRegister = register ∧ chunk.val < processed then
      ResidueBankOp.mul.apply
        (NeighborhoodExecutableEvaluation.modulus tm blockLength)
        (regs currentRegister chunk) scalar
    else
      regs currentRegister chunk

/-- Number of fixed scalar/control registers charged by this interface. -/
def fixedRegisterCount : ℕ := 32

/-- Concrete bit width of the two packed words and all fixed register
contents. Input cells are immutable and deliberately excluded. -/
def packedWorkspaceBits
    (stackWord bankWord : ℕ)
    (fixedValues : Fin fixedRegisterCount → ℕ) : ℕ :=
  stackWord.size + bankWord.size +
    ∑ index, (fixedValues index).size

/-- Exact numerical invariant expected of a concrete DFS microstep.

The packed continuation stack has at most `horizon` digits because the active
frame occupies fixed registers. The bank has exactly the persistent
Cook--Mertz field-cell count. Every remaining scalar is charged against the
aggregate scratch-width contract. -/
structure BoundedWorkspace
    (Q : Type*) [Fintype Q] (workTapeCount candidate : ℕ)
    (stackWord bankWord : ℕ)
    (fixedValues : Fin fixedRegisterCount → ℕ) : Prop where
  /-- Packed suspended continuations fit the interval horizon. -/
  stack_lt :
    stackWord <
      frameRadix Q workTapeCount candidate ^
        WorkspaceAccounting.horizon candidate
  /-- Packed catalytic residues fit the persistent bank. -/
  bank_lt :
    bankWord <
      bankRadix Q workTapeCount candidate ^
        bankDigitCount Q workTapeCount candidate
  /-- Every fixed scalar/control value fits the assigned scratch width. -/
  fixed_lt : ∀ index,
    fixedValues index <
      2 ^ WorkspaceAccounting.scratchBits
        Q workTapeCount candidate

/-- Concrete locations of the two packed words and the fixed scalar/control
registers used by one evaluator microstep. Aliasing is permitted in the
interface because it can only shrink the mutable footprint; an actual
microcode implementation will normally choose an injective allocation. -/
structure Layout where
  /-- Packed continuation stack. -/
  stack : ℕ
  /-- Packed catalytic residue bank. -/
  bank : ℕ
  /-- Fixed scalar and control registers. -/
  fixed : Fin fixedRegisterCount → ℕ

namespace Layout

/-- Exact finite set of mutable register addresses advertised by a layout. -/
def footprint (layout : Layout) : Finset ℕ :=
  {layout.stack, layout.bank} ∪
    Finset.univ.image layout.fixed

/-- The packed stack address belongs to the mutable footprint. -/
@[simp]
theorem stack_mem_footprint (layout : Layout) :
    layout.stack ∈ layout.footprint := by
  simp [footprint]

/-- The packed bank address belongs to the mutable footprint. -/
@[simp]
theorem bank_mem_footprint (layout : Layout) :
    layout.bank ∈ layout.footprint := by
  simp [footprint]

/-- Every fixed scalar address belongs to the mutable footprint. -/
@[simp]
theorem fixed_mem_footprint (layout : Layout)
    (index : Fin fixedRegisterCount) :
    layout.fixed index ∈ layout.footprint := by
  simp [footprint]

end Layout

/-- Runtime data for one candidate/guess evaluation. This record is data, not
program syntax: one uniform `ResidueMicrocode` must handle every inhabitant. -/
structure ResidueInstance
    {workTapeCount : ℕ} (tm : TM workTapeCount) where
  /-- Public Boolean input to the simulated Turing machine. -/
  x : List Bool
  /-- Candidate running time whose envelope pays for this evaluation. -/
  candidateTime : ℕ
  /-- The streamed candidate covers the complete public input. -/
  inputLength_le : x.length ≤ candidateTime
  /-- Neighborhood block length used by the executable evaluator. -/
  blockLength : ℕ
  /-- Certified finite encoding for the selected block length. -/
  encoding :
    NeighborhoodExecutableEvaluation.FiniteEncoding tm blockLength
  /-- Positivity witness required by the neighborhood decomposition. -/
  positive : 0 < blockLength
  /-- Evaluation horizon of the supplied center guess. -/
  horizon : ℕ
  /-- Streamed center guess to be checked. -/
  guess : NeighborhoodGraph.Guess.CenterGuess workTapeCount horizon
  /-- Numeric ternary movement code supplied by the outer trial loop. -/
  guessCode : ℕ
  /-- The movement code lies in the exact finite search range. -/
  guessCode_lt :
    guessCode <
      NeighborhoodGraph.Guess.Search.guessCount workTapeCount horizon
  /-- The typed guess is exactly the executable decoding of its numeric
  movement code. -/
  guess_eq :
    guess =
      NeighborhoodGraph.Guess.Enumeration.candidateGuess
        (Fin.cast
          (by
            simp [NeighborhoodGraph.Guess.Search.guessCount])
          (⟨guessCode, guessCode_lt⟩ :
            Fin
              (NeighborhoodGraph.Guess.Search.guessCount
                workTapeCount horizon)))
  /-- The block length is the canonical balanced length for this candidate,
  rather than an unrelated externally supplied parameter. -/
  blockLength_eq :
    blockLength =
      NeighborhoodEvaluator.candidateBlockLength candidateTime
  /-- The guess horizon is the canonical interval count for this candidate. -/
  horizon_eq :
    horizon =
      WorkspaceAccounting.horizon candidateTime

/-- Uniform remaining compilation boundary for the natural-residue DFS.

`setup` and `body` depend only on the fixed source machine and register
allocation. Input, candidate, encoding, and guess information enter through
`ramInput` and the represented state. The field modulus does not: this
contract targets the canonical modulus selected by
`NeighborhoodExecutableEvaluation`, and a concrete uniform `setup` must
derive and load that modulus from the runtime candidate parameters.

When this evaluator is embedded in `SearchProgram`, it deliberately ignores
the controller's separately selected `firstPrimeAtOrAbove candidateTime`.
That prime need not exceed the grouped interpolation degree. The outer
search is therefore redundant but space-safe; its register must merely be
preserved by the eventual trial kernel. `prefixInvariant_run` is a
source-level all-program-point certificate; compilation transports it to
every target-instruction prefix, including temporary products and copied
packed words. -/
structure ResidueMicrocode
    {workTapeCount : ℕ} (tm : TM workTapeCount) where
  /-- First-order control states, indexed by runtime instance data. -/
  State : ResidueInstance tm → Type
  /-- Initial represented state after uniform setup. -/
  initial : ∀ inst, State inst
  /-- Terminal-state predicate. -/
  terminal : ∀ {inst}, State inst → Prop
  /-- Pure next-state function implemented by one body execution. -/
  next : ∀ {inst}, State inst → State inst
  /-- Natural ranking function for the streamed DFS schedule. -/
  rank : ∀ {inst}, State inst → ℕ
  /-- Every nonterminal transition decreases the schedule rank. -/
  rank_next_lt : ∀ {inst} (state : State inst),
    ¬ terminal state → rank (next state) < rank state
  /-- Concrete encoding as a first-order RAM store. -/
  store : ∀ {inst}, State inst → Store
  /-- Fixed mutable-register layout. -/
  layout : Layout
  /-- Register zero is included for the public verdict ABI. -/
  zero_mem : 0 ∈ layout.footprint
  /-- Loop-test register. Zero means that the DFS is complete. -/
  active : ℕ
  /-- Uniform initialization command. -/
  setup : Cmd
  /-- One uniform first-order DFS/residue microstep. -/
  body : Cmd
  /-- Encoded public RAM input for one runtime instance. This serialization
  carries the source input, candidate, encoding, and guess, but not a
  precomputed field modulus; uniform setup computes the canonical modulus. -/
  ramInput : ResidueInstance tm → List Bool
  /-- Uniform setup realizes the initial represented store, derives the
  canonical modulus from runtime candidate parameters, and establishes any
  cache needed before fixed scratch registers shadow low public-input cells. -/
  setup_runs : ∀ inst,
    Runs setup (RAM.initRegs (ramInput inst))
      (store (initial inst))
  /-- The loop-test convention is exact. -/
  active_zero_iff : ∀ {inst} (state : State inst),
    store state active = 0 ↔ terminal state
  /-- One execution implements precisely one pure microstep. -/
  body_runs : ∀ {inst} (state : State inst),
    ¬ terminal state → Runs body (store state) (store (next state))
  /-- Setup writes only within the fixed mutable footprint. -/
  setupWritesWithin :
    RAM.Structured.Footprint.CmdWritesWithin layout.footprint setup
  /-- The body writes only within the fixed mutable footprint and therefore
  contains no indirect store. -/
  bodyWritesWithin :
    RAM.Structured.Footprint.CmdWritesWithin layout.footprint body
  /-- Every represented loop-boundary state fits the candidate envelope. -/
  bounded : ∀ {inst} (state : State inst),
    BoundedWorkspace tm.Q workTapeCount inst.candidateTime
      (store state layout.stack) (store state layout.bank)
      (fun index => store state (layout.fixed index))
  /-- Fuel horizon used for the compiled all-prefix certificate. -/
  runFuel : ResidueInstance tm → ℕ
  /-- Source-level value invariant for every setup and loop program point. -/
  prefixInvariant : ResidueInstance tm → Store → Prop
  /-- One exact invariant execution of the complete uniform program. This
  ties the all-program-point certificate to a represented terminal state. -/
  prefixInvariant_run : ∀ inst,
    ∃ final : State inst,
      terminal final ∧
      InvariantRuns (prefixInvariant inst)
        (Cmd.seq setup (.whileNonzero active body))
        (RAM.initRegs (ramInput inst)) (store final) (runFuel inst)
  /-- The fixed source code size fits the selected trial envelope. -/
  code_size_le : ∀ (inst : ResidueInstance tm) trialHorizon,
    inst.candidateTime ≤ trialHorizon →
    bitlen
        (Cmd.seq setup
          (.whileNonzero active body)).codeSize ≤
      fixedRegisterCount *
          WorkspaceAccounting.trialEnvelopeBits
            tm.Q workTapeCount trialHorizon +
        1
  /-- The fixed footprint count fits the selected trial envelope. -/
  footprint_count_le : ∀ (inst : ResidueInstance tm) trialHorizon,
    inst.candidateTime ≤ trialHorizon →
    bitlen layout.footprint.card ≤
      fixedRegisterCount *
          WorkspaceAccounting.trialEnvelopeBits
            tm.Q workTapeCount trialHorizon +
        1
  /-- Every fixed mutable address fits the selected trial envelope. -/
  address_size_le : ∀ (inst : ResidueInstance tm) trialHorizon,
    inst.candidateTime ≤ trialHorizon →
    ∀ address ∈ layout.footprint,
      bitlen address ≤
        fixedRegisterCount *
            WorkspaceAccounting.trialEnvelopeBits
              tm.Q workTapeCount trialHorizon +
          1
  /-- The source invariant bounds every mutable value by the selected trial
  envelope. `InvariantRuns.compile_prefix` transports this fact to compiled
  instruction prefixes. -/
  prefixInvariant_values : ∀ (inst : ResidueInstance tm) trialHorizon,
    inst.candidateTime ≤ trialHorizon →
    ∀ store, prefixInvariant inst store →
      ∀ address ∈ layout.footprint,
        bitlen (store address) ≤
          fixedRegisterCount *
            WorkspaceAccounting.trialEnvelopeBits
              tm.Q workTapeCount trialHorizon
  /-- Decode the two natural-residue root values for one instance. -/
  decode : ∀ (inst : ResidueInstance tm),
    Store →
      NeighborhoodExecutableEvaluation.ResidueValue
          tm inst.blockLength ×
        NeighborhoodExecutableEvaluation.ResidueValue
          tm inst.blockLength
  /-- Terminal decoding agrees exactly with the certified evaluator. -/
  terminal_correct : ∀ {inst} (state : State inst),
    terminal state →
    decode inst (store state) =
      (NeighborhoodExecutableEvaluation.Residue.profileDecision
        tm inst.x inst.blockLength inst.encoding
          inst.positive inst.horizon inst.guess).result

namespace ResidueMicrocode

/-- The complete first-order loop obtained by iterating one verified
microstep while its active register is nonzero. -/
def program
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm) :
    Cmd :=
  .seq microcode.setup
    (.whileNonzero microcode.active microcode.body)

end ResidueMicrocode

end NeighborhoodProgram

end Runtime

end TimeSpaceSimulation

end Complexity
