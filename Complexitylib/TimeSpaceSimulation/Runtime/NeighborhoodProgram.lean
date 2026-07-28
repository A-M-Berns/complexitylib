/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram.Internal

/-!
# Fixed-register packed runtime for neighborhood evaluation

These first-order Structured RAM routines implement the packed stack and
catalytic-bank operations needed by the implicit-DAG evaluator. The
sixteen-register residue-bank interface performs dynamic coordinate reads,
modular additions, and modular scalings without indirect writes.

## Main results

- `pop_runs` -- divide the packed stack word by its runtime radix
- `peek_runs` -- read the least-significant digit without changing the word
- `push_runs` -- push one runtime-radix digit
- `bankUpdateAt_runs` -- read, modularly update, and replace one dynamic
  catalytic-bank coordinate
- `bankScaleRegister_runs` -- stream that coordinate update across every
  chunk of one logical Cook--Mertz register
- `*_writesWithin` -- compiled commands mutate only their advertised
  seven-, sixteen-, or seventeen-register footprints
- `*_size_le` -- exact bit-width bounds inherited from `PackedDigits`
- `packedWorkspaceBits_le_trialEnvelope` -- the two packed words and all
  fixed registers fit a constant multiple of the streamed trial envelope
- `ResidueMicrocode.program_result` -- once the isolated one-step microcode
  obligation is supplied, its terminating loop computes the canonical-modulus
  `Residue.profileDecision`; an outer controller prime is deliberately ignored
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace NeighborhoodProgram

open RAM Structured
open NeighborhoodGraph

/-- A numeric all-point bound immediately yields the corresponding bit-width
bound on every advertised register. -/
theorem ValuesWithin.bitlen_le
    {allowed : Finset ℕ} {bound valueBits : ℕ} {store : Store}
    (hstore : ValuesWithin allowed bound store)
    (hbound : RAM.bitlen bound ≤ valueBits) :
    ∀ address, address ∈ allowed →
      RAM.bitlen (store address) ≤ valueBits :=
  Internal.valuesWithin_bitlen_internal hstore hbound

/-- The reusable transient envelope covers every packed and modular raw
value from which it is assembled. -/
theorem transientValueBound_bounds
    (packedCapacity base modulus operand counter : ℕ) :
    counter ≤ transientValueBound packedCapacity base modulus operand counter ∧
    base ≤ transientValueBound packedCapacity base modulus operand counter ∧
    modulus ≤ transientValueBound packedCapacity base modulus operand counter ∧
    operand ≤ transientValueBound packedCapacity base modulus operand counter ∧
    packedCapacity ≤
      transientValueBound packedCapacity base modulus operand counter ∧
    base * packedCapacity ≤
      transientValueBound packedCapacity base modulus operand counter ∧
    operand + base * packedCapacity ≤
      transientValueBound packedCapacity base modulus operand counter ∧
    packedCapacity + operand ≤
      transientValueBound packedCapacity base modulus operand counter ∧
    packedCapacity * operand ≤
      transientValueBound packedCapacity base modulus operand counter :=
  Internal.transientValueBound_bounds_internal
    packedCapacity base modulus operand counter

/-- Repeated-subtraction reduction stays numerically bounded at every source
program point, including its transient comparison register. -/
theorem reduce_invariantRuns
    (regs : RuntimeArithmetic.ReduceRegisters)
    (allowed : Finset ℕ) (bound : ℕ)
    (store : Store) (modulus value : ℕ)
    (hmodulus : 0 < modulus)
    (hvalue : store regs.value = value)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1)
    (hvalueBound : value ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ steps,
      InvariantRuns (ValuesWithin allowed bound)
        (RuntimeArithmetic.reduce regs) store
        (RuntimeArithmetic.reduceResultStore regs
          (value % modulus) store)
        steps :=
  Internal.reduce_invariantRuns_internal regs allowed bound store
    modulus value hmodulus hvalue hmodulusValue hmodulusPred
    hvalueBound hstore

/-- Modular addition stays bounded at every source point when its unreduced
sum fits the chosen envelope. -/
theorem addMod_invariantRuns
    (regs : RuntimeArithmetic.ReduceRegisters)
    (allowed : Finset ℕ) (bound left right : ℕ)
    (store : Store) (modulus : ℕ)
    (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1)
    (hrawBound : store left + store right ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ steps,
      InvariantRuns (ValuesWithin allowed bound)
        (RuntimeArithmetic.addMod regs left right) store
        (RuntimeArithmetic.reduceResultStore regs
          ((store left + store right) % modulus) store)
        steps :=
  Internal.addMod_invariantRuns_internal regs allowed bound left
    right store modulus hmodulus hmodulusValue hmodulusPred
    hrawBound hstore

/-- Modular multiplication stays bounded at every source point when its
unreduced product fits the chosen envelope. -/
theorem mulMod_invariantRuns
    (regs : RuntimeArithmetic.ReduceRegisters)
    (allowed : Finset ℕ) (bound left right : ℕ)
    (store : Store) (modulus : ℕ)
    (hmodulus : 0 < modulus)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred :
      store regs.modulusPred = modulus - 1)
    (hrawBound : store left * store right ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ steps,
      InvariantRuns (ValuesWithin allowed bound)
        (RuntimeArithmetic.mulMod regs left right) store
        (RuntimeArithmetic.reduceResultStore regs
          ((store left * store right) % modulus) store)
        steps :=
  Internal.mulMod_invariantRuns_internal regs allowed bound left
    right store modulus hmodulus hmodulusValue hmodulusPred
    hrawBound hstore

/-- Packed-stack division stays within one common numeric bound at every
source point. In particular, this certificate covers the quotient
accumulator and every division-loop test. -/
theorem pop_invariantRuns
    (regs : StackRegisters) (allowed : Finset ℕ) (bound : ℕ)
    (store : Store) (base word : ℕ)
    (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hone : store regs.one = 1)
    (hwordBound : word ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns (ValuesWithin allowed bound)
        (pop regs) store final steps ∧
      final regs.word = PackedDigits.pop base word ∧
      final regs.quotient = 0 ∧
      final regs.test = 0 ∧
      final regs.base = base ∧
      final regs.basePred = base - 1 ∧
      final regs.one = 1 :=
  Internal.pop_invariantRuns_internal regs allowed bound store base
    word hbase hword hbaseValue hbasePred hone hwordBound hstore

/-- Packed-stack remainder extraction stays within one common numeric bound
at every source point, including the copied word and reduction scratch. -/
theorem peek_invariantRuns
    (regs : StackRegisters) (allowed : Finset ℕ) (bound : ℕ)
    (store : Store) (base word : ℕ)
    (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hwordBound : word ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ steps,
      InvariantRuns (ValuesWithin allowed bound)
        (peek regs) store
        (peekResultStore regs (PackedDigits.digit base word 0)
          store)
        steps :=
  Internal.peek_invariantRuns_internal regs allowed bound store base
    word hbase hword hbaseValue hbasePred hwordBound hstore

/-- Packed-stack push stays within one common numeric bound at every source
point when both its raw product and product-plus-digit fit that bound. -/
theorem push_invariantRuns
    (regs : StackRegisters) (allowed : Finset ℕ) (bound : ℕ)
    (store : Store) (base word value : ℕ)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hvalue : store regs.value = value)
    (hproductBound : base * word ≤ bound)
    (hpushBound : value + base * word ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    InvariantRuns (ValuesWithin allowed bound)
      (push regs) store
      (pushResultStore regs (PackedDigits.push base value word)
        store)
      3 :=
  Internal.push_invariantRuns_internal regs allowed bound store base
    word value hword hbaseValue hvalue hproductBound hpushBound
    hstore

/-- The fixed-register division loop removes the least-significant packed
digit and preserves the radix constants. -/
theorem pop_runs
    (regs : StackRegisters) (store : Store)
    (base word : ℕ) (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hone : store regs.one = 1) :
    ∃ final,
      Runs (pop regs) store final ∧
      final regs.word = PackedDigits.pop base word ∧
      final regs.quotient = 0 ∧
      final regs.test = 0 ∧
      final regs.base = base ∧
      final regs.basePred = base - 1 ∧
      final regs.one = 1 :=
  Internal.pop_runs_internal regs store base word hbase
    hword hbaseValue hbasePred hone

/-- The fixed-register remainder loop reads digit zero while preserving the
packed word. -/
theorem peek_runs
    (regs : StackRegisters) (store : Store)
    (base word : ℕ) (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1) :
    ∃ final,
      Runs (peek regs) store final ∧
      final regs.word = word ∧
      final regs.value = PackedDigits.digit base word 0 ∧
      final regs.test = 0 ∧
      final regs.base = base ∧
      final regs.basePred = base - 1 :=
  Internal.peek_runs_internal regs store base word hbase
    hword hbaseValue hbasePred

/-- The fixed-register multiplication/addition routine pushes one packed
digit. -/
theorem push_runs
    (regs : StackRegisters) (store : Store)
    (base word value : ℕ)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hvalue : store regs.value = value) :
    ∃ final,
      Runs (push regs) store final ∧
      final regs.word = PackedDigits.push base value word ∧
      final regs.quotient = 0 ∧
      final regs.base = base ∧
      final regs.value = value :=
  Internal.push_runs_internal regs store base word value
    hword hbaseValue hvalue

/-- Packed-stack pop performs no indirect write. -/
theorem pop_noStore (regs : StackRegisters) :
    cmdNoStore (pop regs) :=
  Internal.pop_noStore_internal regs

/-- Packed-stack peek performs no indirect write. -/
theorem peek_noStore (regs : StackRegisters) :
    cmdNoStore (peek regs) :=
  Internal.peek_noStore_internal regs

/-- Packed-stack push performs no indirect write. -/
theorem push_noStore (regs : StackRegisters) :
    cmdNoStore (push regs) :=
  Internal.push_noStore_internal regs

/-- The compiled packed-stack pop mutates only its seven fixed registers. -/
theorem pop_writesWithin (regs : StackRegisters) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (Cmd.compile (pop regs)) regs.footprint :=
  Internal.pop_writesWithin_internal regs

/-- The compiled packed-stack peek mutates only its seven fixed registers. -/
theorem peek_writesWithin (regs : StackRegisters) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (Cmd.compile (peek regs)) regs.footprint :=
  Internal.peek_writesWithin_internal regs

/-- The compiled packed-stack push mutates only its seven fixed registers. -/
theorem push_writesWithin (regs : StackRegisters) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (Cmd.compile (push regs)) regs.footprint :=
  Internal.push_writesWithin_internal regs

/-- The entire dynamic packed-bank read, including forward seek and reversal
restore, satisfies one numeric bound at every source program point. -/
theorem bankRead_invariantRuns
    (regs : BankRegisters) (allowed : Finset ℕ) (bound : ℕ)
    (store : Store)
    (base word index digitCount : ℕ)
    (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hone : store regs.one = 1)
    (hindex : store regs.indexCount = index)
    (hwordCapacity : word < base ^ digitCount)
    (hindexCapacity : index ≤ digitCount)
    (hpackedBound : base ^ digitCount ≤ bound)
    (hbaseBound : base ≤ bound)
    (hindexBound : index ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns (ValuesWithin allowed bound)
        (bankRead regs) store final steps ∧
      final regs.word = word ∧
      final regs.buffer = 0 ∧
      final regs.indexCount = 0 ∧
      final regs.completed = 0 ∧
      final regs.result = PackedDigits.digit base word index ∧
      final regs.base = base ∧
      final regs.basePred = base - 1 ∧
      final regs.one = 1 ∧
      final regs.replacement = store regs.replacement :=
  Internal.bankRead_invariantRuns_internal regs allowed bound store
    base word index digitCount hbase hword hbaseValue hbasePred hone
    hindex hwordCapacity hindexCapacity hpackedBound hbaseBound
    hindexBound hstore

/-- The entire dynamic packed-bank replacement stays bounded through seek,
selected-digit removal, replacement push, and reversal restore. -/
theorem bankReplace_invariantRuns
    (regs : BankRegisters) (allowed : Finset ℕ) (bound : ℕ)
    (store : Store)
    (base word index replacement digitCount : ℕ)
    (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hone : store regs.one = 1)
    (hindex : store regs.indexCount = index)
    (hreplacement : store regs.replacement = replacement)
    (hwordCapacity : word < base ^ digitCount)
    (hindexCapacity : index < digitCount)
    (hreplacementDigit : replacement < base)
    (hpackedBound : base ^ digitCount ≤ bound)
    (hbaseBound : base ≤ bound)
    (hindexBound : index ≤ bound)
    (hreplacementBound : replacement ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns (ValuesWithin allowed bound)
        (bankReplace regs) store final steps ∧
      final regs.word = replaceAt base word index replacement ∧
      final regs.buffer = 0 ∧
      final regs.indexCount = 0 ∧
      final regs.completed = 0 ∧
      final regs.result = PackedDigits.digit base word index ∧
      final regs.base = base ∧
      final regs.basePred = base - 1 ∧
      final regs.one = 1 ∧
      final regs.replacement = replacement :=
  Internal.bankReplace_invariantRuns_internal regs allowed bound store
    base word index replacement digitCount hbase hword hbaseValue
    hbasePred hone hindex hreplacement hwordCapacity hindexCapacity
    hreplacementDigit hpackedBound hbaseBound hindexBound
    hreplacementBound hstore

/-- The packed-bank streaming reader returns one dynamic digit and restores
the original packed word. -/
theorem bankRead_runs
    (regs : BankRegisters) (store : Store)
    (base word index : ℕ) (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hone : store regs.one = 1)
    (hindex : store regs.indexCount = index) :
    ∃ final,
      Runs (bankRead regs) store final ∧
      final regs.word = word ∧
      final regs.buffer = 0 ∧
      final regs.indexCount = 0 ∧
      final regs.completed = 0 ∧
      final regs.result = PackedDigits.digit base word index ∧
      final regs.base = base ∧
      final regs.basePred = base - 1 ∧
      final regs.one = 1 ∧
      final regs.replacement = store regs.replacement :=
  Internal.bankRead_runs_internal regs store base word index hbase
    hword hbaseValue hbasePred hone hindex

/-- The packed-bank streaming writer returns the old digit and installs the
replacement without dynamic register addressing. -/
theorem bankReplace_runs
    (regs : BankRegisters) (store : Store)
    (base word index replacement : ℕ) (hbase : 0 < base)
    (hword : store regs.word = word)
    (hbaseValue : store regs.base = base)
    (hbasePred : store regs.basePred = base - 1)
    (hone : store regs.one = 1)
    (hindex : store regs.indexCount = index)
    (hreplacement : store regs.replacement = replacement) :
    ∃ final,
      Runs (bankReplace regs) store final ∧
      final regs.word = replaceAt base word index replacement ∧
      final regs.buffer = 0 ∧
      final regs.indexCount = 0 ∧
      final regs.completed = 0 ∧
      final regs.result = PackedDigits.digit base word index ∧
      final regs.base = base ∧
      final regs.basePred = base - 1 ∧
      final regs.one = 1 ∧
      final regs.replacement = replacement :=
  Internal.bankReplace_runs_internal regs store base word index
    replacement hbase hword hbaseValue hbasePred hone hindex
    hreplacement

/-- One complete modular packed-bank update satisfies a common all-source-
point value bound. The raw operation hypothesis accounts for the unreduced
sum or product before the reduction loop. -/
theorem bankUpdateAt_invariantRuns
    (regs : ResidueBankRegisters) (op : ResidueBankOp)
    (allowed : Finset ℕ) (bound : ℕ)
    (store : Store)
    (base word index modulus operand digitCount : ℕ)
    (hbase : 0 < base)
    (hmodulus : 0 < modulus)
    (hmodulusBase : modulus ≤ base)
    (hword : store regs.bank.word = word)
    (hbaseValue : store regs.bank.base = base)
    (hbasePred : store regs.bank.basePred = base - 1)
    (hone : store regs.bank.one = 1)
    (hindex : store regs.bank.indexCount = index)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hoperand : store regs.operand = operand)
    (hwordCapacity : word < base ^ digitCount)
    (hindexCapacity : index < digitCount)
    (hpackedBound : base ^ digitCount ≤ bound)
    (hbaseBound : base ≤ bound)
    (hindexBound : index ≤ bound)
    (hrawBound :
      op.rawApply (PackedDigits.digit base word index) operand ≤
        bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final steps,
      InvariantRuns (ValuesWithin allowed bound)
        (bankUpdateAt regs op) store final steps ∧
      final regs.bank.word =
        replaceAt base word index
          (op.apply modulus
            (PackedDigits.digit base word index) operand) ∧
      final regs.bank.buffer = 0 ∧
      final regs.bank.indexCount = 0 ∧
      final regs.bank.completed = 0 ∧
      final regs.bank.result =
        PackedDigits.digit base word index ∧
      final regs.bank.base = base ∧
      final regs.bank.basePred = base - 1 ∧
      final regs.bank.one = 1 ∧
      final regs.bank.replacement =
        op.apply modulus
          (PackedDigits.digit base word index) operand ∧
      final regs.modulus = modulus ∧
      final regs.modulusPred = modulus - 1 ∧
      final regs.operand = operand ∧
      final regs.savedIndex = index :=
  Internal.bankUpdateAt_invariantRuns_internal regs op allowed bound
    store base word index modulus operand digitCount hbase hmodulus
    hmodulusBase hword hbaseValue hbasePred hone hindex
    hmodulusValue hmodulusPred hoperand hwordCapacity
    hindexCapacity hpackedBound hbaseBound hindexBound hrawBound
    hstore

/-- One embeddable residue-bank transition reads a dynamic coordinate,
applies modular addition or multiplication, and replaces that coordinate.
The theorem starts from an arbitrary surrounding store and preserves the
field constants and operand, so it can be called inside an outer trial
controller. -/
theorem bankUpdateAt_runs
    (regs : ResidueBankRegisters) (op : ResidueBankOp)
    (store : Store)
    (base word index modulus operand : ℕ)
    (hbase : 0 < base)
    (hmodulus : 0 < modulus)
    (hword : store regs.bank.word = word)
    (hbaseValue : store regs.bank.base = base)
    (hbasePred : store regs.bank.basePred = base - 1)
    (hone : store regs.bank.one = 1)
    (hindex : store regs.bank.indexCount = index)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hoperand : store regs.operand = operand) :
    ∃ final,
      Runs (bankUpdateAt regs op) store final ∧
      final regs.bank.word =
        replaceAt base word index
          (op.apply modulus
            (PackedDigits.digit base word index) operand) ∧
      final regs.bank.buffer = 0 ∧
      final regs.bank.indexCount = 0 ∧
      final regs.bank.completed = 0 ∧
      final regs.bank.result =
        PackedDigits.digit base word index ∧
      final regs.bank.base = base ∧
      final regs.bank.basePred = base - 1 ∧
      final regs.bank.one = 1 ∧
      final regs.bank.replacement =
        op.apply modulus
          (PackedDigits.digit base word index) operand ∧
      final regs.modulus = modulus ∧
      final regs.modulusPred = modulus - 1 ∧
      final regs.operand = operand ∧
      final regs.savedIndex = index :=
  Internal.bankUpdateAt_runs_internal regs op store base word index
    modulus operand hbase hmodulus hword hbaseValue hbasePred hone
    hindex hmodulusValue hmodulusPred hoperand

/-- The operational update theorem, projected to the selected packed
coordinate: the completed RAM command stores exactly the requested modular
addition or multiplication result. -/
theorem bankUpdateAt_selectedDigit_runs
    (regs : ResidueBankRegisters) (op : ResidueBankOp)
    (store : Store)
    (base word index modulus operand : ℕ)
    (hbase : 0 < base)
    (hmodulus : 0 < modulus)
    (hmodulusBase : modulus ≤ base)
    (hword : store regs.bank.word = word)
    (hbaseValue : store regs.bank.base = base)
    (hbasePred : store regs.bank.basePred = base - 1)
    (hone : store regs.bank.one = 1)
    (hindex : store regs.bank.indexCount = index)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hoperand : store regs.operand = operand) :
    ∃ final,
      Runs (bankUpdateAt regs op) store final ∧
      PackedDigits.digit base (final regs.bank.word) index =
        op.apply modulus
          (PackedDigits.digit base word index) operand := by
  obtain ⟨final, hrun, hfinalWord, _⟩ :=
    bankUpdateAt_runs regs op store base word index modulus operand
      hbase hmodulus hword hbaseValue hbasePred hone hindex
      hmodulusValue hmodulusPred hoperand
  refine ⟨final, hrun, ?_⟩
  rw [hfinalWord]
  exact Internal.replaceAt_digit_eq_internal hbase
    (Internal.residueBankOp_lt_internal hmodulus hmodulusBase)

/-- A modular bank update leaves every nonselected packed coordinate
unchanged. -/
theorem bankUpdateAt_otherDigit_runs
    (regs : ResidueBankRegisters) (op : ResidueBankOp)
    (store : Store)
    (base word index otherIndex modulus operand : ℕ)
    (hbase : 0 < base)
    (hmodulus : 0 < modulus)
    (hmodulusBase : modulus ≤ base)
    (hword : store regs.bank.word = word)
    (hbaseValue : store regs.bank.base = base)
    (hbasePred : store regs.bank.basePred = base - 1)
    (hone : store regs.bank.one = 1)
    (hindex : store regs.bank.indexCount = index)
    (hmodulusValue : store regs.modulus = modulus)
    (hmodulusPred : store regs.modulusPred = modulus - 1)
    (hoperand : store regs.operand = operand)
    (hother : otherIndex ≠ index) :
    ∃ final,
      Runs (bankUpdateAt regs op) store final ∧
      PackedDigits.digit base (final regs.bank.word) otherIndex =
        PackedDigits.digit base word otherIndex :=
  Internal.bankUpdateAt_otherDigit_runs_internal
    regs op store base word index otherIndex modulus operand hbase
    hmodulus hmodulusBase hword hbaseValue hbasePred hone hindex
    hmodulusValue hmodulusPred hoperand hother

/-- One embedded modular command preserves the complete packed-bank
representation while replacing exactly one logical register/chunk
coordinate. -/
theorem bankUpdateAt_represents_runs
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength : ℕ)
    (bankRegs : ResidueBankRegisters) (op : ResidueBankOp)
    (store : Store) (base word modulus operand : ℕ)
    (residueRegs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)))
    (hbase : 0 < base)
    (hmodulus : 0 < modulus)
    (hmodulusBase : modulus ≤ base)
    (hword : store bankRegs.bank.word = word)
    (hbaseValue : store bankRegs.bank.base = base)
    (hbasePred : store bankRegs.bank.basePred = base - 1)
    (hone : store bankRegs.bank.one = 1)
    (hindex :
      store bankRegs.bank.indexCount =
        residueBankIndex tm blockLength register chunk)
    (hmodulusValue : store bankRegs.modulus = modulus)
    (hmodulusPred :
      store bankRegs.modulusPred = modulus - 1)
    (hoperand : store bankRegs.operand = operand)
    (hrep :
      RepresentsResidueBank
        tm blockLength base word residueRegs) :
    ∃ final,
      Runs (bankUpdateAt bankRegs op) store final ∧
      RepresentsResidueBank tm blockLength base
        (final bankRegs.bank.word)
        (updateResidueCoordinate tm blockLength residueRegs register
          chunk
          (op.apply modulus
            (residueRegs register chunk) operand)) :=
  Internal.bankUpdateAt_represents_runs_internal
    tm blockLength bankRegs op store base word modulus operand
    residueRegs register chunk hbase hmodulus hmodulusBase hword
    hbaseValue hbasePred hone hindex hmodulusValue hmodulusPred
    hoperand hrep

/-- The source modular bank update writes only its sixteen fixed
registers. -/
theorem bankUpdateAt_sourceWritesWithin
    (regs : ResidueBankRegisters) (op : ResidueBankOp) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.footprint (bankUpdateAt regs op) :=
  Internal.bankUpdateAt_sourceWritesWithin_internal regs op

/-- Compiling a modular bank update preserves its fixed write footprint. -/
theorem bankUpdateAt_writesWithin
    (regs : ResidueBankRegisters) (op : ResidueBankOp) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (bankUpdateAt regs op).compile regs.footprint :=
  Internal.bankUpdateAt_writesWithin_internal regs op

/-- A modular bank update performs no indirect write. -/
theorem bankUpdateAt_noStore
    (regs : ResidueBankRegisters) (op : ResidueBankOp) :
    cmdNoStore (bankUpdateAt regs op) :=
  Internal.bankUpdateAt_noStore_internal regs op

/-- The whole-register scaling loop writes only its seventeen advertised
fixed registers. -/
theorem bankScaleRegister_sourceWritesWithin
    (regs : ResidueScaleRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.footprint (bankScaleRegister regs) :=
  Internal.bankScaleRegister_sourceWritesWithin_internal regs

/-- Compiling the whole-register scaling loop preserves its fixed
seventeen-register write footprint. -/
theorem bankScaleRegister_writesWithin
    (regs : ResidueScaleRegisters) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (bankScaleRegister regs).compile regs.footprint :=
  Internal.bankScaleRegister_writesWithin_internal regs

/-- The whole-register scaling loop performs no indirect write. -/
theorem bankScaleRegister_noStore
    (regs : ResidueScaleRegisters) :
    cmdNoStore (bankScaleRegister regs) :=
  Internal.bankScaleRegister_noStore_internal regs

/-- The source packed-bank reader writes only its twelve fixed registers. -/
theorem bankRead_sourceWritesWithin (regs : BankRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.footprint (bankRead regs) :=
  Internal.bankRead_sourceWritesWithin_internal regs

/-- The source packed-bank writer writes only its twelve fixed registers. -/
theorem bankReplace_sourceWritesWithin (regs : BankRegisters) :
    RAM.Structured.Footprint.CmdWritesWithin
      regs.footprint (bankReplace regs) :=
  Internal.bankReplace_sourceWritesWithin_internal regs

/-- Compiling the packed-bank reader preserves its fixed write footprint. -/
theorem bankRead_writesWithin (regs : BankRegisters) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (bankRead regs).compile regs.footprint :=
  Internal.bankRead_writesWithin_internal regs

/-- Compiling the packed-bank writer preserves its fixed write footprint. -/
theorem bankReplace_writesWithin (regs : BankRegisters) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (bankReplace regs).compile regs.footprint :=
  Internal.bankReplace_writesWithin_internal regs

/-- The streamed replacement installs its supplied value at the selected
packed coordinate. -/
theorem replaceAt_digit_eq
    {base word index value : ℕ}
    (hbase : 0 < base) (hvalue : value < base) :
    PackedDigits.digit base
        (replaceAt base word index value) index =
      value :=
  Internal.replaceAt_digit_eq_internal hbase hvalue

/-- Streamed replacement preserves every nonselected packed digit. -/
theorem replaceAt_digit_ne
    {base word index value digitIndex : ℕ}
    (hbase : 0 < base) (hvalue : value < base)
    (hne : digitIndex ≠ index) :
    PackedDigits.digit base
        (replaceAt base word index value) digitIndex =
      PackedDigits.digit base word digitIndex :=
  Internal.replaceAt_digit_ne_internal hbase hvalue hne

namespace ResidueBankOp

/-- A modular bank operation produces a valid radix digit whenever the
runtime modulus fits the packed-bank radix. -/
theorem apply_lt
    {op : ResidueBankOp} {modulus current operand base : ℕ}
    (hmodulus : 0 < modulus)
    (hmodulusBase : modulus ≤ base) :
    op.apply modulus current operand < base :=
  Internal.residueBankOp_lt_internal hmodulus hmodulusBase

end ResidueBankOp

/-- A modular bank update preserves the packed bank's exact digit-count
bound whenever the selected coordinate is in range. -/
theorem bankUpdateAt_word_lt_pow
    {op : ResidueBankOp}
    {base word count index modulus operand : ℕ}
    (hbase : 0 < base)
    (hword : word < base ^ count)
    (hindex : index < count)
    (hmodulus : 0 < modulus)
    (hmodulusBase : modulus ≤ base) :
    replaceAt base word index
        (op.apply modulus
          (PackedDigits.digit base word index) operand) <
      base ^ count :=
  Internal.bankUpdateAt_word_lt_pow_internal hbase hword hindex
    hmodulus hmodulusBase

/-- Every completed modular bank update stays within the original packed
bank bit budget. -/
theorem bankUpdateAt_word_size_le
    {op : ResidueBankOp}
    {base word count index modulus operand width : ℕ}
    (hbase : 0 < base)
    (hword : word < base ^ count)
    (hindex : index < count)
    (hmodulus : 0 < modulus)
    (hmodulusBase : modulus ≤ base)
    (hbaseWidth : base ≤ 2 ^ width) :
    (replaceAt base word index
      (op.apply modulus
        (PackedDigits.digit base word index) operand)).size ≤
      count * width :=
  Internal.bankUpdateAt_word_size_le_internal hbase hword hindex
    hmodulus hmodulusBase hbaseWidth

/-- The row-major coordinate of every catalytic register/chunk pair lies
inside the exact packed-bank digit count. -/
theorem residueBankIndex_lt
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength : ℕ)
    (register :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1))
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))) :
    residueBankIndex tm blockLength register chunk <
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1) *
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount) :=
  Internal.residueBankIndex_lt_internal tm blockLength register chunk

/-- Row-major packed-bank coordinates are collision-free. -/
theorem residueBankIndex_eq_iff
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength : ℕ)
    (firstRegister secondRegister :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (firstChunk secondChunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))) :
    residueBankIndex tm blockLength firstRegister firstChunk =
        residueBankIndex tm blockLength secondRegister secondChunk ↔
      firstRegister = secondRegister ∧ firstChunk = secondChunk :=
  Internal.residueBankIndex_eq_iff_internal tm blockLength
    firstRegister secondRegister firstChunk secondChunk

/-- Pure replacement preserves the exact logical interpretation of every
packed-bank coordinate. -/
theorem representsResidueBank_replaceAt
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength base word : ℕ)
    (regs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)))
    (value : ℕ)
    (hrep :
      RepresentsResidueBank tm blockLength base word regs)
    (hbase : 0 < base) (hvalue : value < base) :
    RepresentsResidueBank tm blockLength base
      (replaceAt base word
        (residueBankIndex tm blockLength register chunk) value)
      (updateResidueCoordinate
        tm blockLength regs register chunk value) :=
  Internal.representsResidueBank_replaceAt_internal
    tm blockLength base word regs register chunk value
    hrep hbase hvalue

/-- For a canonical candidate instance, every logical catalytic coordinate
lies inside the exact `bankDigitCount` charged by its workspace envelope. -/
theorem residueBankIndex_lt_instance
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (inst : ResidueInstance tm)
    (register :
      Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1))
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm inst.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))) :
    residueBankIndex tm inst.blockLength register chunk <
      bankDigitCount tm.Q workTapeCount inst.candidateTime :=
  Internal.residueBankIndex_lt_instance_internal
    tm inst register chunk

/-- The modular addition primitive agrees at the selected coordinate with
the natural-residue Cook--Mertz `addAt` transition. -/
theorem residueBankAdd_eq_addAt
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength : ℕ)
    (regs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (value :
      NeighborhoodExecutableEvaluation.ResidueValue tm blockLength)
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))) :
    ResidueBankOp.add.apply
        (NeighborhoodExecutableEvaluation.modulus tm blockLength)
        (regs register chunk) (value chunk) =
      (NeighborhoodExecutableEvaluation.Residue.addAt
        tm blockLength regs register value) register chunk :=
  Internal.residueBankAdd_eq_addAt_internal
    tm blockLength regs register value chunk

/-- The modular multiplication primitive agrees at the selected coordinate
with the natural-residue Cook--Mertz `scaleAt` transition. -/
theorem residueBankScale_eq_scaleAt
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength scalar : ℕ)
    (regs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))) :
    ResidueBankOp.mul.apply
        (NeighborhoodExecutableEvaluation.modulus tm blockLength)
        (regs register chunk) scalar =
      (NeighborhoodExecutableEvaluation.Residue.scaleAt
        tm blockLength scalar regs register) register chunk :=
  Internal.residueBankScale_eq_scaleAt_internal
    tm blockLength scalar regs register chunk

/-- The concrete fixed-register addition command implements one selected
natural-residue Cook--Mertz `addAt` coordinate. The command is embeddable in
an arbitrary surrounding store. -/
theorem bankAddAt_selectedDigit_runs
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength : ℕ)
    (bankRegs : ResidueBankRegisters) (store : Store)
    (base word : ℕ)
    (residueRegs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (value :
      NeighborhoodExecutableEvaluation.ResidueValue tm blockLength)
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)))
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hword : store bankRegs.bank.word = word)
    (hbaseValue : store bankRegs.bank.base = base)
    (hbasePred : store bankRegs.bank.basePred = base - 1)
    (hone : store bankRegs.bank.one = 1)
    (hindex :
      store bankRegs.bank.indexCount =
        residueBankIndex tm blockLength register chunk)
    (hmodulusValue :
      store bankRegs.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store bankRegs.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hoperand : store bankRegs.operand = value chunk)
    (hpacked :
      PackedDigits.digit base word
          (residueBankIndex tm blockLength register chunk) =
        residueRegs register chunk) :
    ∃ final,
      Runs (bankAddAt bankRegs) store final ∧
      PackedDigits.digit base (final bankRegs.bank.word)
          (residueBankIndex tm blockLength register chunk) =
        (NeighborhoodExecutableEvaluation.Residue.addAt
          tm blockLength residueRegs register value) register chunk :=
  Internal.bankAddAt_selectedDigit_runs_internal
    tm blockLength bankRegs store base word residueRegs register value
    chunk hbase hmodulus hmodulusBase hword hbaseValue hbasePred hone
    hindex hmodulusValue hmodulusPred hoperand hpacked

/-- The concrete fixed-register multiplication command implements one
selected natural-residue Cook--Mertz `scaleAt` coordinate. The command is
embeddable in an arbitrary surrounding store. -/
theorem bankScaleAt_selectedDigit_runs
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength scalar : ℕ)
    (bankRegs : ResidueBankRegisters) (store : Store)
    (base word : ℕ)
    (residueRegs :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)))
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hword : store bankRegs.bank.word = word)
    (hbaseValue : store bankRegs.bank.base = base)
    (hbasePred : store bankRegs.bank.basePred = base - 1)
    (hone : store bankRegs.bank.one = 1)
    (hindex :
      store bankRegs.bank.indexCount =
        residueBankIndex tm blockLength register chunk)
    (hmodulusValue :
      store bankRegs.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store bankRegs.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hoperand : store bankRegs.operand = scalar)
    (hpacked :
      PackedDigits.digit base word
          (residueBankIndex tm blockLength register chunk) =
        residueRegs register chunk) :
    ∃ final,
      Runs (bankScaleAt bankRegs) store final ∧
      PackedDigits.digit base (final bankRegs.bank.word)
          (residueBankIndex tm blockLength register chunk) =
        (NeighborhoodExecutableEvaluation.Residue.scaleAt
          tm blockLength scalar residueRegs register) register chunk :=
  Internal.bankScaleAt_selectedDigit_runs_internal
    tm blockLength scalar bankRegs store base word residueRegs register
    chunk hbase hmodulus hmodulusBase hword hbaseValue hbasePred hone
    hindex hmodulusValue hmodulusPred hoperand hpacked

/-- The full seventeen-register scaling loop satisfies one numeric bound at
every source program point. The packed-capacity and scalar-product
hypotheses account respectively for every seek/restore word and every
unreduced modular multiplication. -/
theorem bankScaleRegister_invariantRuns
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength scalar base word : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (regs : ResidueScaleRegisters)
    (allowed : Finset ℕ) (bound : ℕ) (store : Store)
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hword : store regs.bank.bank.word = word)
    (hrep :
      RepresentsResidueBank
        tm blockLength base word original)
    (hwordLt :
      word <
        base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)))
    (hbaseValue : store regs.bank.bank.base = base)
    (hbasePred : store regs.bank.bank.basePred = base - 1)
    (hone : store regs.bank.bank.one = 1)
    (hindex :
      store regs.bank.bank.indexCount =
        register.val *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount))
    (hmodulusValue :
      store regs.bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store regs.bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hoperand : store regs.bank.operand = scalar)
    (hremaining :
      store regs.remaining =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount))
    (hpackedBound :
      base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) ≤
        bound)
    (hbaseBound : base ≤ bound)
    (hdigitCountBound :
      (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1) *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) ≤
        bound)
    (hscalarProductBound : base * scalar ≤ bound)
    (hstore : ValuesWithin allowed bound store) :
    ∃ final finalWord steps,
      InvariantRuns (ValuesWithin allowed bound)
        (bankScaleRegister regs) store final steps ∧
      final regs.bank.bank.word = finalWord ∧
      RepresentsResidueBank tm blockLength base finalWord
        (NeighborhoodExecutableEvaluation.Residue.scaleAt
          tm blockLength scalar original register) ∧
      finalWord <
        base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) ∧
      (∀ chunk,
        PackedDigits.digit base finalWord
            (residueBankIndex tm blockLength register chunk) =
          (NeighborhoodExecutableEvaluation.Residue.scaleAt
            tm blockLength scalar original register) register chunk) ∧
      (∀ currentRegister, currentRegister ≠ register →
        ∀ chunk,
          PackedDigits.digit base finalWord
              (residueBankIndex
                tm blockLength currentRegister chunk) =
            original currentRegister chunk) ∧
      final regs.remaining = 0 ∧
      final regs.bank.bank.indexCount =
        register.val *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount) +
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) ∧
      final regs.bank.bank.base = base ∧
      final regs.bank.bank.basePred = base - 1 ∧
      final regs.bank.bank.one = 1 ∧
      final regs.bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength ∧
      final regs.bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1 ∧
      final regs.bank.operand = scalar :=
  Internal.bankScaleRegister_invariantRuns_internal
    tm blockLength scalar base word original register regs allowed
    bound store hbase hmodulus hmodulusBase hword hrep hwordLt
    hbaseValue hbasePred hone hindex hmodulusValue hmodulusPred
    hoperand hremaining hpackedBound hbaseBound hdigitCountBound
    hscalarProductBound hstore

/-- The seventeen-register streamed loop scales every chunk of one
Cook--Mertz catalytic register. Its final packed word represents the exact
logical `Residue.scaleAt`; the theorem separately exposes both the selected
chunk values and preservation of every nonselected logical register. -/
theorem bankScaleRegister_runs
    {workTapeCount : ℕ}
    (tm : TM workTapeCount) (blockLength scalar base word : ℕ)
    (original :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm blockLength)
    (register :
      Fin
        (NeighborhoodExecutableEvaluation.graphFanIn
          workTapeCount + 1))
    (regs : ResidueScaleRegisters) (store : Store)
    (hbase : 0 < base)
    (hmodulus :
      0 < NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusBase :
      NeighborhoodExecutableEvaluation.modulus tm blockLength ≤ base)
    (hword : store regs.bank.bank.word = word)
    (hrep :
      RepresentsResidueBank
        tm blockLength base word original)
    (hwordLt :
      word <
        base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)))
    (hbaseValue : store regs.bank.bank.base = base)
    (hbasePred : store regs.bank.bank.basePred = base - 1)
    (hone : store regs.bank.bank.one = 1)
    (hindex :
      store regs.bank.bank.indexCount =
        register.val *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount))
    (hmodulusValue :
      store regs.bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength)
    (hmodulusPred :
      store regs.bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1)
    (hoperand : store regs.bank.operand = scalar)
    (hremaining :
      store regs.remaining =
        TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth tm blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn
            workTapeCount)) :
    ∃ final finalWord,
      Runs (bankScaleRegister regs) store final ∧
      final regs.bank.bank.word = finalWord ∧
      RepresentsResidueBank tm blockLength base finalWord
        (NeighborhoodExecutableEvaluation.Residue.scaleAt
          tm blockLength scalar original register) ∧
      finalWord <
        base ^
          ((NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount + 1) *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount)) ∧
      (∀ chunk,
        PackedDigits.digit base finalWord
            (residueBankIndex tm blockLength register chunk) =
          (NeighborhoodExecutableEvaluation.Residue.scaleAt
            tm blockLength scalar original register) register chunk) ∧
      (∀ currentRegister, currentRegister ≠ register →
        ∀ chunk,
          PackedDigits.digit base finalWord
              (residueBankIndex
                tm blockLength currentRegister chunk) =
            original currentRegister chunk) ∧
      final regs.remaining = 0 ∧
      final regs.bank.bank.indexCount =
        register.val *
            TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
              (NeighborhoodExecutableEvaluation.payloadWidth
                tm blockLength)
              (NeighborhoodExecutableEvaluation.graphFanIn
                workTapeCount) +
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (NeighborhoodExecutableEvaluation.payloadWidth
              tm blockLength)
            (NeighborhoodExecutableEvaluation.graphFanIn
              workTapeCount) ∧
      final regs.bank.bank.base = base ∧
      final regs.bank.bank.basePred = base - 1 ∧
      final regs.bank.bank.one = 1 ∧
      final regs.bank.modulus =
        NeighborhoodExecutableEvaluation.modulus tm blockLength ∧
      final regs.bank.modulusPred =
        NeighborhoodExecutableEvaluation.modulus tm blockLength - 1 ∧
      final regs.bank.operand = scalar :=
  Internal.bankScaleRegister_runs_internal
    tm blockLength scalar base word original register regs store
    hbase hmodulus hmodulusBase hword hrep hwordLt hbaseValue
    hbasePred hone hindex hmodulusValue hmodulusPred hoperand
    hremaining

/-- Pushing one bounded digit grows the packed width by at most one digit. -/
theorem pushedWord_size_le
    {base value word count width : ℕ}
    (hword : word < base ^ count)
    (hvalue : value < base)
    (hbaseWidth : base ≤ 2 ^ width) :
    (PackedDigits.push base value word).size ≤
      (count + 1) * width :=
  Internal.pushedWord_size_le_internal hword hvalue hbaseWidth

/-- Popping a bounded nonempty word removes one digit's width. -/
theorem poppedWord_size_le
    {base word count width : ℕ}
    (hbase : 0 < base)
    (hword : word < base ^ (count + 1))
    (hbaseWidth : base ≤ 2 ^ width) :
    (PackedDigits.pop base word).size ≤ count * width :=
  Internal.poppedWord_size_le_internal hbase hword hbaseWidth

/-- A peeked digit fits in the selected digit width. -/
theorem peekedDigit_size_le
    {base word width : ℕ}
    (hbase : 0 < base)
    (hbaseWidth : base ≤ 2 ^ width) :
    (PackedDigits.digit base word 0).size ≤ width :=
  Internal.peekedDigit_size_le_internal hbase hbaseWidth

/-- A bounded continuation stack fits the exact stack charge used by the
direct-neighborhood workspace accounting. -/
theorem stackWord_size_le
    {Q : Type*} [Fintype Q] {workTapeCount candidate stackWord : ℕ}
    (hstack :
      stackWord <
        frameRadix Q workTapeCount candidate ^
          WorkspaceAccounting.horizon candidate) :
    stackWord.size ≤
      WorkspaceAccounting.stackBits Q workTapeCount candidate :=
  Internal.stackWord_size_le_internal hstack

/-- A bounded residue bank fits the exact catalytic-bank charge. -/
theorem bankWord_size_le
    {Q : Type*} [Fintype Q]
    {workTapeCount candidate bankWord : ℕ}
    (hbank :
      bankWord <
        bankRadix Q workTapeCount candidate ^
          bankDigitCount Q workTapeCount candidate) :
    bankWord.size ≤
      WorkspaceAccounting.catalyticBankBits
        Q workTapeCount candidate :=
  Internal.bankWord_size_le_internal hbank

/-- The concrete packed stack, packed residue bank, and fixed-register
contents fit a fixed multiple of every encompassing streamed-trial
workspace envelope. -/
theorem packedWorkspaceBits_le_trialEnvelope
    {Q : Type*} [Fintype Q] (workTapeCount : ℕ)
    {candidate trialHorizon stackWord bankWord : ℕ}
    {fixedValues : Fin fixedRegisterCount → ℕ}
    (hcandidate : candidate ≤ trialHorizon)
    (hbounded :
      BoundedWorkspace Q workTapeCount candidate
        stackWord bankWord fixedValues) :
    packedWorkspaceBits stackWord bankWord fixedValues ≤
      fixedRegisterCount *
        WorkspaceAccounting.trialEnvelopeBits
          Q workTapeCount trialHorizon :=
  Internal.packedWorkspaceBits_le_trialEnvelope_internal
    workTapeCount hcandidate hbounded

/-- Along any family satisfying the concrete packing invariant, the packed
words and fixed registers are asymptotically bounded by the streamed-trial
workspace envelope. -/
theorem packedWorkspaceBits_isBigO_trialEnvelope
    {Q : Type*} [Fintype Q] (workTapeCount : ℕ)
    (stackWord bankWord : ℕ → ℕ)
    (fixedValues : ℕ → Fin fixedRegisterCount → ℕ)
    (hbounded : ∀ candidate,
      BoundedWorkspace Q workTapeCount candidate
        (stackWord candidate) (bankWord candidate)
        (fixedValues candidate)) :
    (fun candidate =>
      packedWorkspaceBits (stackWord candidate) (bankWord candidate)
        (fixedValues candidate)) =O
      (fun candidate =>
        WorkspaceAccounting.trialEnvelopeBits
          Q workTapeCount candidate) :=
  Internal.packedWorkspaceBits_isBigO_trialEnvelope_internal
    workTapeCount stackWord bankWord fixedValues hbounded

namespace ResidueMicrocode

/-- Iterating a rank-decreasing verified microstep reaches a terminal
first-order RAM store. -/
theorem loop_runs
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm)
    {inst : ResidueInstance tm} (state : microcode.State inst) :
    ∃ final : microcode.State inst,
      microcode.terminal final ∧
      Runs (.whileNonzero microcode.active microcode.body)
        (microcode.store state)
        (microcode.store final) :=
  Internal.microcode_loop_runs_internal microcode state

/-- Uniform setup followed by the terminating microstep loop decodes to
exactly the existing canonical-modulus natural-residue profile decision.
When embedded under `SearchProgram`, this result does not consume the
controller's separately searched prime. -/
theorem program_result
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm)
    (inst : ResidueInstance tm) :
    ∃ final,
      Runs microcode.program
        (RAM.initRegs (microcode.ramInput inst)) final ∧
      microcode.decode inst final =
        (NeighborhoodExecutableEvaluation.Residue.profileDecision
          tm inst.x inst.blockLength inst.encoding inst.positive
            inst.horizon inst.guess).result :=
  Internal.microcode_program_result_internal microcode inst

/-- Uniform setup and loop write only inside their advertised footprint. -/
theorem program_sourceWritesWithin
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm) :
    RAM.Structured.Footprint.CmdWritesWithin
      microcode.layout.footprint microcode.program :=
  Internal.microcode_program_sourceWritesWithin_internal microcode

/-- Compiling the uniform program preserves its exact fixed footprint. -/
theorem program_writesWithin
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      microcode.program.compile microcode.layout.footprint :=
  Internal.microcode_program_writesWithin_internal microcode

/-- The evaluator loop contains no indirect write. Immutable indirect reads
remain available to its microstep body. -/
theorem program_noStore
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm) :
    cmdNoStore microcode.program :=
  Internal.microcode_program_noStore_internal microcode

/-- Every loop-boundary mutable value fits the encompassing envelope. The
stronger all-compiled-prefix fact is packaged by `traceBound`. -/
theorem mutableValue_size_le
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm)
    {inst : ResidueInstance tm} {trialHorizon : ℕ}
    (hcandidate : inst.candidateTime ≤ trialHorizon)
    (state : microcode.State inst) {address : ℕ}
    (haddress : address ∈ microcode.layout.footprint) :
    (microcode.store state address).size ≤
      fixedRegisterCount *
        WorkspaceAccounting.trialEnvelopeBits
          tm.Q workTapeCount trialHorizon :=
  Internal.microcode_mutableValue_size_le_internal
    microcode hcandidate state haddress

/-- The source invariant bounds every mutable value after every compiled
instruction prefix, including prefixes inside arithmetic loops. -/
theorem compiledPrefix_mutableValue_size_le
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm)
    (inst : ResidueInstance tm) (trialHorizon : ℕ)
    (hcandidate : inst.candidateTime ≤ trialHorizon)
    (k : ℕ) (hk : k ≤ microcode.runFuel inst)
    (address : ℕ)
    (haddress : address ∈ microcode.layout.footprint) :
    RAM.bitlen
        ((RAM.run microcode.program.compile k
          (RAM.initCfg (microcode.ramInput inst))).regs address) ≤
      fixedRegisterCount *
        WorkspaceAccounting.trialEnvelopeBits
          tm.Q workTapeCount trialHorizon :=
  Internal.microcode_compiledPrefix_mutableValue_size_le_internal
    microcode inst trialHorizon hcandidate k hk address haddress

/-- The uniform compiled evaluator has an exact dense-overlay trace
certificate. `ResidueMicrocode.prefixInvariant_run` certifies every
source-program point, and `InvariantRuns.compile_prefix` transports that
invariant to every compiled instruction prefix. Thus temporary products and
cached input-prefix values are covered rather than inferred from
loop-boundary stores. -/
theorem traceBound
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (microcode : ResidueMicrocode tm)
    (inst : ResidueInstance tm) (trialHorizon : ℕ)
    (hcandidate : inst.candidateTime ≤ trialHorizon) :
    RegisterStore.DenseOverlay.FixedRegisters.TraceBound
      microcode.program.compile (microcode.ramInput inst)
      (microcode.runFuel inst) microcode.layout.footprint.card
      (fixedRegisterCount *
          WorkspaceAccounting.trialEnvelopeBits
            tm.Q workTapeCount trialHorizon +
        1) :=
  Internal.microcode_traceBound_internal
    microcode inst trialHorizon hcandidate

end ResidueMicrocode

end NeighborhoodProgram

end Runtime

end TimeSpaceSimulation

end Complexity
