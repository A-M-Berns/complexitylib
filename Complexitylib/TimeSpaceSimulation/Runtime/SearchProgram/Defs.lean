/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Data.Nat.Prime.Infinite
import Complexitylib.Models.RandomAccessMachine.Structured.Footprint.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.Invariant.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.PrimeSearch

/-!
# First-order Williams outer search controller — definitions

This module defines the fixed-register control plane around one abstract
candidate/guess trial. The controller streams candidate times upward from the
input length, selects the least prime at or above each candidate, and streams
all guesses without allocating a list. The only evaluator-specific component
is `TrialKernel.command`, governed by one exact all-prefix invariant contract.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace SearchProgram

open RAM Structured

/-- Seventeen distinct controller registers. The first eight implement the
outer loops, the next eight are viewed as a `PrimeSearch.Registers`
allocation, and the final register holds the cached public-input prefix. -/
structure Registers where
  /-- Injective physical allocation of the controller registers. -/
  index : Fin 17 → ℕ
  /-- Distinct logical fields occupy distinct concrete registers. -/
  injective : Function.Injective index
  /-- The public ABI length cell is the controller's length register. -/
  inputLength_zero : index 0 = 0
  /-- Register one is reserved for the collision-safe input-prefix cache. -/
  prefixCache_one : index 16 = 1

namespace Registers

/-- Canonical public allocation used by the end-to-end simulator.

Logical slot zero is physical `R₀`, the prefix cache in logical slot sixteen
is physical `R₁`, and swapping logical slots one and sixteen assigns every
remaining slot a distinct address in `R₂, …, R₁₆`. -/
def canonical : Registers where
  index := fun slot =>
    ((Equiv.swap (1 : Fin 17) (16 : Fin 17)) slot).val
  injective := by
    intro first second heq
    apply (Equiv.swap (1 : Fin 17) (16 : Fin 17)).injective
    exact Fin.ext heq
  inputLength_zero := by
    simp [Equiv.swap_apply_def]
  prefixCache_one := by
    simp

/-- Every canonical controller register lies in the fixed physical prefix
`R₀, …, R₁₆`. -/
theorem canonical_index_lt (slot : Fin 17) :
    canonical.index slot < 17 :=
  ((Equiv.swap (1 : Fin 17) (16 : Fin 17)) slot).isLt

/-- Distinct logical fields occupy distinct concrete registers. -/
theorem index_ne (regs : Registers) {first second : Fin 17}
    (hne : first ≠ second) :
    regs.index first ≠ regs.index second :=
  fun heq => hne (regs.injective heq)

/-- Equality of allocated registers reflects equality of logical slots. -/
@[simp]
theorem index_inj_iff (regs : Registers) {first second : Fin 17} :
    regs.index first = regs.index second ↔ first = second :=
  regs.injective.eq_iff

/-- Preserved input length and initial candidate lower bound. -/
abbrev inputLength (regs : Registers) : ℕ := regs.index 0

/-- Current streamed candidate time. -/
abbrev candidate (regs : Registers) : ℕ := regs.index 1

/-- Current streamed guess code. -/
abbrev guess (regs : Registers) : ℕ := regs.index 2

/-- One exactly when the current kernel trial succeeds. -/
abbrev success (regs : Registers) : ℕ := regs.index 3

/-- Boolean verdict written by a successful kernel trial. -/
abbrev verdict (regs : Registers) : ℕ := regs.index 4

/-- One exactly when another guess follows the current guess. -/
abbrev hasNext (regs : Registers) : ℕ := regs.index 5

/-- Inner guess-loop test. -/
abbrev guessActive (regs : Registers) : ℕ := regs.index 6

/-- Outer candidate-loop test. -/
abbrev candidateActive (regs : Registers) : ℕ := regs.index 7

/-- Embed a prime-search slot into the upper half of the allocation. -/
def primeSlot (slot : Fin 8) : Fin 17 :=
  ⟨slot.val + 8, by omega⟩

/-- The upper eight registers, viewed as the fixed-register prime search. -/
def primeRegisters (regs : Registers) :
    RAM.Structured.PrimeSearch.Registers where
  index := fun slot => regs.index (primeSlot slot)
  injective := by
    intro first second heq
    apply Fin.ext
    have hslot := regs.injective heq
    exact Nat.add_right_cancel (congrArg Fin.val hslot)

/-- Selected runtime prime. -/
abbrev prime (regs : Registers) : ℕ :=
  regs.primeRegisters.candidate

/-- Constant-one register shared with the prime-search program. -/
abbrev one (regs : Registers) : ℕ :=
  regs.primeRegisters.one

/-- Packed copy of every public input cell that can be shadowed by a fixed
mutable destination. -/
abbrev prefixCache (regs : Registers) : ℕ :=
  regs.index 16

/-- The finite mutable-address footprint of the controller allocation. -/
def footprint (regs : Registers) : Finset ℕ :=
  Finset.univ.image regs.index

/-- Every controller register belongs to its advertised footprint. -/
@[simp]
theorem index_mem_footprint (regs : Registers) (slot : Fin 17) :
    regs.index slot ∈ regs.footprint :=
  Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

end Registers

/-- Largest fixed mutable destination used by the controller and trial. -/
def footprintLimit (regs : Registers) (kernelFootprint : Finset ℕ) : ℕ :=
  (regs.footprint ∪ kernelFootprint).sup
    (fun address : ℕ => address)

/-- Straight-line operations that pack the initial public cells
`R₁, …, R_limit` into `R₁`.

Only the accumulator is written. At iteration `j`, the source `R_j` has
therefore not yet been shadowed. -/
def cacheInputPrefixOps (regs : Registers) (limit : ℕ) : List Basic :=
  .mul regs.prefixCache regs.prefixCache regs.prefixCache ::
    (List.range (limit - 1)).flatMap fun offset =>
      let address := offset + 2
      [.add regs.prefixCache regs.prefixCache regs.prefixCache,
        .add regs.prefixCache regs.prefixCache address]

/-- Uniform collision-safe public-input preprocessing. -/
def cacheInputPrefix (regs : Registers) (limit : ℕ) : Cmd :=
  Cmd.basics (cacheInputPrefixOps regs limit)

/-- Exact packed prefix produced by `cacheInputPrefix`. This operational
definition deliberately fixes the bit order used by the later cached-input
lookup routine. -/
def prefixCacheValue
    (regs : Registers) (input : List Bool) (limit : ℕ) : ℕ :=
  (Basic.execList (cacheInputPrefixOps regs limit)
    (RAM.initRegs input)) regs.prefixCache

/-- The mutable overlay still represents the actual public input: every
possibly shadowed cell is available in the packed prefix cache, while every
larger address still agrees with the ordinary public-input ABI. -/
def InputFrame
    (regs : Registers) (kernelFootprint : Finset ℕ)
    (input : List Bool) (store : Store) : Prop :=
  store regs.prefixCache =
      prefixCacheValue regs input
        (footprintLimit regs kernelFootprint) ∧
    ∀ address,
      footprintLimit regs kernelFootprint < address →
        store address = RAM.initRegs input address

/-- Natural encoding of whether an optional trial result is successful. -/
@[simp]
def successValue : Option Bool → ℕ
  | none => 0
  | some _ => 1

/-- Natural encoding of an optional Boolean verdict. Failure writes zero. -/
@[simp]
def verdictValue : Option Bool → ℕ
  | none => 0
  | some verdict => Input.bitValue verdict

/-- Natural encoding of whether another in-range guess follows `guess`. -/
def hasNextValue (guessCount guess : ℕ) : ℕ :=
  if guess + 1 < guessCount then 1 else 0

/-- Exact postcondition required of one candidate/prime/guess kernel call.

The kernel may use arbitrary additional fixed scratch registers, but it must
preserve the controller state named here and write the three advertised
outputs exactly. -/
structure TrialPost
    (regs : Registers)
    (kernelFootprint : Finset ℕ)
    (guessCount : ℕ → ℕ)
    (outcome : List Bool → ℕ → ℕ → ℕ → Option Bool)
    (input : List Bool)
    (initial final : Store) : Prop where
  /-- The collision-safe representation of the actual public input remains
  valid after the trial. -/
  inputFrame :
    InputFrame regs kernelFootprint input final
  /-- The immutable input length is preserved. -/
  inputLength_eq :
    final regs.inputLength = initial regs.inputLength
  /-- The current candidate is preserved. -/
  candidate_eq :
    final regs.candidate = initial regs.candidate
  /-- The selected prime is preserved. -/
  prime_eq :
    final regs.prime = initial regs.prime
  /-- The current guess is preserved. -/
  guess_eq :
    final regs.guess = initial regs.guess
  /-- The shared constant one is preserved. -/
  one_eq :
    final regs.one = initial regs.one
  /-- The outer loop flag is preserved. -/
  candidateActive_eq :
    final regs.candidateActive = initial regs.candidateActive
  /-- The inner loop flag is preserved. -/
  guessActive_eq :
    final regs.guessActive = initial regs.guessActive
  /-- Success exactly reflects the abstract trial outcome. -/
  success_eq :
    final regs.success =
      successValue
        (outcome input (initial regs.candidate)
          (initial regs.prime) (initial regs.guess))
  /-- The verdict exactly reflects the abstract trial outcome. -/
  verdict_eq :
    final regs.verdict =
      verdictValue
        (outcome input (initial regs.candidate)
          (initial regs.prime) (initial regs.guess))
  /-- Guess exhaustion is exact. -/
  hasNext_eq :
    final regs.hasNext =
      hasNextValue
        (guessCount (initial regs.candidate))
        (initial regs.guess)

/-- Narrow uniform executable contract for one candidate/prime/guess trial. -/
structure TrialKernel (regs : Registers) where
  /-- First-order trial command. -/
  command : Cmd
  /-- Finite set of direct destinations used by the trial command. -/
  footprint : Finset ℕ
  /-- The trial contains no indirect store and writes only its fixed
  footprint. -/
  writesWithin :
    RAM.Structured.Footprint.CmdWritesWithin footprint command
  /-- Positive number of guesses for each candidate. -/
  guessCount : ℕ → ℕ
  /-- Every candidate has at least one guess. -/
  guessCount_pos : ∀ candidate, 0 < guessCount candidate
  /-- Pure outcome modeled by one command call. -/
  outcome : List Bool → ℕ → ℕ → ℕ → Option Bool
  /-- Advertised mutable-value width for one trial prefix. -/
  prefixValueBits : List Bool → ℕ → ℕ → ℕ → ℕ
  /-- Source-level all-program-point certificate for one trial. This is the
  compositional form consumed by `InvariantRuns.compile_prefix`; unlike
  `Runs`, it does not discard intermediate mutable-value bounds. -/
  prefixInvariantRuns : ∀ (input : List Bool) (store : Store),
    InputFrame regs footprint input store →
    store regs.inputLength = input.length →
    store regs.one = 1 →
    store regs.guess < guessCount (store regs.candidate) →
    ∃ final steps,
      InvariantRuns
        (fun current =>
          ∀ address, address ∈ regs.footprint ∪ footprint →
            bitlen (current address) ≤
              prefixValueBits input (store regs.candidate)
                (store regs.prime) (store regs.guess))
        command store final steps ∧
      TrialPost regs footprint guessCount outcome input store final

/-- Least prime at or above a lower bound, used only in specifications. -/
noncomputable def firstPrimeAtOrAbove (lower : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes lower)

/-- The kernel succeeds at one explicit candidate and Boolean verdict. -/
def CandidateReturns
    (kernel : TrialKernel regs) (input : List Bool) (candidate : ℕ)
    (verdict : Bool) : Prop :=
  ∃ guess, guess < kernel.guessCount candidate ∧
    kernel.outcome input candidate
      (firstPrimeAtOrAbove candidate) guess =
      some verdict

/-- Some candidate at or above `inputLength` succeeds. This is the exact
termination premise for the unbounded streamed controller. -/
def EventuallySucceeds
    (kernel : TrialKernel regs) (input : List Bool) : Prop :=
  ∃ candidate verdict,
    input.length ≤ candidate ∧
    CandidateReturns kernel input candidate verdict

/-- Stop both loops after a successful trial. -/
def stopOnSuccess (regs : Registers) : Cmd :=
  Cmd.seq
    (.basic (.imm regs.candidateActive 0))
    (.basic (.imm regs.guessActive 0))

/-- Advance the guess when one remains; otherwise stop the inner loop. -/
def advanceGuessOrStop (regs : Registers) : Cmd :=
  .ifZero regs.hasNext
    (.basic (.imm regs.guessActive 0))
    (.basic (.add regs.guess regs.guess regs.one))

/-- Interpret one kernel result and update the loop controls. -/
def finishTrial (regs : Registers) : Cmd :=
  .ifZero regs.success
    (advanceGuessOrStop regs)
    (stopOnSuccess regs)

/-- One streamed guess iteration. -/
def guessBody (regs : Registers)
    (kernel : TrialKernel regs) : Cmd :=
  Cmd.seq kernel.command (finishTrial regs)

/-- Enumerate guesses without materializing a list. -/
def guessLoop (regs : Registers)
    (kernel : TrialKernel regs) : Cmd :=
  .whileNonzero regs.guessActive (guessBody regs kernel)

/-- Copy the candidate into the prime-search register. -/
def initializePrime (regs : Registers) : Cmd :=
  .basic (.mul regs.prime regs.candidate regs.one)

/-- Reset the streamed guess counter. -/
def initializeGuesses (regs : Registers) : Cmd :=
  Cmd.seq
    (.basic (.imm regs.guess 0))
    (.basic (.imm regs.guessActive 1))

/-- Advance the candidate only when no successful guess stopped the search. -/
def advanceCandidateOnFailure (regs : Registers) : Cmd :=
  .ifZero regs.candidateActive .skip
    (.basic (.add regs.candidate regs.candidate regs.one))

/-- Select a prime and enumerate all guesses for one candidate. -/
def candidateBody (regs : Registers)
    (kernel : TrialKernel regs) : Cmd :=
  Cmd.seq (initializePrime regs)
    (Cmd.seq
      (RAM.Structured.PrimeSearch.search regs.primeRegisters)
      (Cmd.seq (initializeGuesses regs)
        (Cmd.seq (guessLoop regs kernel)
          (advanceCandidateOnFailure regs))))

/-- Initialize the streamed candidate counter from the input length. -/
def setup (regs : Registers) : Cmd :=
  Cmd.seqList
    [.basic (.imm regs.one 1),
      .basic (.mul regs.candidate regs.inputLength regs.one),
      .basic (.imm regs.candidateActive 1)]

/-- Search controller before publishing its Boolean result through the
standard RAM output cell. This command preserves `R₀` as the input length
while the kernel still needs the public-input ABI. -/
def coreProgram (regs : Registers)
    (kernel : TrialKernel regs) : Cmd :=
  Cmd.seq
    (cacheInputPrefix regs
      (footprintLimit regs kernel.footprint))
    (Cmd.seq (setup regs)
      (.whileNonzero regs.candidateActive
        (candidateBody regs kernel)))

/-- Copy the successful verdict into the standard RAM output cell `R₀`. -/
def publishVerdict (regs : Registers) : Cmd :=
  .basic (.mul regs.inputLength regs.verdict regs.one)

/-- Complete unbounded Williams outer search controller, including the
standard terminal ABI write `R₀ := verdict`. -/
def program (regs : Registers)
    (kernel : TrialKernel regs) : Cmd :=
  Cmd.seq (coreProgram regs kernel) (publishVerdict regs)

/-- Uniform mutable-value width assertion for every ordinary compiled-RAM
prefix on the controller's complete fixed destination set. -/
def CompiledPrefixValueBound
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (fuel valueBits : ℕ) : Prop :=
  ∀ k, k ≤ fuel → ∀ address,
    address ∈ regs.footprint ∪ kernel.footprint →
      bitlen
        ((RAM.run (program regs kernel).compile k
          (RAM.initCfg input)).regs address) ≤ valueBits

/-- Source-store form of a uniform mutable-value bound, designed for
composition with `InvariantRuns`. -/
def MutableValuesWithin
    (allowed : Finset ℕ) (valueBits : ℕ) (store : Store) : Prop :=
  ∀ address, address ∈ allowed →
    bitlen (store address) ≤ valueBits

/-- Compositional all-prefix resource envelope for one bounded controller
execution.

The cache and prime-search fields isolate the two reusable runtime lemmas
outside the abstract trial kernel. All remaining controller updates are
certified from the numeric target, guess-count, and kernel-prefix fields. -/
structure PrefixEnvelope
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (target valueBits : ℕ) : Prop where
  /-- Zero/one control flags fit the advertised word width. -/
  one_le : 1 ≤ valueBits
  /-- The largest streamed candidate fits the advertised word width. -/
  target_bitlen : bitlen target ≤ valueBits
  /-- The collision-safe cache prelude has an all-prefix certificate and
  establishes the public-input frame. -/
  cacheInvariantRuns :
    ∃ cached steps,
      InvariantRuns
        (MutableValuesWithin
          (regs.footprint ∪ kernel.footprint) valueBits)
        (cacheInputPrefix regs
          (footprintLimit regs kernel.footprint))
        (RAM.initRegs input) cached steps ∧
      InputFrame regs kernel.footprint input cached
  /-- Prime selection preserves the common mutable-value invariant. This is
  deliberately a prime-search-local obligation rather than an opaque premise
  about the complete outer controller. -/
  primeSearchInvariantRuns :
    ∀ candidate store,
      input.length ≤ candidate →
      candidate ≤ target →
      store regs.prime = candidate →
      MutableValuesWithin
        (regs.footprint ∪ kernel.footprint) valueBits store →
      ∃ final steps,
        InvariantRuns
          (MutableValuesWithin
            (regs.footprint ∪ kernel.footprint) valueBits)
          (RAM.Structured.PrimeSearch.search regs.primeRegisters)
          store final steps ∧
        RAM.Structured.PrimeSearch.SearchPost
          regs.primeRegisters candidate final
  /-- Every in-range streamed guess fits the common word width. -/
  guessCount_bitlen :
    ∀ candidate,
      input.length ≤ candidate →
      candidate ≤ target →
      bitlen (kernel.guessCount candidate) ≤ valueBits
  /-- The trial kernel's own all-prefix budget fits the common word width
  throughout the bounded candidate interval. -/
  kernelPrefix_le :
    ∀ candidate,
      input.length ≤ candidate →
      candidate ≤ target →
      ∀ prime guess,
        guess < kernel.guessCount candidate →
        kernel.prefixValueBits input candidate prime guess ≤
          valueBits

/-- Exact successful terminal state of the controller. -/
structure ProgramPost
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (verdict : Bool) (store : Store) : Prop where
  /-- The collision-safe representation still denotes the actual input. -/
  inputFrame : InputFrame regs kernel.footprint input store
  /-- The successful Boolean is published through the standard output cell
  `R₀`. -/
  output_eq :
    store regs.inputLength = Input.bitValue verdict
  /-- Candidates are streamed upward from the input length. -/
  candidate_ge : input.length ≤ store regs.candidate
  /-- The selected prime is exactly the least prime for the final candidate. -/
  prime_eq :
    store regs.prime =
      firstPrimeAtOrAbove (store regs.candidate)
  /-- The successful guess is in range. -/
  guess_lt :
    store regs.guess <
      kernel.guessCount (store regs.candidate)
  /-- The final trial outcome is exactly the reported verdict. -/
  outcome_eq :
    kernel.outcome input (store regs.candidate)
      (store regs.prime) (store regs.guess) =
        some verdict
  /-- The numeric result register contains the reported Boolean. -/
  verdict_eq :
    store regs.verdict = Input.bitValue verdict
  /-- The success flag is set. -/
  success_eq : store regs.success = 1
  /-- The shared constant one is preserved. -/
  one_eq : store regs.one = 1
  /-- The inner loop is inactive on exit. -/
  guessActive_eq : store regs.guessActive = 0
  /-- The outer loop is inactive on exit. -/
  candidateActive_eq : store regs.candidateActive = 0

end SearchProgram

end Runtime

end TimeSpaceSimulation

end Complexity
