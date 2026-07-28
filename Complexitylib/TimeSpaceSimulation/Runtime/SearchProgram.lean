/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.SearchProgram.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.SearchProgram.Internal

/-!
# First-order Williams outer search controller

This module exposes the generic fixed-register controller that streams
candidates, selects runtime primes, and enumerates guesses around one exact
candidate/guess trial kernel.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace SearchProgram

/-- Erasing the all-prefix certificate yields the narrow exact `Runs`
contract used by the streamed controller proof. -/
theorem TrialKernel.runs
    (kernel : TrialKernel regs) (input : List Bool)
    (store : RAM.Structured.Store)
    (hframe : InputFrame regs kernel.footprint input store)
    (hinput : store regs.inputLength = input.length)
    (hone : store regs.one = 1)
    (hguess :
      store regs.guess <
        kernel.guessCount (store regs.candidate)) :
    ∃ final,
      RAM.Structured.Runs kernel.command store final ∧
      TrialPost regs kernel.footprint kernel.guessCount
        kernel.outcome input store final :=
  Internal.trialKernel_runs_internal kernel input store
    hframe hinput hone hguess

/-- The specification-only selector is the least prime at or above its
argument. -/
theorem firstPrimeAtOrAbove_spec (lower : ℕ) :
    RAM.Structured.PrimeSearch.IsFirstPrimeAtOrAbove lower
      (firstPrimeAtOrAbove lower) :=
  Internal.firstPrimeAtOrAbove_spec_internal lower

/-- Bertrand's postulate bounds the selected prime by twice a positive
candidate. -/
theorem firstPrimeAtOrAbove_le_two_mul
    (lower : ℕ) (hlower : 0 < lower) :
    firstPrimeAtOrAbove lower ≤ 2 * lower :=
  Internal.firstPrimeAtOrAbove_le_two_mul_internal lower hlower

/-- Selecting the least prime costs at most one additional bit. -/
theorem firstPrimeAtOrAbove_bitlen_le
    (lower : ℕ) (hlower : 0 < lower) :
    RAM.bitlen (firstPrimeAtOrAbove lower) ≤
      RAM.bitlen lower + 1 :=
  Internal.firstPrimeAtOrAbove_bitlen_le_internal lower hlower

/-- The collision-safe prelude terminates from the public RAM ABI and
establishes the exact cached-prefix/untouched-suffix input frame. -/
theorem cacheInputPrefix_runs_inputFrame
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) :
    let limit := footprintLimit regs kernel.footprint
    let cached :=
      RAM.Structured.Basic.execList
        (cacheInputPrefixOps regs limit) (RAM.initRegs input)
    RAM.Structured.Runs
        (cacheInputPrefix regs limit) (RAM.initRegs input) cached ∧
      InputFrame regs kernel.footprint input cached :=
  Internal.cacheInputPrefix_runs_inputFrame_internal regs kernel input

/-- If one explicit candidate succeeds, the controller terminates no later
than that candidate. An earlier successful candidate may determine the
reported verdict. -/
theorem program_runs_bounded_candidate
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (target : ℕ)
    (targetVerdict : Bool)
    (htarget : input.length ≤ target)
    (hreturns :
      CandidateReturns kernel input target targetVerdict) :
    ∃ final verdict,
      RAM.Structured.Runs (program regs kernel)
        (RAM.initRegs input) final ∧
      ProgramPost regs kernel input verdict final ∧
      final regs.candidate ≤ target :=
  Internal.program_runs_bounded_candidate_internal regs kernel input
    target targetVerdict htarget hreturns

/-- A compositional cache/prime/kernel envelope upgrades the bounded
controller execution to an all-program-point mutable-value certificate. No
whole-controller prefix hypothesis is required. -/
theorem program_invariantRuns_bounded_candidate
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (target valueBits : ℕ)
    (targetVerdict : Bool)
    (htarget : input.length ≤ target)
    (hreturns :
      CandidateReturns kernel input target targetVerdict)
    (henvelope :
      PrefixEnvelope regs kernel input target valueBits) :
    ∃ final verdict steps,
      RAM.Structured.InvariantRuns
        (MutableValuesWithin
          (regs.footprint ∪ kernel.footprint) valueBits)
        (program regs kernel) (RAM.initRegs input) final steps ∧
      ProgramPost regs kernel input verdict final ∧
      final regs.candidate ≤ target :=
  Internal.program_invariantRuns_bounded_candidate_internal
    regs kernel input target valueBits targetVerdict htarget
    hreturns henvelope

/-- Generic completeness: the unbounded streamed controller terminates from
the ordinary public-input ABI whenever some candidate succeeds. No time oracle
is used by the executable program. -/
theorem program_runs
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool)
    (hterminates : EventuallySucceeds kernel input) :
    ∃ final verdict,
      RAM.Structured.Runs (program regs kernel)
        (RAM.initRegs input) final ∧
      ProgramPost regs kernel input verdict final :=
  Internal.program_runs_internal regs kernel input hterminates

/-- Every source-level direct write of the complete controller lies in one
fixed finite destination set. In particular, a kernel containing an indirect
`store` cannot satisfy `TrialKernel.writesWithin`. -/
theorem sourceWritesWithin
    (regs : Registers) (kernel : TrialKernel regs) :
    RAM.Structured.Footprint.CmdWritesWithin
      (regs.footprint ∪ kernel.footprint)
      (program regs kernel) :=
  Internal.sourceWritesWithin_internal regs kernel

/-- Structured compilation preserves the complete fixed write footprint. -/
theorem compiledWritesWithin
    (regs : Registers) (kernel : TrialKernel regs) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (program regs kernel).compile
      (regs.footprint ∪ kernel.footprint) :=
  Internal.compiledWritesWithin_internal regs kernel

/-- The complete controller footprint contains the public verdict/length
register R0. -/
theorem zero_mem_footprint
    (regs : Registers) (kernel : TrialKernel regs) :
    0 ∈ regs.footprint ∪ kernel.footprint := by
  apply Finset.mem_union_left
  simpa [regs.inputLength_zero] using
    regs.index_mem_footprint 0

/-- Per-prefix ordinary-RAM mutable-value bounds on the fixed destination set
lift directly to the dense-overlay trace certificate. Compiler control-flow
bounds supply the program-counter side automatically. -/
theorem traceBound
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (fuel valueBits : ℕ)
    (hcode :
      RAM.bitlen (program regs kernel).codeSize ≤ valueBits + 1)
    (hcount :
      RAM.bitlen (regs.footprint ∪ kernel.footprint).card ≤
        valueBits + 1)
    (haddresses :
      ∀ address ∈ regs.footprint ∪ kernel.footprint,
        RAM.bitlen address ≤ valueBits + 1)
    (hvalues :
      CompiledPrefixValueBound regs kernel input fuel valueBits) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.TraceBound
      (program regs kernel).compile input fuel
      (regs.footprint ∪ kernel.footprint).card
      (valueBits + 1) :=
  Internal.traceBound_internal regs kernel input fuel valueBits
    hcode hcount haddresses hvalues

/-- A compositional source-level invariant execution supplies all mutable
compiled-prefix bounds required by the dense trace certificate. -/
theorem traceBound_of_invariantRun
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (valueBits steps : ℕ)
    {final : RAM.Structured.Store}
    (hrun :
      RAM.Structured.InvariantRuns
        (MutableValuesWithin
          (regs.footprint ∪ kernel.footprint) valueBits)
        (program regs kernel) (RAM.initRegs input) final steps)
    (hcode :
      RAM.bitlen (program regs kernel).codeSize ≤ valueBits + 1)
    (hcount :
      RAM.bitlen (regs.footprint ∪ kernel.footprint).card ≤
        valueBits + 1)
    (haddresses :
      ∀ address ∈ regs.footprint ∪ kernel.footprint,
        RAM.bitlen address ≤ valueBits + 1) :
    RAM.RegisterStore.DenseOverlay.FixedRegisters.TraceBound
      (program regs kernel).compile input steps
      (regs.footprint ∪ kernel.footprint).card
      (valueBits + 1) :=
  Internal.traceBound_of_invariantRun_internal regs kernel input
    valueBits steps hrun hcode hcount haddresses

/-- The bounded streamed search and its compositional prefix envelope produce
the dense-overlay trace certificate directly. The caller supplies only the
fixed code/address side conditions; mutable prefixes are discharged by the
cache, prime-search, and trial contracts in `PrefixEnvelope`. -/
theorem traceBound_bounded_candidate
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (target valueBits : ℕ)
    (targetVerdict : Bool)
    (htarget : input.length ≤ target)
    (hreturns :
      CandidateReturns kernel input target targetVerdict)
    (henvelope :
      PrefixEnvelope regs kernel input target valueBits)
    (hcode :
      RAM.bitlen (program regs kernel).codeSize ≤ valueBits + 1)
    (hcount :
      RAM.bitlen (regs.footprint ∪ kernel.footprint).card ≤
        valueBits + 1)
    (haddresses :
      ∀ address ∈ regs.footprint ∪ kernel.footprint,
        RAM.bitlen address ≤ valueBits + 1) :
    ∃ final verdict steps,
      ProgramPost regs kernel input verdict final ∧
      final regs.candidate ≤ target ∧
      RAM.RegisterStore.DenseOverlay.FixedRegisters.TraceBound
        (program regs kernel).compile input steps
        (regs.footprint ∪ kernel.footprint).card
        (valueBits + 1) := by
  obtain ⟨final, verdict, steps, hrun, hpost, hupper⟩ :=
    program_invariantRuns_bounded_candidate regs kernel input
      target valueBits targetVerdict htarget hreturns henvelope
  exact ⟨final, verdict, steps, hpost, hupper,
    traceBound_of_invariantRun regs kernel input valueBits steps
      hrun hcode hcount haddresses⟩

/-- A terminal candidate inherits any known explicit upper bound. -/
theorem ProgramPost.candidate_bitlen_le
    (_hpost : ProgramPost regs kernel input verdict store)
    {target : ℕ} (hupper : store regs.candidate ≤ target) :
    RAM.bitlen (store regs.candidate) ≤ RAM.bitlen target :=
  Internal.programPost_candidate_bitlen_le_internal regs store hupper

/-- The selected prime has at most one more bit than the successful
candidate. -/
theorem ProgramPost.prime_bitlen_le
    (hpost : ProgramPost regs kernel input verdict store)
    (hcandidate : 0 < store regs.candidate) :
    RAM.bitlen (store regs.prime) ≤
      RAM.bitlen (store regs.candidate) + 1 :=
  Internal.programPost_prime_bitlen_le_internal hpost hcandidate

/-- Relative to a positive-input witness bound, the selected prime also costs
at most one extra bit. -/
theorem ProgramPost.prime_bitlen_le_target
    (hpost : ProgramPost regs kernel input verdict store)
    {target : ℕ} (hupper : store regs.candidate ≤ target)
    (hinput : 0 < input.length) :
    RAM.bitlen (store regs.prime) ≤ RAM.bitlen target + 1 :=
  Internal.programPost_prime_bitlen_le_target_internal
    hpost hupper hinput

/-- The successful streamed guess fits the candidate's advertised guess
count. -/
theorem ProgramPost.guess_bitlen_le
    (hpost : ProgramPost regs kernel input verdict store) :
    RAM.bitlen (store regs.guess) ≤
      RAM.bitlen
        (kernel.guessCount (store regs.candidate)) :=
  Internal.programPost_guess_bitlen_le_internal hpost

/-- Candidate, selected-prime, and streamed-guess widths packaged with one
terminating controller execution. -/
theorem program_runs_with_bit_bounds
    (regs : Registers) (kernel : TrialKernel regs)
    (input : List Bool) (target : ℕ)
    (targetVerdict : Bool)
    (htarget : input.length ≤ target)
    (hinput : 0 < input.length)
    (hreturns :
      CandidateReturns kernel input target targetVerdict) :
    ∃ final verdict,
      RAM.Structured.Runs (program regs kernel)
        (RAM.initRegs input) final ∧
      ProgramPost regs kernel input verdict final ∧
      RAM.bitlen (final regs.candidate) ≤ RAM.bitlen target ∧
      RAM.bitlen (final regs.prime) ≤ RAM.bitlen target + 1 ∧
      RAM.bitlen (final regs.guess) ≤
        RAM.bitlen
          (kernel.guessCount (final regs.candidate)) := by
  obtain ⟨final, verdict, hrun, hpost, hupper⟩ :=
    program_runs_bounded_candidate regs kernel input target
      targetVerdict htarget hreturns
  exact ⟨final, verdict, hrun, hpost,
    hpost.candidate_bitlen_le hupper,
    hpost.prime_bitlen_le_target hupper hinput,
    hpost.guess_bitlen_le⟩

/-- Every successful terminal postcondition names a genuine abstract kernel
return at its final candidate. -/
theorem ProgramPost.candidateReturns
    (hpost : ProgramPost regs kernel input verdict store) :
    CandidateReturns kernel input (store regs.candidate) verdict :=
  Internal.programPost_candidateReturns_internal hpost

/-- Generic soundness transfer from the one-trial kernel relation to the
controller's reported Boolean. -/
theorem ProgramPost.sound
    {Good : Bool → Prop}
    (hkernel :
      ∀ candidate prime guess result,
        kernel.outcome input candidate prime guess = some result →
          Good result)
    (hpost : ProgramPost regs kernel input verdict store) :
    Good verdict :=
  Internal.programPost_sound_internal hkernel hpost

end SearchProgram

end Runtime

end TimeSpaceSimulation

end Complexity
