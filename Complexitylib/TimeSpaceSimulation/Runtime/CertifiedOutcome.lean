/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.CertifiedOutcome.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.CertifiedOutcome.Internal

/-!
# Per-guess certified-search outcome

This module exposes the semantic `SearchProgram.TrialKernel.outcome` contract
for an exact `CertifiedSearch.EngineFamily`. It intentionally stops before
constructing a concrete first-order `TrialKernel`: the future command must
implement `guessCount` and `outcome` and prove its own all-prefix execution
contract.

The runtime prime is intentionally irrelevant to this specification. The
eventual command must preserve that outer-controller register and compute the
canonical Cook--Mertz modulus internally before proving refinement to this
prime-independent outcome.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace CertifiedOutcome

open NeighborhoodGraph
open NeighborhoodGraph.Guess

/-- The corrected packed-guess charge covers the complete ternary movement
counter, including every interval and named tape. -/
theorem guessCount_bitlen_le_guessBits
    (workTapeCount candidate : ℕ) :
    RAM.bitlen (guessCount workTapeCount candidate) ≤
      WorkspaceAccounting.guessBits workTapeCount candidate :=
  Internal.guessCount_bitlen_le_guessBits_internal
    workTapeCount candidate

/-- Every in-range candidate's full ternary counter fits the encompassing
streamed-trial envelope. -/
theorem guessCount_bitlen_le_trialEnvelope
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    {candidate trialHorizon : ℕ}
    (hcandidate : candidate ≤ trialHorizon) :
    RAM.bitlen (guessCount workTapeCount candidate) ≤
      WorkspaceAccounting.trialEnvelopeBits
        Q workTapeCount trialHorizon := by
  calc
    RAM.bitlen (guessCount workTapeCount candidate) ≤
        WorkspaceAccounting.guessBits workTapeCount candidate :=
      guessCount_bitlen_le_guessBits workTapeCount candidate
    _ ≤ WorkspaceAccounting.totalBits
        Q workTapeCount candidate := by
      unfold WorkspaceAccounting.totalBits
      omega
    _ ≤ WorkspaceAccounting.trialEnvelopeBits
        Q workTapeCount trialHorizon :=
      WorkspaceAccounting.totalBits_le_trialEnvelope
        Q workTapeCount hcandidate

/-- Every balanced candidate has at least one movement code. -/
theorem guessCount_pos (workTapeCount candidate : ℕ) :
    0 < guessCount workTapeCount candidate := by
  simp [guessCount, Search.guessCount]

/-- The semantic specification is currently independent of the selected
runtime prime. -/
theorem outcome_prime_irrelevant
    (tm : TM workTapeCount)
    (family : CertifiedSearch.EngineFamily tm)
    (input : List Bool) (candidate firstPrime secondPrime code : ℕ) :
    outcome tm family input candidate firstPrime code =
      outcome tm family input candidate secondPrime code :=
  rfl

/-- The actual center-movement word is a bounded runtime guess code. -/
theorem actualGuessCode_lt
    (tm : TM workTapeCount) (input : List Bool)
    (candidate : ℕ) :
    actualGuessCode tm input candidate <
      guessCount workTapeCount candidate :=
  Internal.actualGuessCode_lt_internal tm input candidate

/-- Decoding the proof-side actual code recovers the true movement guess. -/
theorem decodedGuess_actual
    (tm : TM workTapeCount) (input : List Bool)
    (candidate : ℕ)
    (hcode :
      actualGuessCode tm input candidate <
        guessCount workTapeCount candidate) :
    decodedGuess workTapeCount candidate
        (actualGuessCode tm input candidate) hcode =
      actualCenterGuess tm input
        (blockLength candidate) (horizon candidate) :=
  Internal.decodedGuess_actual_internal
    tm input candidate hcode

/-- Any Boolean returned by one locally checked per-guess outcome is a sound
source-machine decision. -/
theorem outcome_sound
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : CertifiedSearch.EngineFamily tm)
    (input : List Bool) (candidate prime code : ℕ)
    {answer : Bool}
    (hrun :
      outcome tm family input candidate prime code =
        some answer) :
    (answer = true → input ∈ L) ∧
      (answer = false → input ∉ L) :=
  Internal.outcome_sound_internal tm L actualTime hdecides
    family input candidate prime code hrun

/-- Once a candidate covers the actual source time, the bounded code of the
actual movement trajectory returns some correct Boolean at every prime. -/
theorem actualGuessCode_returns
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : CertifiedSearch.EngineFamily tm)
    (input : List Bool) (candidate prime : ℕ)
    (hcover : actualTime input.length ≤ candidate) :
    ∃ answer,
      outcome tm family input candidate prime
          (actualGuessCode tm input candidate) =
        some answer ∧
      (answer = true → input ∈ L) ∧
      (answer = false → input ∉ L) :=
  Internal.actualGuessCode_returns_internal
    tm L actualTime hdecides family input candidate prime hcover

/-- Candidate completeness in the exact existential shape needed by the
outer `SearchProgram`: at every prime, some bounded code returns a correct
verdict once the candidate covers the source time. -/
theorem candidateReturnsAt_complete
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : CertifiedSearch.EngineFamily tm)
    (input : List Bool) (candidate prime : ℕ)
    (hcover : actualTime input.length ≤ candidate) :
    ∃ answer,
      CandidateReturnsAt tm family input candidate prime answer ∧
      (answer = true → input ∈ L) ∧
      (answer = false → input ∉ L) :=
  Internal.candidateReturnsAt_complete_internal
    tm L actualTime hdecides family input candidate prime hcover

/-- Any Boolean returned by a concrete kernel refining the locally checked
semantic outcome is a sound source-machine decision. -/
theorem KernelRefines.outcome_sound
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : CertifiedSearch.EngineFamily tm)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines : KernelRefines kernel tm family)
    (input : List Bool) (candidate prime code : ℕ)
    {answer : Bool}
    (hrun :
      kernel.outcome input candidate prime code = some answer) :
    (answer = true → input ∈ L) ∧
      (answer = false → input ∉ L) :=
  Internal.kernel_outcome_sound_internal
    tm L actualTime hdecides family kernel hrefines
      input candidate prime code hrun

/-- Once a candidate covers the actual running time, a concrete refining
kernel has a bounded guess returning the correct verdict. -/
theorem KernelRefines.candidateReturns_complete
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : CertifiedSearch.EngineFamily tm)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines : KernelRefines kernel tm family)
    (input : List Bool) (candidate : ℕ)
    (hcover : actualTime input.length ≤ candidate) :
    ∃ answer,
      SearchProgram.CandidateReturns
        kernel input candidate answer ∧
      (answer = true → input ∈ L) ∧
      (answer = false → input ∉ L) :=
  Internal.kernel_candidateReturns_complete_internal
    tm L actualTime hdecides family kernel hrefines
      input candidate hcover

/-- Every concrete refining kernel eventually succeeds on every input, at
the latest once the outer candidate reaches the true source running time. -/
theorem KernelRefines.eventuallySucceeds
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : CertifiedSearch.EngineFamily tm)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines : KernelRefines kernel tm family)
    (input : List Bool) :
    SearchProgram.EventuallySucceeds kernel input :=
  Internal.kernel_eventuallySucceeds_internal
    tm L actualTime hdecides family kernel hrefines input

/-- The exact streamed guess range of a refining kernel fits the certified
trial envelope at every smaller candidate. -/
theorem KernelRefines.guessCount_bitlen_le_trialEnvelope
    (tm : TM workTapeCount)
    (family : CertifiedSearch.EngineFamily tm)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines : KernelRefines kernel tm family)
    {candidate target : ℕ}
    (hcandidate : candidate ≤ target) :
    RAM.bitlen (kernel.guessCount candidate) ≤
      WorkspaceAccounting.trialEnvelopeBits
        tm.Q workTapeCount target :=
  Internal.kernel_guessCount_bitlen_le_trialEnvelope_internal
    tm family kernel hrefines hcandidate

/-- A refining kernel whose own all-prefix width fits the common controller
bound obtains the complete cache/prime/guess/kernel envelope automatically. -/
theorem KernelRefines.prefixEnvelope
    (tm : TM workTapeCount)
    (family : CertifiedSearch.EngineFamily tm)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines : KernelRefines kernel tm family)
    (input : List Bool) (target : ℕ)
    (htarget : input.length ≤ target)
    (hkernelPrefix :
      ∀ candidate,
        input.length ≤ candidate →
        candidate ≤ target →
        ∀ prime guess,
          guess < kernel.guessCount candidate →
          kernel.prefixValueBits input candidate prime guess ≤
            controllerValueBits tm regs kernel target) :
    SearchProgram.PrefixEnvelope regs kernel input target
      (controllerValueBits tm regs kernel target) :=
  Internal.kernel_prefixEnvelope_internal
    tm family regs kernel hrefines input target htarget hkernelPrefix

/-- For a fixed source machine and concrete kernel, the complete controller
word width at the guaranteed search endpoint remains
`O(√(T(n) log T(n)))`. -/
theorem controllerValueBits_max_actualTime_isBigO
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    {actualTime T : ℕ → ℕ}
    (htime : actualTime =O T)
    (hT : ∀ n, n ≤ T n) :
    (fun n =>
      controllerValueBits tm regs kernel
        (max n (actualTime n))) =O
      ComplexityBridge.sqrtLogSpace T :=
  Internal.controllerValueBits_max_actualTime_isBigO_internal
    tm regs kernel htime hT

/-- The one-bit dense-trace cushion preserves the same
square-root-logarithmic asymptotic bound. -/
theorem controllerTraceBits_max_actualTime_isBigO
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    {actualTime T : ℕ → ℕ}
    (htime : actualTime =O T)
    (hT : ∀ n, n ≤ T n) :
    (fun n =>
      controllerValueBits tm regs kernel
          (max n (actualTime n)) + 1) =O
      ComplexityBridge.sqrtLogSpace T :=
  Internal.controllerTraceBits_max_actualTime_isBigO_internal
    tm regs kernel htime hT

/-- Fixed controller code size is absorbed by every advertised controller
word envelope. -/
theorem controller_codeSize_bitlen_le
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (target : ℕ) :
    RAM.bitlen (SearchProgram.program regs kernel).codeSize ≤
      controllerValueBits tm regs kernel target :=
  Internal.controller_codeSize_bitlen_le_internal
    tm regs kernel target

/-- Fixed mutable-footprint cardinality is absorbed by every advertised
controller word envelope. -/
theorem controller_footprintCard_bitlen_le
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (target : ℕ) :
    RAM.bitlen (regs.footprint ∪ kernel.footprint).card ≤
      controllerValueBits tm regs kernel target :=
  Internal.controller_footprintCard_bitlen_le_internal
    tm regs kernel target

/-- Every fixed mutable address is absorbed by the controller word
envelope. -/
theorem controller_address_bitlen_le
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (target : ℕ)
    {address : ℕ}
    (haddress :
      address ∈ regs.footprint ∪ kernel.footprint) :
    RAM.bitlen address ≤
      controllerValueBits tm regs kernel target :=
  Internal.controller_address_bitlen_le_internal
    tm regs kernel target haddress

/-- A future concrete kernel whose semantic fields are definitionally the
ones specified here converts the arbitrary-prime relation at the controller's
selected prime into the exact `SearchProgram.CandidateReturns` predicate. -/
theorem CandidateReturnsAt.toSearchProgram
    (tm : TM workTapeCount)
    (family : CertifiedSearch.EngineFamily tm)
    (kernel : SearchProgram.TrialKernel regs)
    (hguessCount :
      kernel.guessCount = guessCount workTapeCount)
    (houtcome :
      kernel.outcome = outcome tm family)
    (input : List Bool) (candidate : ℕ) (answer : Bool)
    (hreturns :
      CandidateReturnsAt tm family input candidate
        (SearchProgram.firstPrimeAtOrAbove candidate) answer) :
    SearchProgram.CandidateReturns
      kernel input candidate answer := by
  obtain ⟨code, hcode, hrun⟩ := hreturns
  refine ⟨code, ?_, ?_⟩
  · simpa [hguessCount] using hcode
  · simpa [houtcome] using hrun

/-- Exact outer-controller completeness for any future kernel implementing
the two semantic fields specified by this module. No executable command
inhabitant is constructed here. -/
theorem searchProgram_candidateReturns_complete
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (family : CertifiedSearch.EngineFamily tm)
    (kernel : SearchProgram.TrialKernel regs)
    (hguessCount :
      kernel.guessCount = guessCount workTapeCount)
    (houtcome :
      kernel.outcome = outcome tm family)
    (input : List Bool) (candidate : ℕ)
    (hcover : actualTime input.length ≤ candidate) :
    ∃ answer,
      SearchProgram.CandidateReturns
        kernel input candidate answer ∧
      (answer = true → input ∈ L) ∧
      (answer = false → input ∉ L) := by
  obtain ⟨answer, hreturns, htrue, hfalse⟩ :=
    candidateReturnsAt_complete tm L actualTime hdecides family
      input candidate
      (SearchProgram.firstPrimeAtOrAbove candidate) hcover
  exact ⟨answer,
    hreturns.toSearchProgram tm family kernel
      hguessCount houtcome input candidate answer,
    htrue, hfalse⟩

end CertifiedOutcome

end Runtime

end TimeSpaceSimulation

end Complexity
