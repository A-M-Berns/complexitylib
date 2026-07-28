/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.CertifiedSearch.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.SearchProgram.Defs

/-!
# Per-guess certified-search outcome — definitions

This module specifies the pure outcome relation that a future
`SearchProgram.TrialKernel.command` must implement. For one balanced
candidate it decodes one bounded ternary movement code, runs the complete
local consistency check, and only after that check passes asks the exact
engine for the decision snapshot.

The runtime-prime argument is intentionally unused. It remains in the
signature so the definition has exactly the shape of
`SearchProgram.TrialKernel.outcome`. The concrete arithmetic implementation
will preserve that outer-controller value while internally computing the
canonical Cook--Mertz modulus from the candidate parameters.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace CertifiedOutcome

open NeighborhoodGraph
open NeighborhoodGraph.Guess

/-- Balanced block length attached to one candidate time. -/
def blockLength (candidate : ℕ) : ℕ :=
  WorkspaceAccounting.blockLength candidate

/-- Least balanced interval horizon covering one candidate time. -/
def horizon (candidate : ℕ) : ℕ :=
  WorkspaceAccounting.horizon candidate

/-- Number of bounded ternary movement guesses at one candidate. -/
def guessCount (workTapeCount candidate : ℕ) : ℕ :=
  Search.guessCount workTapeCount (horizon candidate)

/-- Decode an in-range natural counter as one typed movement guess. -/
def decodedGuess
    (workTapeCount candidate code : ℕ)
    (hcode : code < guessCount workTapeCount candidate) :
    CenterGuess workTapeCount (horizon candidate) :=
  Enumeration.candidateGuess
    (Fin.cast
      (by simp [guessCount, Search.guessCount])
      (⟨code, hcode⟩ :
        Fin (guessCount workTapeCount candidate)))

/-- Exact semantic outcome of one candidate/guess trial.

The full local `Consistency.passes` check is evaluated before
`engine.snapshot`. Failure, a nonhalting snapshot, or an illegal verdict
symbol all return `none`. The outer-controller prime is deliberately ignored;
the future first-order implementation computes the canonical evaluator
modulus internally. -/
@[nolint unusedArguments]
def outcome
    (tm : TM workTapeCount)
    (family : CertifiedSearch.EngineFamily tm)
    (input : List Bool) (candidate : ℕ)
    (_prime : ℕ) (code : ℕ) : Option Bool :=
  if hcode : code < guessCount workTapeCount candidate then
    let engine := family.engine input candidate
    let guess := decodedGuess workTapeCount candidate code hcode
    match Consistency.passes tm input (blockLength candidate)
        (EvaluatedProvider.provider engine.node) guess with
    | false => none
    | true =>
        match engine.snapshot guess with
        | none => none
        | some snapshot =>
            if snapshot.state = tm.qhalt then
              CertifiedTrial.decodeVerdict snapshot.verdict
            else
              none
  else
    none

/-- `SearchProgram.CandidateReturns`-shaped relation at an explicitly
supplied prime. This is the semantic relation a future concrete
`TrialKernel` obtains by setting its `guessCount` and `outcome` fields to the
definitions above. -/
def CandidateReturnsAt
    (tm : TM workTapeCount)
    (family : CertifiedSearch.EngineFamily tm)
    (input : List Bool) (candidate prime : ℕ)
    (verdict : Bool) : Prop :=
  ∃ code, code < guessCount workTapeCount candidate ∧
    outcome tm family input candidate prime code = some verdict

/-- A concrete first-order trial kernel implements the certified semantic
guess count and per-guess outcome. This relation says nothing about how the
command proves its operational or all-prefix resource contract; those are
already fields of `SearchProgram.TrialKernel`. -/
structure KernelRefines
    (kernel : SearchProgram.TrialKernel regs)
    (tm : TM workTapeCount)
    (family : CertifiedSearch.EngineFamily tm) : Prop where
  /-- The streamed numeric guess range is exact. -/
  guessCount_eq : ∀ candidate,
    kernel.guessCount candidate =
      guessCount workTapeCount candidate
  /-- Every pure outcome named by the operational kernel is the fully
  locally checked certified outcome. -/
  outcome_eq : ∀ input candidate prime code,
    kernel.outcome input candidate prime code =
      outcome tm family input candidate prime code

/-- Fixed code, footprint-cardinality, and register-address contribution to
the controller's mutable-word envelope. -/
def controllerStaticBits
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs) : ℕ :=
  max (SearchProgram.footprintLimit regs kernel.footprint)
    (max
      (RAM.bitlen (SearchProgram.program regs kernel).codeSize)
      (RAM.bitlen
        (regs.footprint ∪ kernel.footprint).card))

/-- Common mutable-word width for the controller around one certified trial
horizon. The first maximum absorbs fixed program data. The runtime term uses
the conservative fixed-register multiplier already exposed by the concrete
neighborhood microcode, and two extra bits cover prime-search small cases. -/
def controllerValueBits
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (target : ℕ) : ℕ :=
  max (controllerStaticBits regs kernel)
    (NeighborhoodProgram.fixedRegisterCount *
        WorkspaceAccounting.trialEnvelopeBits
          tm.Q workTapeCount target +
      2)

/-- Proof-side code of the actual center-movement trajectory. It is used only
as the completeness witness and is absent from `outcome`. -/
def actualGuessCode
    (tm : TM workTapeCount) (input : List Bool)
    (candidate : ℕ) : ℕ :=
  (Enumeration.encodeMovementCode
    (actualCenterGuess tm input
      (blockLength candidate) (horizon candidate))).val

end CertifiedOutcome

end Runtime

end TimeSpaceSimulation

end Complexity
