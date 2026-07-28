/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.CandidateParameters.Internal

/-!
# Runtime construction of one candidate's numerical parameters

This module exposes the exact execution, fixed-destination footprint, and
all-program-point word bound for the uniform parameter-construction program.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace CandidateParameters

open RAM Structured
open NeighborhoodGraph

/-- The uniform parameter program terminates with every advertised numerical
parameter equal to its mathematical definition. -/
theorem program_runs
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    (regs : Registers) (store : Store) (candidate : ℕ)
    (hcandidate : store regs.candidate = candidate) :
    ∃ final,
      Runs (program Q workTapeCount regs) store final ∧
      Post Q workTapeCount candidate regs store final :=
  Internal.program_runs_internal Q workTapeCount regs store candidate
    hcandidate

/-- Every source-level program point respects the common mutable-value width
for a streamed candidate bounded by the advertised trial horizon. -/
theorem program_invariantRuns
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    (regs : Registers) (store : Store)
    (candidate target : ℕ)
    (hcandidate : store regs.candidate = candidate)
    (hcandidateLe : candidate ≤ target)
    (hstore :
      ValuesWithin regs.footprint
        (NeighborhoodProgram.fixedRegisterCount *
          WorkspaceAccounting.trialEnvelopeBits
            Q workTapeCount target) store) :
    ∃ final steps,
      InvariantRuns
        (ValuesWithin regs.footprint
          (NeighborhoodProgram.fixedRegisterCount *
            WorkspaceAccounting.trialEnvelopeBits
              Q workTapeCount target))
        (program Q workTapeCount regs) store final steps ∧
      Post Q workTapeCount candidate regs store final :=
  Internal.program_invariantRuns_internal Q workTapeCount regs store
    candidate target hcandidate hcandidateLe hstore

/-- Every direct source-level destination belongs to the advertised
thirty-two-register mutable footprint. -/
theorem program_sourceWritesWithin
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    (regs : Registers) :
    RAM.Structured.Footprint.CmdWritesWithin regs.footprint
      (program Q workTapeCount regs) :=
  Internal.program_sourceWritesWithin_internal Q workTapeCount regs

/-- Compilation preserves the exact fixed-register write boundary. -/
theorem program_writesWithin
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    (regs : Registers) :
    RegisterStore.DenseOverlay.FixedRegisters.Footprint.ProgramWritesWithin
      (program Q workTapeCount regs).compile regs.footprint :=
  Internal.program_writesWithin_internal Q workTapeCount regs

/-- The parameter program contains no indirect store instruction. -/
theorem program_noStore
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    (regs : Registers) :
    NeighborhoodProgram.cmdNoStore
      (program Q workTapeCount regs) :=
  Internal.program_noStore_internal Q workTapeCount regs

end CandidateParameters

end Runtime

end TimeSpaceSimulation

end Complexity
