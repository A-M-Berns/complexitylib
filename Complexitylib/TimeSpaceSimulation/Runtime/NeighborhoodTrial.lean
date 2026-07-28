/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodTrial.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodTrial.Internal

/-!
# Register allocation for a concrete neighborhood trial

This module exposes one collision-free physical allocation shared by runtime
candidate-parameter construction and the packed neighborhood scheduler. The
single advertised trial footprint includes only that workspace and the three
controller outputs.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodTrial

namespace Registers

/-- Parameter setup writes entirely inside the single trial footprint. -/
theorem parameters_footprint_subset
    (regs : Registers controller) :
    regs.parameters.footprint ⊆ regs.footprint :=
  Internal.parameters_footprint_subset_internal regs

/-- Runtime candidate-parameter setup writes entirely within the single
trial footprint. -/
theorem parameterProgram_writesWithin
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    (regs : Registers controller) :
    RAM.Structured.Footprint.CmdWritesWithin regs.footprint
      (regs.parameterProgram Q workTapeCount) :=
  Internal.parameterProgram_writesWithin_internal
    Q workTapeCount regs

/-- The packed workspace is disjoint from every controller register. -/
theorem layout_disjoint_controller
    (regs : Registers controller) :
    Disjoint regs.layout.footprint controller.footprint :=
  Internal.layout_disjoint_controller_internal regs

/-- Exactly the three trial-output slots are controller registers in the
trial footprint. -/
theorem controller_index_mem_footprint_iff
    (regs : Registers controller) (slot : Fin 17) :
    controller.index slot ∈ regs.footprint ↔
      slot = 3 ∨ slot = 4 ∨ slot = 5 :=
  Internal.controller_index_mem_footprint_iff_internal regs slot

/-- The public ABI cell `R₀` is preserved by every footprint-respecting
trial command. -/
theorem inputLength_not_mem_footprint
    (regs : Registers controller) :
    controller.inputLength ∉ regs.footprint :=
  Internal.inputLength_not_mem_footprint_internal regs

/-- The cached public-input prefix is preserved by every
footprint-respecting trial command. -/
theorem prefixCache_not_mem_footprint
    (regs : Registers controller) :
    controller.prefixCache ∉ regs.footprint :=
  Internal.prefixCache_not_mem_footprint_internal regs

/-- The streamed candidate is preserved by every footprint-respecting trial
command. -/
theorem candidate_not_mem_footprint
    (regs : Registers controller) :
    controller.candidate ∉ regs.footprint :=
  Internal.candidate_not_mem_footprint_internal regs

/-- The current guess is preserved by every footprint-respecting trial
command. -/
theorem guess_not_mem_footprint
    (regs : Registers controller) :
    controller.guess ∉ regs.footprint :=
  Internal.guess_not_mem_footprint_internal regs

/-- The outer controller's separately searched prime is preserved by every
footprint-respecting trial command. -/
theorem prime_not_mem_footprint
    (regs : Registers controller) :
    controller.prime ∉ regs.footprint :=
  Internal.prime_not_mem_footprint_internal regs

/-- The shared controller constant one is preserved by every
footprint-respecting trial command. -/
theorem one_not_mem_footprint
    (regs : Registers controller) :
    controller.one ∉ regs.footprint :=
  Internal.one_not_mem_footprint_internal regs

/-- The outer-loop activity flag is preserved by every
footprint-respecting trial command. -/
theorem candidateActive_not_mem_footprint
    (regs : Registers controller) :
    controller.candidateActive ∉ regs.footprint :=
  Internal.candidateActive_not_mem_footprint_internal regs

/-- The inner-loop activity flag is preserved by every footprint-respecting
trial command. -/
theorem guessActive_not_mem_footprint
    (regs : Registers controller) :
    controller.guessActive ∉ regs.footprint :=
  Internal.guessActive_not_mem_footprint_internal regs

/-- A footprint-respecting trial preserves every non-output controller
register. -/
theorem runs_preserves_controller_index
    (regs : Registers controller)
    {command : RAM.Structured.Cmd}
    {initial final : RAM.Structured.Store}
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin regs.footprint command)
    (hrun : RAM.Structured.Runs command initial final)
    (slot : Fin 17)
    (hsuccess : slot ≠ 3)
    (hverdict : slot ≠ 4)
    (hhasNext : slot ≠ 5) :
    final (controller.index slot) =
      initial (controller.index slot) :=
  Internal.runs_preserves_controller_index_internal
    regs hwrites hrun slot hsuccess hverdict hhasNext

/-- A footprint-respecting trial preserves the collision-safe public-input
frame, including the cached prefix and every untouched high input cell. -/
theorem runs_preserves_inputFrame
    (regs : Registers controller)
    {command : RAM.Structured.Cmd} {input : List Bool}
    {initial final : RAM.Structured.Store}
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin regs.footprint command)
    (hrun : RAM.Structured.Runs command initial final)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    SearchProgram.InputFrame
      controller regs.footprint input final :=
  Internal.runs_preserves_inputFrame_internal
    regs hwrites hrun hframe

/-- Candidate-parameter setup terminates with the exact numerical postcondition
while preserving the collision-safe public-input frame. -/
theorem parameterProgram_runs_preserving_inputFrame
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    (regs : Registers controller)
    (input : List Bool) (initial : RAM.Structured.Store) (candidate : ℕ)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial)
    (hcandidate : initial controller.candidate = candidate) :
    ∃ final,
      RAM.Structured.Runs
        (regs.parameterProgram Q workTapeCount) initial final ∧
      CandidateParameters.Post
        Q workTapeCount candidate regs.parameters initial final ∧
      SearchProgram.InputFrame
        controller regs.footprint input final :=
  Internal.parameterProgram_runs_preserving_inputFrame_internal
    Q workTapeCount regs input initial candidate hframe hcandidate

end Registers

/-- The scheduler modulus is exactly the modulus produced by runtime
candidate-parameter construction, after using the instance's canonical block
length equation. -/
theorem fieldModulus_eq_canonicalModulus
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    NeighborhoodScheduler.fieldModulus instanceData =
      CandidateParameters.canonicalModulus
        tm.Q workTapeCount instanceData.candidateTime :=
  Internal.fieldModulus_eq_canonicalModulus_internal instanceData

/-- A successful parameter setup loads exactly the block length carried by
the scheduler instance. -/
theorem parametersPost_blockLength_eq
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    {controller : SearchProgram.Registers}
    (regs : Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    {initial final : RAM.Structured.Store}
    (hpost :
      CandidateParameters.Post tm.Q workTapeCount
        instanceData.candidateTime regs.parameters initial final) :
    final regs.parameters.blockLength =
      instanceData.blockLength :=
  Internal.parametersPost_blockLength_eq_internal
    regs instanceData hpost

/-- A successful parameter setup loads exactly the tight ceiling horizon
carried by the scheduler instance. -/
theorem parametersPost_horizon_eq
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    {controller : SearchProgram.Registers}
    (regs : Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    {initial final : RAM.Structured.Store}
    (hpost :
      CandidateParameters.Post tm.Q workTapeCount
        instanceData.candidateTime regs.parameters initial final) :
    final regs.parameters.horizon =
      instanceData.horizon :=
  Internal.parametersPost_horizon_eq_internal
    regs instanceData hpost

/-- A successful parameter setup loads the scheduler's exact canonical field
modulus rather than the outer controller's independently searched prime. -/
theorem parametersPost_modulus_eq
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    {controller : SearchProgram.Registers}
    (regs : Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    {initial final : RAM.Structured.Store}
    (hpost :
      CandidateParameters.Post tm.Q workTapeCount
        instanceData.candidateTime regs.parameters initial final) :
    final regs.parameters.primeRegisters.candidate =
      NeighborhoodScheduler.fieldModulus instanceData :=
  Internal.parametersPost_modulus_eq_internal
    regs instanceData hpost

/-- A successful parameter setup also loads the exact predecessor of the
scheduler modulus used by modular reduction. -/
theorem parametersPost_modulusPred_eq
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    {controller : SearchProgram.Registers}
    (regs : Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    {initial final : RAM.Structured.Store}
    (hpost :
      CandidateParameters.Post tm.Q workTapeCount
        instanceData.candidateTime regs.parameters initial final) :
    final regs.parameters.modulusPred =
      NeighborhoodScheduler.fieldModulus instanceData - 1 :=
  Internal.parametersPost_modulusPred_eq_internal
    regs instanceData hpost

end NeighborhoodTrial
end Runtime
end TimeSpaceSimulation
end Complexity
