/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Structured.Footprint
import
  Complexitylib.TimeSpaceSimulation.Runtime.CandidateParameters
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodTrial.Defs

/-!
# Register allocation for a concrete neighborhood trial -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodTrial
namespace Internal

open RAM Structured

variable {controller : SearchProgram.Registers}

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} {command : Cmd}
    (hsubset : small ⊆ large)
    (hwrites : Footprint.CmdWritesWithin small command) :
    Footprint.CmdWritesWithin large command := by
  induction command with
  | skip =>
      trivial
  | basic op =>
      cases op <;>
        simp_all [Footprint.CmdWritesWithin, Footprint.BasicWritesWithin]
      all_goals exact hsubset hwrites
  | seq first second firstIH secondIH =>
      exact
        ⟨firstIH hwrites.1, secondIH hwrites.2⟩
  | ifZero register onZero onNonzero onZeroIH onNonzeroIH =>
      exact
        ⟨onZeroIH hwrites.1, onNonzeroIH hwrites.2⟩
  | whileNonzero register body bodyIH =>
      exact bodyIH hwrites

private theorem layout_address
    (regs : Registers controller) {address : ℕ}
    (haddress : address ∈ regs.layout.footprint) :
    ∃ slot, address = regs.index slot := by
  simp only [NeighborhoodProgram.Layout.footprint, Registers.layout,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image, Finset.mem_univ, true_and] at haddress
  rcases haddress with (rfl | rfl) | ⟨slot, rfl⟩
  · exact ⟨32, rfl⟩
  · exact ⟨33, rfl⟩
  · exact ⟨Registers.fixedSlot slot, rfl⟩

theorem parameters_footprint_subset_internal
    (regs : Registers controller) :
    regs.parameters.footprint ⊆ regs.footprint := by
  intro address haddress
  obtain ⟨slot, _, rfl⟩ := Finset.mem_image.mp haddress
  apply Finset.mem_union_left
  exact NeighborhoodProgram.Layout.fixed_mem_footprint regs.layout slot

theorem parameterProgram_writesWithin_internal
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    (regs : Registers controller) :
    Footprint.CmdWritesWithin regs.footprint
      (regs.parameterProgram Q workTapeCount) := by
  apply cmdWritesWithin_mono
    (parameters_footprint_subset_internal regs)
  exact
    CandidateParameters.program_sourceWritesWithin
      Q workTapeCount regs.parameters

theorem layout_disjoint_controller_internal
    (regs : Registers controller) :
    Disjoint regs.layout.footprint controller.footprint := by
  rw [Finset.disjoint_left]
  intro address hlayout hcontroller
  obtain ⟨workspaceSlot, rfl⟩ := layout_address regs hlayout
  obtain ⟨controllerSlot, _, hslot⟩ :=
    Finset.mem_image.mp hcontroller
  exact regs.index_ne_controller workspaceSlot controllerSlot hslot.symm

theorem controller_index_mem_footprint_iff_internal
    (regs : Registers controller) (slot : Fin 17) :
    controller.index slot ∈ regs.footprint ↔
      slot = 3 ∨ slot = 4 ∨ slot = 5 := by
  constructor
  · intro hmem
    rw [Registers.footprint, Finset.mem_union] at hmem
    rcases hmem with hlayout | houtput
    · exact False.elim
        (Finset.disjoint_left.mp
          (layout_disjoint_controller_internal regs)
          hlayout (controller.index_mem_footprint slot))
    · simp only [Registers.outputFootprint, Finset.mem_insert,
        Finset.mem_singleton] at houtput
      rcases houtput with heq | heq | heq
      · exact Or.inl (controller.injective heq)
      · exact Or.inr (Or.inl (controller.injective heq))
      · exact Or.inr (Or.inr (controller.injective heq))
  · intro hslot
    apply Finset.mem_union_right
    rcases hslot with rfl | rfl | rfl
    · simp [Registers.outputFootprint]
    · simp [Registers.outputFootprint]
    · simp [Registers.outputFootprint]

theorem inputLength_not_mem_footprint_internal
    (regs : Registers controller) :
    controller.inputLength ∉ regs.footprint := by
  simpa using
    (not_congr
      (controller_index_mem_footprint_iff_internal regs (0 : Fin 17))).mpr
      (by decide)

theorem prefixCache_not_mem_footprint_internal
    (regs : Registers controller) :
    controller.prefixCache ∉ regs.footprint := by
  simpa using
    (not_congr
      (controller_index_mem_footprint_iff_internal regs (16 : Fin 17))).mpr
      (by decide)

theorem candidate_not_mem_footprint_internal
    (regs : Registers controller) :
    controller.candidate ∉ regs.footprint := by
  simpa using
    (not_congr
      (controller_index_mem_footprint_iff_internal regs (1 : Fin 17))).mpr
      (by decide)

theorem guess_not_mem_footprint_internal
    (regs : Registers controller) :
    controller.guess ∉ regs.footprint := by
  simpa using
    (not_congr
      (controller_index_mem_footprint_iff_internal regs (2 : Fin 17))).mpr
      (by decide)

theorem prime_not_mem_footprint_internal
    (regs : Registers controller) :
    controller.prime ∉ regs.footprint := by
  simpa [SearchProgram.Registers.prime,
    SearchProgram.Registers.primeRegisters,
    SearchProgram.Registers.primeSlot] using
    (not_congr
      (controller_index_mem_footprint_iff_internal regs (8 : Fin 17))).mpr
      (by decide)

theorem one_not_mem_footprint_internal
    (regs : Registers controller) :
    controller.one ∉ regs.footprint := by
  simpa [SearchProgram.Registers.one,
    SearchProgram.Registers.primeRegisters,
    SearchProgram.Registers.primeSlot] using
    (not_congr
      (controller_index_mem_footprint_iff_internal regs (14 : Fin 17))).mpr
      (by decide)

theorem candidateActive_not_mem_footprint_internal
    (regs : Registers controller) :
    controller.candidateActive ∉ regs.footprint := by
  simpa using
    (not_congr
      (controller_index_mem_footprint_iff_internal regs (7 : Fin 17))).mpr
      (by decide)

theorem guessActive_not_mem_footprint_internal
    (regs : Registers controller) :
    controller.guessActive ∉ regs.footprint := by
  simpa using
    (not_congr
      (controller_index_mem_footprint_iff_internal regs (6 : Fin 17))).mpr
      (by decide)

theorem runs_preserves_controller_index_internal
    (regs : Registers controller)
    {command : Cmd} {initial final : Store}
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin regs.footprint command)
    (hrun : Runs command initial final)
    (slot : Fin 17)
    (hsuccess : slot ≠ 3)
    (hverdict : slot ≠ 4)
    (hhasNext : slot ≠ 5) :
    final (controller.index slot) =
      initial (controller.index slot) := by
  apply RAM.Structured.Footprint.runs_eq_outside hwrites hrun
  rw [controller_index_mem_footprint_iff_internal regs slot]
  simp [hsuccess, hverdict, hhasNext]

theorem runs_preserves_inputFrame_internal
    (regs : Registers controller)
    {command : Cmd} {input : List Bool}
    {initial final : Store}
    (hwrites :
      RAM.Structured.Footprint.CmdWritesWithin regs.footprint command)
    (hrun : Runs command initial final)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial) :
    SearchProgram.InputFrame
      controller regs.footprint input final := by
  constructor
  · exact
      (RAM.Structured.Footprint.runs_eq_outside hwrites hrun
        (prefixCache_not_mem_footprint_internal regs)).trans hframe.1
  · intro address hlimit
    calc
      final address = initial address := by
        apply RAM.Structured.Footprint.runs_eq_outside hwrites hrun
        intro hmember
        have hallMember :
            address ∈ controller.footprint ∪ regs.footprint :=
          Finset.mem_union_right _ hmember
        have hle :
            address ≤
              SearchProgram.footprintLimit
                controller regs.footprint := by
          exact Finset.le_sup
            (f := fun value : ℕ => value) hallMember
        omega
      _ = RAM.initRegs input address :=
        hframe.2 address hlimit

theorem parameterProgram_runs_preserving_inputFrame_internal
    (Q : Type*) [Fintype Q] (workTapeCount : ℕ)
    (regs : Registers controller)
    (input : List Bool) (initial : Store) (candidate : ℕ)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint input initial)
    (hcandidate : initial controller.candidate = candidate) :
    ∃ final,
      Runs (regs.parameterProgram Q workTapeCount) initial final ∧
      CandidateParameters.Post
        Q workTapeCount candidate regs.parameters initial final ∧
      SearchProgram.InputFrame
        controller regs.footprint input final := by
  obtain ⟨final, hrun, hpost⟩ :=
    CandidateParameters.program_runs
      Q workTapeCount regs.parameters initial candidate hcandidate
  exact
    ⟨final, hrun, hpost,
      runs_preserves_inputFrame_internal regs
        (parameterProgram_writesWithin_internal Q workTapeCount regs)
        hrun hframe⟩

theorem fieldModulus_eq_canonicalModulus_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    NeighborhoodScheduler.fieldModulus instanceData =
      CandidateParameters.canonicalModulus
        tm.Q workTapeCount instanceData.candidateTime := by
  unfold NeighborhoodScheduler.fieldModulus
  unfold NeighborhoodExecutableEvaluation.modulus
  unfold CandidateParameters.canonicalModulus
  unfold CandidateParameters.degreeEndpoint
  rw [instanceData.blockLength_eq]
  unfold NeighborhoodExecutableEvaluation.payloadWidth
  rw [ComputationGraph.CompactEncoding.width_eq]
  simp only [NeighborhoodExecutableEvaluation.graphFanIn,
    NeighborhoodEvaluator.fanIn,
    CandidateParameters.booleanWidth, CandidateParameters.fanIn,
    NeighborhoodGraph.WorkspaceAccounting.booleanWidth,
    NeighborhoodGraph.WorkspaceAccounting.fanIn,
    NeighborhoodEvaluator.candidateBlockLength,
    NeighborhoodGraph.WorkspaceAccounting.blockLength]

theorem parametersPost_blockLength_eq_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    {controller : SearchProgram.Registers}
    (regs : Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    {initial final : Store}
    (hpost :
      CandidateParameters.Post tm.Q workTapeCount
        instanceData.candidateTime regs.parameters initial final) :
    final regs.parameters.blockLength =
      instanceData.blockLength := by
  rw [hpost.blockLength_eq, instanceData.blockLength_eq]
  rfl

theorem parametersPost_horizon_eq_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    {controller : SearchProgram.Registers}
    (regs : Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    {initial final : Store}
    (hpost :
      CandidateParameters.Post tm.Q workTapeCount
        instanceData.candidateTime regs.parameters initial final) :
    final regs.parameters.horizon =
      instanceData.horizon := by
  rw [hpost.horizon_eq, instanceData.horizon_eq]

theorem parametersPost_modulus_eq_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    {controller : SearchProgram.Registers}
    (regs : Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    {initial final : Store}
    (hpost :
      CandidateParameters.Post tm.Q workTapeCount
        instanceData.candidateTime regs.parameters initial final) :
    final regs.parameters.primeRegisters.candidate =
      NeighborhoodScheduler.fieldModulus instanceData := by
  rw [hpost.modulus_eq,
    fieldModulus_eq_canonicalModulus_internal instanceData]

theorem parametersPost_modulusPred_eq_internal
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    {controller : SearchProgram.Registers}
    (regs : Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    {initial final : Store}
    (hpost :
      CandidateParameters.Post tm.Q workTapeCount
        instanceData.candidateTime regs.parameters initial final) :
    final regs.parameters.modulusPred =
      NeighborhoodScheduler.fieldModulus instanceData - 1 := by
  rw [hpost.modulusPred_eq,
    fieldModulus_eq_canonicalModulus_internal instanceData]

end Internal
end NeighborhoodTrial
end Runtime
end TimeSpaceSimulation
end Complexity
