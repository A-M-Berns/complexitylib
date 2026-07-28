/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Classes
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay
import Complexitylib.Models.RandomAccessMachine.Structured
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation.CertifiedSearch
import Complexitylib.TimeSpaceSimulation.Runtime.CertifiedOutcome
import Complexitylib.TimeSpaceSimulation.Runtime.SearchProgram

/-!
# Source-language correctness of the compiled outer search -- internals
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace LanguageDecision

open RAM Structured

namespace Internal

private theorem programPost_sound
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines :
      CertifiedOutcome.KernelRefines kernel tm
        (NeighborhoodExecutableEvaluation.Residue.engineFamily
          tm order))
    (input : List Bool) (answer : Bool)
    (final : Store)
    (hpost :
      SearchProgram.ProgramPost
        regs kernel input answer final) :
    (answer = true → input ∈ L) ∧
      (answer = false → input ∉ L) := by
  apply hpost.sound
  intro candidate prime guess result houtcome
  exact CertifiedOutcome.KernelRefines.outcome_sound
    tm L actualTime hdecides
    (NeighborhoodExecutableEvaluation.Residue.engineFamily tm order)
    kernel hrefines input candidate prime guess houtcome

private theorem answer_true_iff
    {input : List Bool} {L : Language} {answer : Bool}
    (hsound :
      (answer = true → input ∈ L) ∧
        (answer = false → input ∉ L)) :
    answer = true ↔ input ∈ L := by
  constructor
  · exact hsound.1
  · intro hmember
    cases answer with
    | false =>
        exact False.elim ((hsound.2 rfl) hmember)
    | true =>
        rfl

private theorem answer_false_iff
    {input : List Bool} {L : Language} {answer : Bool}
    (hsound :
      (answer = true → input ∈ L) ∧
        (answer = false → input ∉ L)) :
    answer = false ↔ input ∉ L := by
  constructor
  · exact hsound.2
  · intro hnotMember
    cases answer with
    | false =>
        rfl
    | true =>
        exact False.elim (hnotMember (hsound.1 rfl))

private theorem sourceExecution
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines :
      CertifiedOutcome.KernelRefines kernel tm
        (NeighborhoodExecutableEvaluation.Residue.engineFamily
          tm order))
    (input : List Bool) :
    ∃ final answer steps cost space,
      Exec (SearchProgram.program regs kernel)
          (RAM.initRegs input) final steps cost space ∧
        SearchProgram.ProgramPost
          regs kernel input answer final ∧
        (answer = true → input ∈ L) ∧
        (answer = false → input ∉ L) := by
  have hterminates :
      SearchProgram.EventuallySucceeds kernel input :=
    CertifiedOutcome.KernelRefines.eventuallySucceeds
      tm L actualTime hdecides
      (NeighborhoodExecutableEvaluation.Residue.engineFamily tm order)
      kernel hrefines input
  obtain ⟨final, answer, hrun, hpost⟩ :=
    SearchProgram.program_runs regs kernel input hterminates
  obtain ⟨steps, cost, space, hexec⟩ := hrun
  exact ⟨final, answer, steps, cost, space, hexec, hpost,
    programPost_sound tm L actualTime hdecides order regs kernel
      hrefines input answer final hpost⟩

theorem compiledHaltsWithLanguageVerdict_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines :
      CertifiedOutcome.KernelRefines kernel tm
        (NeighborhoodExecutableEvaluation.Residue.engineFamily
          tm order)) :
    ∀ input, ∃ fuel answer,
      RAM.Halted (SearchProgram.program regs kernel).compile
        (RAM.run (SearchProgram.program regs kernel).compile fuel
          (RAM.initCfg input)) ∧
      (RAM.run (SearchProgram.program regs kernel).compile fuel
          (RAM.initCfg input)).verdict =
        Input.bitValue answer ∧
      (answer = true ↔ input ∈ L) ∧
      (answer = false ↔ input ∉ L) := by
  intro input
  obtain ⟨final, answer, steps, cost, space, hexec, hpost,
      hsound⟩ :=
    sourceExecution tm L actualTime hdecides order regs kernel
      hrefines input
  have hcompiled :=
    Exec.compile_correct hexec
  have hrun :
      RAM.run (SearchProgram.program regs kernel).compile steps
          (RAM.initCfg input) =
        { pc := (SearchProgram.program regs kernel).codeSize,
          regs := final } := by
    simpa [RAM.initCfg] using hcompiled.1
  have hhalt :
      RAM.Halted (SearchProgram.program regs kernel).compile
        (RAM.run (SearchProgram.program regs kernel).compile steps
          (RAM.initCfg input)) := by
    simpa [RAM.initCfg] using Exec.compile_halted hexec
  have houtput :
      (RAM.run (SearchProgram.program regs kernel).compile steps
          (RAM.initCfg input)).verdict =
        Input.bitValue answer := by
    rw [hrun]
    change final 0 = Input.bitValue answer
    rw [← regs.inputLength_zero]
    exact hpost.output_eq
  exact ⟨steps, answer, hhalt, houtput,
    answer_true_iff hsound, answer_false_iff hsound⟩

theorem compiledBoundedExecution_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines :
      CertifiedOutcome.KernelRefines kernel tm
        (NeighborhoodExecutableEvaluation.Residue.engineFamily
          tm order))
    (input : List Bool) (target valueBits : ℕ)
    (htarget : input.length ≤ target)
    (hcover : actualTime input.length ≤ target)
    (henvelope :
      SearchProgram.PrefixEnvelope
        regs kernel input target valueBits)
    (hcode :
      RAM.bitlen (SearchProgram.program regs kernel).codeSize ≤
        valueBits + 1)
    (hcount :
      RAM.bitlen
          (regs.footprint ∪ kernel.footprint).card ≤
        valueBits + 1)
    (haddresses :
      ∀ address ∈ regs.footprint ∪ kernel.footprint,
        RAM.bitlen address ≤ valueBits + 1) :
    ∃ final answer steps,
      InvariantRuns
          (SearchProgram.MutableValuesWithin
            (regs.footprint ∪ kernel.footprint) valueBits)
          (SearchProgram.program regs kernel)
          (RAM.initRegs input) final steps ∧
        SearchProgram.ProgramPost
          regs kernel input answer final ∧
        final regs.candidate ≤ target ∧
        RAM.run (SearchProgram.program regs kernel).compile steps
            (RAM.initCfg input) =
          { pc := (SearchProgram.program regs kernel).codeSize,
            regs := final } ∧
        RAM.Halted (SearchProgram.program regs kernel).compile
          (RAM.run (SearchProgram.program regs kernel).compile steps
            (RAM.initCfg input)) ∧
        RAM.RegisterStore.DenseOverlay.FixedRegisters.TraceBound
          (SearchProgram.program regs kernel).compile input steps
          (regs.footprint ∪ kernel.footprint).card
          (valueBits + 1) ∧
        (answer = true ↔ input ∈ L) ∧
        (answer = false ↔ input ∉ L) := by
  obtain ⟨targetAnswer, hreturns, _htrue, _hfalse⟩ :=
    CertifiedOutcome.KernelRefines.candidateReturns_complete
      tm L actualTime hdecides
      (NeighborhoodExecutableEvaluation.Residue.engineFamily tm order)
      kernel hrefines input target hcover
  obtain ⟨final, answer, steps, hrun, hpost, hupper⟩ :=
    SearchProgram.program_invariantRuns_bounded_candidate
      regs kernel input target valueBits targetAnswer htarget
      hreturns henvelope
  have htrace :=
    SearchProgram.traceBound_of_invariantRun regs kernel input
      valueBits steps hrun hcode hcount haddresses
  obtain ⟨cost, space, hexec⟩ :=
    InvariantRuns.toExecExists hrun
  have hcompiled :=
    Exec.compile_correct hexec
  have hrunCompiled :
      RAM.run (SearchProgram.program regs kernel).compile steps
          (RAM.initCfg input) =
        { pc := (SearchProgram.program regs kernel).codeSize,
          regs := final } := by
    simpa [RAM.initCfg] using hcompiled.1
  have hhalt :
      RAM.Halted (SearchProgram.program regs kernel).compile
        (RAM.run (SearchProgram.program regs kernel).compile steps
          (RAM.initCfg input)) := by
    simpa [RAM.initCfg] using Exec.compile_halted hexec
  have hsound :=
    programPost_sound tm L actualTime hdecides order regs kernel
      hrefines input answer final hpost
  exact ⟨final, answer, steps, hrun, hpost, hupper,
    hrunCompiled, hhalt, htrace, answer_true_iff hsound,
    answer_false_iff hsound⟩

theorem compiledCertifiedExecution_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines :
      CertifiedOutcome.KernelRefines kernel tm
        (NeighborhoodExecutableEvaluation.Residue.engineFamily
          tm order))
    (input : List Bool)
    (hkernelPrefix :
      ∀ candidate,
        input.length ≤ candidate →
        candidate ≤ max input.length (actualTime input.length) →
        ∀ prime guess,
          guess < kernel.guessCount candidate →
          kernel.prefixValueBits input candidate prime guess ≤
            CertifiedOutcome.controllerValueBits tm regs kernel
              (max input.length (actualTime input.length))) :
    ∃ final answer steps,
      InvariantRuns
          (SearchProgram.MutableValuesWithin
            (regs.footprint ∪ kernel.footprint)
            (CertifiedOutcome.controllerValueBits tm regs kernel
              (max input.length (actualTime input.length))))
          (SearchProgram.program regs kernel)
          (RAM.initRegs input) final steps ∧
        SearchProgram.ProgramPost
          regs kernel input answer final ∧
        final regs.candidate ≤
          max input.length (actualTime input.length) ∧
        RAM.run (SearchProgram.program regs kernel).compile steps
            (RAM.initCfg input) =
          { pc := (SearchProgram.program regs kernel).codeSize,
            regs := final } ∧
        RAM.Halted (SearchProgram.program regs kernel).compile
          (RAM.run (SearchProgram.program regs kernel).compile steps
            (RAM.initCfg input)) ∧
        RAM.RegisterStore.DenseOverlay.FixedRegisters.TraceBound
          (SearchProgram.program regs kernel).compile input steps
          (regs.footprint ∪ kernel.footprint).card
          (CertifiedOutcome.controllerValueBits tm regs kernel
              (max input.length (actualTime input.length)) + 1) ∧
        (answer = true ↔ input ∈ L) ∧
        (answer = false ↔ input ∉ L) := by
  let target := max input.length (actualTime input.length)
  let valueBits :=
    CertifiedOutcome.controllerValueBits tm regs kernel target
  have henvelope :
      SearchProgram.PrefixEnvelope
        regs kernel input target valueBits := by
    exact CertifiedOutcome.KernelRefines.prefixEnvelope
      tm
      (NeighborhoodExecutableEvaluation.Residue.engineFamily tm order)
      regs kernel hrefines input target (by
        dsimp only [target]
        exact le_max_left _ _) (by
          simpa [target, valueBits] using hkernelPrefix)
  apply compiledBoundedExecution_internal
    tm L actualTime hdecides order regs kernel hrefines
      input target valueBits
  · dsimp only [target]
    exact le_max_left _ _
  · dsimp only [target]
    exact le_max_right _ _
  · exact henvelope
  · exact (CertifiedOutcome.controller_codeSize_bitlen_le
      tm regs kernel target).trans (Nat.le_succ _)
  · exact (CertifiedOutcome.controller_footprintCard_bitlen_le
      tm regs kernel target).trans (Nat.le_succ _)
  · intro address haddress
    exact (CertifiedOutcome.controller_address_bitlen_le
      tm regs kernel target haddress).trans (Nat.le_succ _)

/-- The canonical dense-overlay execution carries exactly the same certified
halt, fixed-register trace bound, and public `R₀` verdict as the ordinary RAM
execution. -/
theorem compiledCertifiedDenseExecution_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines :
      CertifiedOutcome.KernelRefines kernel tm
        (NeighborhoodExecutableEvaluation.Residue.engineFamily
          tm order))
    (input : List Bool)
    (hkernelPrefix :
      ∀ candidate,
        input.length ≤ candidate →
        candidate ≤ max input.length (actualTime input.length) →
        ∀ prime guess,
          guess < kernel.guessCount candidate →
          kernel.prefixValueBits input candidate prime guess ≤
            CertifiedOutcome.controllerValueBits tm regs kernel
              (max input.length (actualTime input.length))) :
    ∃ fuel,
      let program := (SearchProgram.program regs kernel).compile
      let final :=
        (RAM.RegisterStore.DenseOverlay.Snapshot.initial input).run
          program input fuel
      final.Halted program ∧
        RAM.RegisterStore.DenseOverlay.FixedRegisters.TraceBound
          program input fuel
          (regs.footprint ∪ kernel.footprint).card
          (CertifiedOutcome.controllerValueBits tm regs kernel
              (max input.length (actualTime input.length)) + 1) ∧
        (input ∈ L →
          RAM.RegisterStore.DenseOverlay.read input final.overlay 0 = 1) ∧
        (input ∉ L →
          RAM.RegisterStore.DenseOverlay.read input final.overlay 0 = 0) := by
  obtain ⟨finalStore, answer, steps, _hinvariant, hpost, _hcandidate,
      hrun, hhalt, htrace, htrue, hfalse⟩ :=
    compiledCertifiedExecution_internal
      tm L actualTime hdecides order regs kernel hrefines input
        hkernelPrefix
  refine ⟨steps, ?_⟩
  dsimp only
  let program := (SearchProgram.program regs kernel).compile
  let denseFinal :=
    (RAM.RegisterStore.DenseOverlay.Snapshot.initial input).run
      program input steps
  change
    denseFinal.Halted program ∧
      RAM.RegisterStore.DenseOverlay.FixedRegisters.TraceBound
        program input steps
        (regs.footprint ∪ kernel.footprint).card
        (CertifiedOutcome.controllerValueBits tm regs kernel
            (max input.length (actualTime input.length)) + 1) ∧
      (input ∈ L →
        RAM.RegisterStore.DenseOverlay.read
          input denseFinal.overlay 0 = 1) ∧
      (input ∉ L →
        RAM.RegisterStore.DenseOverlay.read
          input denseFinal.overlay 0 = 0)
  have hdecode :
      denseFinal.decode input =
        RAM.run program steps (RAM.initCfg input) := by
    calc
      denseFinal.decode input =
          RAM.run program steps
            ((RAM.RegisterStore.DenseOverlay.Snapshot.initial input
              ).decode input) := by
        exact
          RAM.RegisterStore.DenseOverlay.Snapshot.decode_run
            program input steps
              (RAM.RegisterStore.DenseOverlay.Snapshot.initial input)
              (RAM.RegisterStore.DenseOverlay.Snapshot.initial_canonical
                input)
      _ = RAM.run program steps (RAM.initCfg input) := by
        rw [RAM.RegisterStore.DenseOverlay.Snapshot.initial_decode]
  have hdenseHalt : denseFinal.Halted program := by
    have hhalt' : RAM.Halted program
        (RAM.run program steps (RAM.initCfg input)) := by
      exact hhalt
    rw [← hdecode] at hhalt'
    simpa [RAM.Halted, RAM.curInstr,
      RAM.RegisterStore.DenseOverlay.Snapshot.Halted,
      RAM.RegisterStore.DenseOverlay.Snapshot.curInstr,
      RAM.RegisterStore.DenseOverlay.Snapshot.decode] using hhalt'
  have hread :
      RAM.RegisterStore.DenseOverlay.read input denseFinal.overlay 0 =
        (RAM.run program steps (RAM.initCfg input)).verdict := by
    rw [← hdecode]
    rfl
  have houtput :
      RAM.RegisterStore.DenseOverlay.read input denseFinal.overlay 0 =
        Input.bitValue answer := by
    calc
      RAM.RegisterStore.DenseOverlay.read input denseFinal.overlay 0 =
          (RAM.run program steps (RAM.initCfg input)).verdict :=
        hread
      _ = finalStore 0 := by
        rw [hrun]
        rfl
      _ = finalStore regs.inputLength := by
        exact congrArg finalStore regs.inputLength_zero.symm
      _ = Input.bitValue answer := hpost.output_eq
  refine ⟨hdenseHalt, htrace, ?_, ?_⟩
  · intro hmember
    rw [houtput, htrue.mpr hmember]
    simp [Input.bitValue]
  · intro hnotMember
    rw [houtput, hfalse.mpr hnotMember]
    simp [Input.bitValue]

theorem compiledDecidesInSpace_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (hrefines :
      CertifiedOutcome.KernelRefines kernel tm
        (NeighborhoodExecutableEvaluation.Residue.engineFamily
          tm order))
    (spaceBound : ℕ → ℕ)
    (hspace :
      ∀ input final steps cost space,
        Exec (SearchProgram.program regs kernel)
            (RAM.initRegs input) final steps cost space →
          space ≤ spaceBound input.length) :
    (SearchProgram.program regs kernel).compile.DecidesInSpace
      L spaceBound := by
  intro input
  obtain ⟨final, answer, steps, cost, space, hexec, hpost,
      hsound⟩ :=
    sourceExecution tm L actualTime hdecides order regs kernel
      hrefines input
  have hcompiled :=
    Exec.compile_correct hexec
  have hrun :
      RAM.run (SearchProgram.program regs kernel).compile steps
          (RAM.initCfg input) =
        { pc := (SearchProgram.program regs kernel).codeSize,
          regs := final } := by
    simpa [RAM.initCfg] using hcompiled.1
  have hhalt :
      RAM.Halted (SearchProgram.program regs kernel).compile
        (RAM.run (SearchProgram.program regs kernel).compile steps
          (RAM.initCfg input)) := by
    simpa [RAM.initCfg] using Exec.compile_halted hexec
  have houtput :
      (RAM.run (SearchProgram.program regs kernel).compile steps
          (RAM.initCfg input)).verdict =
        Input.bitValue answer := by
    rw [hrun]
    change final 0 = Input.bitValue answer
    rw [← regs.inputLength_zero]
    exact hpost.output_eq
  have htrue := answer_true_iff hsound
  have hfalse := answer_false_iff hsound
  refine ⟨steps, hhalt, ?_, ?_, ?_⟩
  · have hspaceEq :
        RAM.spaceUpto
            (SearchProgram.program regs kernel).compile steps
            (RAM.initCfg input) =
          space := by
        simpa [RAM.initCfg] using hcompiled.2.2
    rw [hspaceEq]
    exact hspace input final steps cost space hexec
  · intro hmember
    rw [houtput, htrue.mpr hmember]
    simp [Input.bitValue]
  · intro hnotMember
    rw [houtput, hfalse.mpr hnotMember]
    simp [Input.bitValue]

end Internal

end LanguageDecision

end Runtime

end TimeSpaceSimulation

end Complexity
