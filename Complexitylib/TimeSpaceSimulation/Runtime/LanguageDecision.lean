/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.LanguageDecision.Internal

/-!
# Source-language correctness of the compiled outer search

This module closes the semantic boundary between the exact neighborhood
engine and the first-order outer controller.  Any executable trial kernel
refining the residue engine family makes the compiled controller halt on every
input and publish exactly the source Turing machine's Boolean decision.

The unconditional theorem is semantic.  The bounded theorem separately names
the prefix envelope and fixed code/address obligations consumed by the dense
RAM compiler.  A final theorem packages ordinary `RAM.Program.DecidesInSpace`
only when the caller supplies an ordinary source-store space bound; semantic
refinement alone intentionally makes no such resource claim.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace LanguageDecision

open RAM Structured

/-- Every refining concrete trial kernel makes the compiled outer controller
halt and return the exact source-language Boolean on every input. -/
theorem compiledHaltsWithLanguageVerdict
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
      (answer = false ↔ input ∉ L) :=
  Internal.compiledHaltsWithLanguageVerdict_internal
    tm L actualTime hdecides order regs kernel hrefines

/-- Resource-explicit bounded form of the semantic bridge.  The result keeps
the source invariant run, compiled halting state, and dense-overlay trace
certificate synchronized at one exact step count. -/
theorem compiledBoundedExecution
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
        (answer = false ↔ input ∉ L) :=
  Internal.compiledBoundedExecution_internal
    tm L actualTime hdecides order regs kernel hrefines input target
      valueBits htarget hcover henvelope hcode hcount haddresses

/-- Canonical bounded execution at the first proof-level endpoint guaranteed
to cover the source run. Cache, prime search, guess width, code size,
footprint cardinality, and fixed addresses are discharged automatically; the
only remaining resource premise is the concrete trial kernel's own
all-prefix value bound. -/
theorem compiledCertifiedExecution
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
        (answer = false ↔ input ∉ L) :=
  Internal.compiledCertifiedExecution_internal
    tm L actualTime hdecides order regs kernel hrefines input
      hkernelPrefix

/-- Re-express the canonical certified execution directly in the dense
snapshot semantics consumed by the fixed-register Turing-machine compiler. -/
theorem compiledCertifiedDenseExecution
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
          RAM.RegisterStore.DenseOverlay.read input final.overlay 0 = 0) :=
  Internal.compiledCertifiedDenseExecution_internal
    tm L actualTime hdecides order regs kernel hrefines input
      hkernelPrefix

/-- Package the semantic bridge as ordinary RAM space decision whenever the
caller supplies an ordinary source-store `Exec` space bound.  This premise is
kept explicit because the dense-overlay envelope is accounted by the later
Turing-machine compiler rather than by `RAM.Cfg.space`. -/
theorem compiledDecidesInSpace
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
      L spaceBound :=
  Internal.compiledDecidesInSpace_internal
    tm L actualTime hdecides order regs kernel hrefines spaceBound
      hspace

end LanguageDecision

end Runtime

end TimeSpaceSimulation

end Complexity
