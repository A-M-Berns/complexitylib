/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.ControllerMachine.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.ControllerMachine.Internal

/-!
# Concrete Turing machine generated from a Williams search controller

The generated machine and its exact space function are fixed once the source
machine's concrete trial kernel is fixed.  Its asymptotic space accounting is
already independent of the remaining semantic correctness proof.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace ControllerMachine

/-- Every input has a halted dense-overlay controller run satisfying the exact
fixed-register trace contract required by the direct Turing-machine
compiler. -/
theorem certifiedDenseExecution
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
    (hkernelPrefix :
      ∀ input candidate,
        input.length ≤ candidate →
        candidate ≤ max input.length (actualTime input.length) →
        ∀ prime guess,
          guess < kernel.guessCount candidate →
          kernel.prefixValueBits input candidate prime guess ≤
            CertifiedOutcome.controllerValueBits tm regs kernel
              (max input.length (actualTime input.length))) :
    ∀ input, ∃ fuel,
      let final :=
        (RAM.RegisterStore.DenseOverlay.Snapshot.initial input).run
          (program regs kernel) input fuel
      final.Halted (program regs kernel) ∧
        RAM.RegisterStore.DenseOverlay.FixedRegisters.TraceBound
          (program regs kernel) input fuel
          (spec regs kernel).allowed.card
          (MachineSpace.controllerWordBits
            tm regs kernel actualTime input.length) ∧
        (input ∈ L →
          RAM.RegisterStore.DenseOverlay.read input final.overlay 0 = 1) ∧
        (input ∉ L →
          RAM.RegisterStore.DenseOverlay.read input final.overlay 0 = 0) :=
  Internal.certifiedDenseExecution_internal
    tm L actualTime hdecides order regs kernel hrefines hkernelPrefix

/-- The generated direct-register Turing machine decides the source language
within the exact initialized instruction-space budget. -/
theorem decidesInSpace
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
    (hkernelPrefix :
      ∀ input candidate,
        input.length ≤ candidate →
        candidate ≤ max input.length (actualTime input.length) →
        ∀ prime guess,
          guess < kernel.guessCount candidate →
          kernel.prefixValueBits input candidate prime guess ≤
            CertifiedOutcome.controllerValueBits tm regs kernel
              (max input.length (actualTime input.length))) :
    (simulator regs kernel).DecidesInSpace L
      (space tm regs kernel actualTime) :=
  Internal.decidesInSpace_internal
    tm L actualTime hdecides order regs kernel hrefines hkernelPrefix

/-- The exact space function of the generated direct-register simulator is
square-root-logarithmic in every encompassing source time bound. -/
theorem space_isBigO
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    {actualTime T : ℕ → ℕ}
    (htime : actualTime =O T)
    (hT : ∀ n, n ≤ T n) :
    (space tm regs kernel actualTime) =O
      ComplexityBridge.sqrtLogSpace T :=
  Internal.space_isBigO_internal
    tm regs kernel htime hT

end ControllerMachine

end Runtime

end TimeSpaceSimulation

end Complexity
