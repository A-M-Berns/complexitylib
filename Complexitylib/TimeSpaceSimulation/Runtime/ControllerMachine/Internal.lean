/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.ControllerMachine.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.LanguageDecision
import Complexitylib.TimeSpaceSimulation.Runtime.MachineSpace

/-!
# Concrete Turing machine generated from a Williams controller -- proofs
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace ControllerMachine

namespace Internal

/-- The certified controller run, re-expressed with the exact program,
footprint cardinality, and word-width functions consumed by the direct
fixed-register compiler. -/
theorem certifiedDenseExecution_internal
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
          RAM.RegisterStore.DenseOverlay.read input final.overlay 0 = 0) := by
  intro input
  simpa [program, spec, allowed, MachineSpace.controllerWordBits] using
    LanguageDecision.compiledCertifiedDenseExecution
      tm L actualTime hdecides order regs kernel hrefines input
        (hkernelPrefix input)

/-- The direct fixed-register compiler turns the certified dense controller
execution into a concrete multitape Turing-machine space bound. -/
theorem decidesInSpace_internal
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
      (space tm regs kernel actualTime) := by
  exact
    RAM.FixedRegisterMachine.programTM_decidesInSpace_traceBound
      (spec regs kernel) L
      (MachineSpace.controllerWordBits tm regs kernel actualTime)
      (certifiedDenseExecution_internal
        tm L actualTime hdecides order regs kernel
          hrefines hkernelPrefix)

theorem space_isBigO_internal
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    {actualTime T : ℕ → ℕ}
    (htime : actualTime =O T)
    (hT : ∀ n, n ≤ T n) :
    (space tm regs kernel actualTime) =O
      ComplexityBridge.sqrtLogSpace T := by
  exact
    MachineSpace.fixedRegisterSimulatorSpace_isBigO
      (spec regs kernel) tm regs kernel htime hT

end Internal

end ControllerMachine

end Runtime

end TimeSpaceSimulation

end Complexity
