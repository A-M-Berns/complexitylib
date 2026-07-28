/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.CertifiedOutcome
import Complexitylib.TimeSpaceSimulation.Runtime.MachineSpace.Defs

/-!
# Exact space budget for the fixed-register Williams simulator -- proofs
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace MachineSpace

namespace Internal

theorem initializeSpace_le_instructionSpace_internal
    {program : RAM.Program}
    (spec : RAM.FixedRegisterMachine.Spec program)
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (actualTime : ℕ → ℕ) (inputLength : ℕ) :
    RAM.FixedRegisterMachine.initializeSpace spec inputLength ≤
      RAM.FixedRegisterMachine.instructionSpace
        (controllerWordBits tm regs kernel actualTime inputLength) := by
  have hsize :
      inputLength.size ≤
        (max inputLength (actualTime inputLength)).size :=
    Nat.size_le_size (Nat.le_max_left _ _)
  have henvelope :=
    NeighborhoodGraph.WorkspaceAccounting.size_le_trialEnvelope
      tm.Q workTapeCount
      (max inputLength (actualTime inputLength))
  have hcontroller :
      NeighborhoodProgram.fixedRegisterCount *
            NeighborhoodGraph.WorkspaceAccounting.trialEnvelopeBits
              tm.Q workTapeCount
                (max inputLength (actualTime inputLength)) +
          2 ≤
        CertifiedOutcome.controllerValueBits tm regs kernel
          (max inputLength (actualTime inputLength)) :=
    le_max_right _ _
  simp only [RAM.FixedRegisterMachine.initializeSpace,
    TM.binaryLengthSpace,
    RAM.FixedRegisterMachine.instructionSpace, controllerWordBits]
  simp only [NeighborhoodProgram.fixedRegisterCount] at hcontroller
  omega

theorem fixedRegisterSimulatorSpace_eq_instructionSpace_internal
    {program : RAM.Program}
    (spec : RAM.FixedRegisterMachine.Spec program)
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (actualTime : ℕ → ℕ) (inputLength : ℕ) :
    fixedRegisterSimulatorSpace spec tm regs kernel actualTime inputLength =
      RAM.FixedRegisterMachine.instructionSpace
        (controllerWordBits tm regs kernel actualTime inputLength) := by
  rw [fixedRegisterSimulatorSpace, max_eq_right]
  exact initializeSpace_le_instructionSpace_internal
    spec tm regs kernel actualTime inputLength

private theorem constant_isBigO_sqrtLog_internal
    (constant : ℕ) {T : ℕ → ℕ}
    (hT : ∀ n, n ≤ T n) :
    (fun _ : ℕ => constant) =O
      ComplexityBridge.sqrtLogSpace T := by
  have hconstantRounded :
      (fun _ : ℕ => constant) =O
        ComplexityBridge.roundedSqrtLogSpace T := by
    have hle :
        ∀ n,
          constant ≤
            constant *
              ComplexityBridge.roundedSqrtLogSpace T n := by
      intro n
      have hpositive :
          1 ≤ ComplexityBridge.roundedSqrtLogSpace T n := by
        exact
          NeighborhoodGraph.WorkspaceAccounting.blockLength_pos
            (T n)
      simpa using Nat.mul_le_mul_left constant hpositive
    exact
      (BigO.of_le hle).trans
        (BigO.const_mul_left constant
          (BigO.refl
            (ComplexityBridge.roundedSqrtLogSpace T)))
  exact hconstantRounded.trans
    (ComplexityBridge.roundedSqrtLogSpace_isBigO hT)

theorem controllerWordBits_isBigO_internal
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    {actualTime T : ℕ → ℕ}
    (htime : actualTime =O T)
    (hT : ∀ n, n ≤ T n) :
    (controllerWordBits tm regs kernel actualTime) =O
      ComplexityBridge.sqrtLogSpace T := by
  simpa [controllerWordBits] using
    CertifiedOutcome.controllerTraceBits_max_actualTime_isBigO
      tm regs kernel htime hT

theorem fixedRegisterSimulatorSpace_isBigO_internal
    {program : RAM.Program}
    (spec : RAM.FixedRegisterMachine.Spec program)
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    {actualTime T : ℕ → ℕ}
    (htime : actualTime =O T)
    (hT : ∀ n, n ≤ T n) :
    (fixedRegisterSimulatorSpace spec tm regs kernel actualTime) =O
      ComplexityBridge.sqrtLogSpace T := by
  have hword :
      (controllerWordBits tm regs kernel actualTime) =O
        ComplexityBridge.sqrtLogSpace T :=
    controllerWordBits_isBigO_internal
      tm regs kernel htime hT
  have hone :
      (fun _ : ℕ => 1) =O
        ComplexityBridge.sqrtLogSpace T :=
    constant_isBigO_sqrtLog_internal 1 hT
  have hphase :
      (fun n =>
        RAM.FixedRegisterMachine.instructionSpace
          (controllerWordBits tm regs kernel actualTime n)) =O
        ComplexityBridge.sqrtLogSpace T := by
    simpa [RAM.FixedRegisterMachine.instructionSpace] using
      BigO.const_mul_left 1000 (BigO.add hword hone)
  have heq :
      fixedRegisterSimulatorSpace spec tm regs kernel actualTime =
        fun n =>
          RAM.FixedRegisterMachine.instructionSpace
            (controllerWordBits tm regs kernel actualTime n) := by
    funext n
    exact
      fixedRegisterSimulatorSpace_eq_instructionSpace_internal
        spec tm regs kernel actualTime n
  rw [heq]
  exact hphase

end Internal

end MachineSpace

end Runtime

end TimeSpaceSimulation

end Complexity
