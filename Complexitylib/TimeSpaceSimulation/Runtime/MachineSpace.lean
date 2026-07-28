/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.Runtime.MachineSpace.Internal

/-!
# Exact space budget for the fixed-register Williams simulator

The direct fixed-register compiler's initialization is absorbed pointwise by
the execution budget.  The resulting whole-machine space function inherits
the controller's square-root-logarithmic asymptotic bound.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace MachineSpace

/-- Input-length initialization is pointwise absorbed by the direct
instruction-simulation budget. -/
theorem initializeSpace_le_instructionSpace
    {program : RAM.Program}
    (spec : RAM.FixedRegisterMachine.Spec program)
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (actualTime : ℕ → ℕ) (inputLength : ℕ) :
    RAM.FixedRegisterMachine.initializeSpace spec inputLength ≤
      RAM.FixedRegisterMachine.instructionSpace
        (controllerWordBits tm regs kernel actualTime inputLength) :=
  Internal.initializeSpace_le_instructionSpace_internal
    spec tm regs kernel actualTime inputLength

/-- The maximum joining initialization and execution simplifies to the
execution phase budget. -/
theorem fixedRegisterSimulatorSpace_eq_instructionSpace
    {program : RAM.Program}
    (spec : RAM.FixedRegisterMachine.Spec program)
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (actualTime : ℕ → ℕ) (inputLength : ℕ) :
    fixedRegisterSimulatorSpace spec tm regs kernel actualTime inputLength =
      RAM.FixedRegisterMachine.instructionSpace
        (controllerWordBits tm regs kernel actualTime inputLength) :=
  Internal.fixedRegisterSimulatorSpace_eq_instructionSpace_internal
    spec tm regs kernel actualTime inputLength

/-- The dense-overlay word width supplied to the direct compiler is
square-root-logarithmic. -/
theorem controllerWordBits_isBigO
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    {actualTime T : ℕ → ℕ}
    (htime : actualTime =O T)
    (hT : ∀ n, n ≤ T n) :
    (controllerWordBits tm regs kernel actualTime) =O
      ComplexityBridge.sqrtLogSpace T :=
  Internal.controllerWordBits_isBigO_internal
    tm regs kernel htime hT

/-- The complete initialized direct-register simulator has the advertised
square-root-logarithmic asymptotic space bound. -/
theorem fixedRegisterSimulatorSpace_isBigO
    {program : RAM.Program}
    (spec : RAM.FixedRegisterMachine.Spec program)
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    {actualTime T : ℕ → ℕ}
    (htime : actualTime =O T)
    (hT : ∀ n, n ≤ T n) :
    (fixedRegisterSimulatorSpace spec tm regs kernel actualTime) =O
      ComplexityBridge.sqrtLogSpace T :=
  Internal.fixedRegisterSimulatorSpace_isBigO_internal
    spec tm regs kernel htime hT

end MachineSpace

end Runtime

end TimeSpaceSimulation

end Complexity
