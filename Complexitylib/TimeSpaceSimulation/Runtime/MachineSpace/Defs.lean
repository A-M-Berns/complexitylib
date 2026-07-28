/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.FixedRegisterMachine.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.CertifiedOutcome.Defs

/-!
# Exact space budget for the fixed-register Williams simulator

This definitions layer joins the controller's dense-trace word width to the
direct fixed-register RAM compiler.  Initialization first counts the public
input length.  The execution phase then uses a fixed constant times the
largest represented RAM word.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace MachineSpace

/-- Dense-overlay word width supplied to the direct fixed-register compiler. -/
def controllerWordBits
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (actualTime : ℕ → ℕ) (inputLength : ℕ) : ℕ :=
  CertifiedOutcome.controllerValueBits tm regs kernel
      (max inputLength (actualTime inputLength)) +
    1

/-- Exact all-prefix space budget of the initialized direct-register
simulator. -/
def fixedRegisterSimulatorSpace
    {program : RAM.Program}
    (spec : RAM.FixedRegisterMachine.Spec program)
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (actualTime : ℕ → ℕ) (inputLength : ℕ) : ℕ :=
  max
    (RAM.FixedRegisterMachine.initializeSpace spec inputLength)
    (RAM.FixedRegisterMachine.instructionSpace
      (controllerWordBits tm regs kernel actualTime inputLength))

end MachineSpace

end Runtime

end TimeSpaceSimulation

end Complexity
