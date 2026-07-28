/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.FixedRegisterMachine
import Complexitylib.TimeSpaceSimulation.Runtime.MachineSpace.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.SearchProgram

/-!
# Concrete Turing machine generated from a Williams search controller

This definitions layer fixes the exact direct-register compiler
specialization used by the final simulation.  The compiler infers its finite
register prefix from the verified controller footprint and hardwired program
operands.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace Runtime

namespace ControllerMachine

open RAM

/-- Compiled first-order RAM program of the complete search controller. -/
def program
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs) :
    RAM.Program :=
  (SearchProgram.program regs kernel).compile

/-- Exact finite mutable footprint of the complete search controller. -/
def allowed
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs) :
    Finset ℕ :=
  regs.footprint ∪ kernel.footprint

/-- Automatically inferred direct-register compiler specification for the
complete controller. -/
noncomputable def spec
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs) :
    RAM.FixedRegisterMachine.Spec (program regs kernel) :=
  RAM.FixedRegisterMachine.Spec.ofFootprint
    (allowed regs kernel)
    (SearchProgram.zero_mem_footprint regs kernel)
    (SearchProgram.compiledWritesWithin regs kernel)

/-- Fixed multitape Turing machine generated from one concrete trial kernel. -/
noncomputable def simulator
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs) :
    TM (RAM.FixedRegisterMachine.workTapeCount (spec regs kernel)) :=
  RAM.FixedRegisterMachine.programTM (spec regs kernel)

/-- Exact all-prefix space function advertised for the generated simulator. -/
noncomputable def space
    (tm : TM workTapeCount)
    (regs : SearchProgram.Registers)
    (kernel : SearchProgram.TrialKernel regs)
    (actualTime : ℕ → ℕ) :
    ℕ → ℕ :=
  MachineSpace.fixedRegisterSimulatorSpace
    (spec regs kernel) tm regs kernel actualTime

end ControllerMachine

end Runtime

end TimeSpaceSimulation

end Complexity
