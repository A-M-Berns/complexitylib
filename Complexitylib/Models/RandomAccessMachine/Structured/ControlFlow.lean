/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Structured.ControlFlow.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.ControlFlow.Internal

/-!
# Control-flow bounds for structured RAM programs

All absolute jumps emitted by the structured compiler stay inside the compiled
command, whose terminal boundary contains the appended halt instruction.
Consequently every prefix of a compiled execution has a program counter bounded
by the source command's fixed code size.
-/

namespace Complexity

namespace RAM

namespace Structured

namespace ControlFlow

/-- One RAM step preserves a closed control-flow boundary. -/
theorem step_pc_le
    {program : Program} {bound : ℕ} {cfg : Cfg}
    (htargets : ProgramTargetsWithin program bound)
    (hboundary : BoundaryHalts program bound)
    (hpc : cfg.pc ≤ bound) :
    (RAM.step program cfg).pc ≤ bound :=
  Internal.step_pc_le_internal htargets hboundary hpc

/-- Every prefix of a closed RAM execution stays inside its boundary. -/
theorem run_pc_le
    {program : Program} {bound fuel : ℕ} {cfg : Cfg}
    (htargets : ProgramTargetsWithin program bound)
    (hboundary : BoundaryHalts program bound)
    (hpc : cfg.pc ≤ bound) :
    (RAM.run program fuel cfg).pc ≤ bound :=
  Internal.run_pc_le_internal htargets hboundary hpc

/-- Every absolute jump emitted by a structured command stays within its code
boundary. -/
theorem Cmd.compile_targetsWithin (cmd : Cmd) :
    ProgramTargetsWithin cmd.compile cmd.codeSize :=
  Internal.Cmd.compile_targetsWithin_internal cmd

/-- The code boundary of a closed structured compilation contains its appended
halt instruction. -/
theorem Cmd.compile_boundaryHalts (cmd : Cmd) :
    BoundaryHalts cmd.compile cmd.codeSize :=
  Internal.Cmd.compile_boundaryHalts_internal cmd

/-- Every prefix of a compiled structured execution has a program counter at
most the fixed source-code size. -/
theorem Cmd.run_compile_pc_le
    (cmd : Cmd) (initial : Store) (fuel : ℕ) :
    (RAM.run cmd.compile fuel { pc := 0, regs := initial }).pc ≤
      cmd.codeSize :=
  Internal.Cmd.run_compile_pc_le_internal cmd initial fuel

end ControlFlow

end Structured

end RAM

end Complexity
