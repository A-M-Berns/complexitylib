/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalStep.Defs

/-!
# Runtime-length traces on packed local configurations

This definitions layer iterates the fixed-source packed transition command.
The caller places the runtime step count in the range driver's count cell.
Each iteration performs one packed source step and decrements that cell.

The eventual packed computation kernel stores the caller's immutable count
above the local-configuration digits before entering this loop, then restores
it after consuming the represented configuration. This lets the trace use the
existing count cell without allocating another live scratch register.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedLocalTrace

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- One source transition followed by a decrement of the runtime step count. -/
def body
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (PackedLocalStep.step tm order controller regs)
    (.basic
      (.sub (CombineValue.rangeRegisters regs).count
        (CombineValue.rangeRegisters regs).count
        (CombineValue.rangeRegisters regs).one))

/-- Execute exactly the number of packed transitions stored in the count cell. -/
def trace
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  .whileNonzero (CombineValue.rangeRegisters regs).count
    (body tm order controller regs)

/-- Stable live context of a completed packed local trace.

The count cell is intentionally absent: it is the loop counter and equals zero
on exit. -/
structure PreservesContext
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- Current assignment code is preserved. -/
  assignment_eq :
    final (CombineValue.rangeRegisters regs).remaining =
      initial (CombineValue.rangeRegisters regs).remaining
  /-- Outer modular-sum accumulator is restored exactly. -/
  accumulator_eq :
    final (CombineValue.rangeRegisters regs).accumulator =
      initial (CombineValue.rangeRegisters regs).accumulator
  /-- The range driver's canonical one cell is restored exactly. -/
  one_eq :
    final (CombineValue.rangeRegisters regs).one =
      initial (CombineValue.rangeRegisters regs).one
  /-- Packed catalytic bank word is untouched. -/
  catalyticWord_eq :
    final regs.layout.bank = initial regs.layout.bank
  /-- Stable parameter and active-frame ABI fields are preserved. -/
  abi : ControlDecode.PreservesABI regs initial final

/-- Exact semantic endpoint of a runtime-length packed local trace. -/
structure Post
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (centers : TapeIndex workTapeCount → ℕ)
    (finalCfg : Cfg workTapeCount tm.Q)
    (suffix : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- The packed word represents the exact frozen trace endpoint. -/
  represents :
    PackedLocalRepresentation.Represents
      tm order blockLength centers finalCfg suffix
        (final (PackedLocalStep.bankRegisters regs).word)
  /-- The runtime step counter has been exhausted. -/
  count_eq :
    final (CombineValue.rangeRegisters regs).count = 0
  /-- Live caller state other than the consumed counter is preserved. -/
  context : PreservesContext regs initial final
  /-- Every address outside the exact packed-step footprint is preserved. -/
  eq_outside :
    ∀ address, address ∉ PackedLocalStep.footprint regs →
      final address = initial address

end PackedLocalTrace
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
