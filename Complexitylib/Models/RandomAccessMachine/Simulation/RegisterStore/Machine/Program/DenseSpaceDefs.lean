/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Containment.Defs
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Fixed
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseBoundsDefs

/-!
# Fixed-register dense-simulator space bounds

These definitions turn a bound on the serialized mutable overlay into one
fuel-independent budget for a complete simulated RAM iteration. The loop may
run for arbitrarily many iterations, but every iteration starts and ends at the
same twenty-tape ABI with all work heads at cell one.
-/

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- A uniform upper bound for the selected dense-step width when every decoded
RAM register has bit width at most `wordBits`. -/
def denseFixedStepWidth (program : Program) (wordBits : ℕ) : ℕ :=
  2 * programStaticWidth program + 4 * wordBits + 4

/-- All-prefix auxiliary-space budget for one body/test/rewind loop segment.
The leading cell pays for the canonical cell-one ABI at the segment boundary. -/
def denseFixedIterationSpace (program : Program) (inputLength entryBudget
    wordBits : ℕ) : ℕ :=
  1 +
    2000000000 * (programResourceMagnitude program + 1) ^ 2 *
      (DenseOverlay.FixedRegisters.codeBudget entryBudget wordBits +
        inputLength + denseFixedStepWidth program wordBits + 1) *
      (denseFixedStepWidth program wordBits + 1)

/-- All-prefix auxiliary-space budget for final lookup and verdict emission. -/
def denseFixedOutputSpace (inputLength entryBudget wordBits : ℕ) : ℕ :=
  1 + 2000000 *
    (DenseOverlay.FixedRegisters.codeBudget entryBudget wordBits +
      inputLength + 1)

/-- The exact standard-initializer runtime at one input length. This term is
used only to bound the uncharged output head during initialization; its value
is independent of the actual input bits. -/
def denseFixedInitOutputSpace (inputLength : ℕ) : ℕ :=
  denseProgramInitTime standardControlInstructionTapes
    (List.replicate inputLength false)

/-- Complete fixed-TM decision-space budget. It combines the sharp initializer
workspace, the initializer's output-head reserve, one local loop segment, and
the final verdict phase. No term grows with the number of loop iterations. -/
def denseProgramDecisionSpace (program : Program) (inputLength entryBudget
    wordBits : ℕ) : ℕ :=
  max (denseProgramInitSpace inputLength)
    (max (denseFixedInitOutputSpace inputLength)
      (max (denseFixedIterationSpace program inputLength entryBudget wordBits)
        (denseFixedOutputSpace inputLength entryBudget wordBits)))

end Machine
end RegisterStore
end RAM
end Complexity
