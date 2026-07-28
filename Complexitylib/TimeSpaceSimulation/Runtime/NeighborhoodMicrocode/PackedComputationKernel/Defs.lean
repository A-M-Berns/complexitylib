/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.GuessedCombineSpec.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalInitialization.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalOutputChunk.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedLocalTrace.Defs

/-!
# Fixed packed computation-factor kernel

This definitions layer composes packed local initialization, a runtime-length
source trace, and grouped output extraction into one fixed command.

The outer assignment count is stored above the local-configuration digits.
After output extraction, a runtime-counted sequence of packed pops removes the
local prefix and recovers that suspended count. The grouped output is saved
across the destructive division loop and restored to the packed-factor cell.

The exact contextual contract records the two runtime inputs that the generic
combine-factor scaffold cannot infer from the active frame alone:

* the persistent outer movement-code register represents `instanceData.guess`;
* `Layout.active` is the grouped output chunk requested by the surrounding
  chunk stream.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace PackedComputationKernel

open RAM Structured
open TreeEval CookMertz

variable {controller : SearchProgram.Registers}

/-- Reuse the collision-free packed local-word interface. -/
abbrev bankRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    NeighborhoodProgram.BankRegisters :=
  PackedLocalStep.bankRegisters regs

/-- Stack view whose word is the transient packed local configuration. -/
abbrev stackRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    NeighborhoodProgram.StackRegisters :=
  (bankRegisters regs).mainStack

/-- Packed Boolean factor saved while the local word is divided back to its
suspended high-order suffix. -/
abbrev savedPacked
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  (CombineValue.rangeRegisters regs).term

/-- The typed movement code canonically stored by one runtime instance. -/
def guessCode
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    Fin
      (3 ^
        NeighborhoodGraph.Guess.Enumeration.movementCount
          workTapeCount instanceData.horizon) :=
  Fin.cast
    (by
      simp [NeighborhoodGraph.Guess.Search.guessCount])
    (⟨instanceData.guessCode, instanceData.guessCode_lt⟩ :
      Fin
        (NeighborhoodGraph.Guess.Search.guessCount
          workTapeCount instanceData.horizon))

/-- Save the immutable outer assignment count as the packed-word suffix. -/
def saveSuffix
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  CombineTerm.copy (bankRegisters regs).word
    (CombineValue.rangeRegisters regs).count

/-- Install the runtime source-step count after local initialization. -/
def installTraceCount
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  CombineTerm.copy (CombineValue.rangeRegisters regs).count
    (Layout.blockLength regs)

/-- Preserve the grouped output while packed division reuses its physical
test cell. -/
def savePackedValue
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  CombineTerm.copy (savedPacked regs) (CombineTerm.packedValue regs)

/-- Initialize the runtime local-digit count and packed-division constants. -/
def initializeDrop
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := bankRegisters regs
  let range := CombineValue.rangeRegisters regs
  Cmd.basics
    [.imm bank.value ((workTapeCount + 2) * 3),
      .mul range.count bank.value (Layout.blockLength regs),
      .imm bank.value 1,
      .add range.count range.count bank.value,
      .imm bank.base (PackedLocalConfiguration.radix tm),
      .imm bank.basePred (PackedLocalConfiguration.radix tm - 1),
      .imm bank.one 1]

/-- Remove one low-order local digit and decrement the runtime prefix count. -/
def dropBody
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (NeighborhoodProgram.pop (stackRegisters regs))
    (.basic
      (.sub (CombineValue.rangeRegisters regs).count
        (CombineValue.rangeRegisters regs).count
        (CombineValue.rangeRegisters regs).one))

/-- Remove exactly the runtime number of local-configuration digits. -/
def dropPrefix
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  .whileNonzero (CombineValue.rangeRegisters regs).count
    (dropBody regs)

/-- Restore the suspended assignment count from the divided packed word. -/
def restoreCount
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  CombineTerm.copy (CombineValue.rangeRegisters regs).count
    (bankRegisters regs).word

/-- Restore the grouped Boolean factor after packed division. -/
def restorePackedValue
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  CombineTerm.copy (CombineTerm.packedValue regs) (savedPacked regs)

/-- Consume the represented local word, recover the suspended count, and
restore the saved grouped factor. -/
def finish
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [savePackedValue regs,
      initializeDrop tm regs,
      dropPrefix regs,
      restoreCount regs,
      restorePackedValue regs,
      PackedLocalOutputChunk.restoreRangeOne regs]

/-- One fixed-source packed computation-factor command.

The source depends only on the simulated machine, its fixed state order, and
the two fixed register allocations. Candidate time, block length, movement
guess, interval, assignment, and output chunk remain runtime data.
-/
def command
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [saveSuffix regs,
      PackedLocalInitialization.build tm order controller regs,
      installTraceCount regs,
      PackedLocalTrace.trace tm order controller regs,
      PackedLocalOutputChunk.build tm controller regs,
      finish tm regs]

/-- Exact fixed mutable footprint of the complete packed factor command. -/
abbrev footprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  PackedLocalStep.footprint regs

/-- Runtime representation required by one packed-factor invocation. -/
structure Context
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : Fin instanceData.horizon)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)))
    (store : Store) : Prop where
  /-- Stable active-frame and catalytic-bank representation. -/
  computation :
    CombineTerm.ComputationFrameContext regs instanceData frame tape slot
      interval.val logicalBank store
  /-- The persistent outer movement counter is this instance's exact code. -/
  guess_eq : store controller.guess = code.val
  /-- The surrounding chunk stream supplies the requested output coordinate. -/
  cursor_eq : store (Layout.active regs) = outputChunk.val

/-- Correctness contract of the fixed packed factor at one runtime
computation frame and grouped output coordinate. -/
def SpecAt
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : Fin instanceData.horizon)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (outputChunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))) :
    Prop :=
  ∀ (store : Store) (assignment : ℕ),
    Context regs instanceData frame tape slot interval logicalBank code
      outputChunk store →
    store (CombineValue.rangeRegisters regs).remaining = assignment →
    store (CombineValue.rangeRegisters regs).modulus =
      NeighborhoodScheduler.fieldModulus instanceData →
    store (CombineValue.rangeRegisters regs).modulusPred =
      NeighborhoodScheduler.fieldModulus instanceData - 1 →
    store (CombineValue.rangeRegisters regs).one = 1 →
    ∃ final,
      Runs (command tm order controller regs) store final ∧
      CombineTerm.PackedPost regs
        (CombineTerm.packedAssignmentValue
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
          (GuessedLocalEvaluation.booleanCombineAtGuess
            tm instanceData.blockLength instanceData.encoding
            instanceData.positive instanceData.guess interval tape slot)
          outputChunk assignment)
        assignment store final ∧
      final (bankRegisters regs).word =
        store (CombineValue.rangeRegisters regs).count ∧
      Context regs instanceData frame tape slot interval logicalBank code
        outputChunk final

end PackedComputationKernel
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
