/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.CombineBranch.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.PackedComputationKernel.Defs

/-!
# Fixed computation-chunk provider

This layer wraps the packed local-transition factor and the fixed
tensor-basis factor in the complete Boolean-assignment range fold required
for one grouped computation-node output.

The number of assignments varies with the runtime candidate. The fixed
source therefore reconstructs it as
`chunkRadix ^ (bankDigitCount - chunkCount)` before starting the fold.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ComputationChunkKernel

open RAM Structured
open TreeEval CookMertz

variable {controller : SearchProgram.Registers}

/-- Shared outer assignment-range interface. -/
abbrev rangeRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    CombineValue.RangeRegisters :=
  CombineValue.rangeRegisters regs

/-- Scratch exponent used to reconstruct the immutable assignment count
after one packed-factor invocation. -/
abbrev countExponent
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 9

/-- Exact mutable allowance for the chunk provider: ordinary combine
scratch plus the controller constant cell used as a temporary bank save. -/
def footprint
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  CombineValue.combineScratchFootprint regs ∪ {controller.one}

/-- Number of grouped Boolean input digits in one complete assignment. -/
def assignmentDigitCount
    {tm : TM workTapeCount}
    (instanceData : NeighborhoodProgram.ResidueInstance tm) : ℕ :=
  NeighborhoodExecutableEvaluation.graphFanIn workTapeCount *
    PrimeGrouped.Logarithmic.chunkCount
      (NeighborhoodExecutableEvaluation.payloadWidth
        tm instanceData.blockLength)
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)

/-- Exact packed computation representation together with the immutable
cardinality of its surrounding Boolean-assignment range. -/
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
  /-- Active-frame, movement-code, output-cursor, and bank representation. -/
  packed :
    PackedComputationKernel.Context regs instanceData frame tape slot
      interval logicalBank code outputChunk store
  /-- The range count is the complete Boolean-assignment cardinality. -/
  count_eq :
    store (rangeRegisters regs).count =
      CombineValue.assignmentCount
        (NeighborhoodExecutableEvaluation.payloadWidth
          tm instanceData.blockLength)
        (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)

/-- Assignment-term context including the controller constant temporarily
used to save and restore the exact catalytic-bank word. -/
structure TermContext
    {tm : TM workTapeCount}
    (controller : SearchProgram.Registers)
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
    (stackWord bankWord : ℕ)
    (store : Store) : Prop where
  /-- Packed computation and canonical assignment-count representation. -/
  context :
    Context regs instanceData frame tape slot interval logicalBank code
      outputChunk store
  /-- The controller constant is available as a reversible save cell. -/
  controllerOne_eq : store controller.one = 1
  /-- The suspended scheduler continuation has its fixed incoming word. -/
  stack_eq :
    store (Layout.frameStackRegisters regs).word = stackWord
  /-- The catalytic bank has its fixed incoming packed word. -/
  bank_eq : store regs.layout.bank = bankWord

/-- One repeated multiplication while constructing the assignment count. -/
def countBody
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (.basic
      (.mul (rangeRegisters regs).count
        (rangeRegisters regs).count (Layout.chunkRadix regs)))
    (.basic
      (.sub (rangeRegisters regs).remaining
        (rangeRegisters regs).remaining (rangeRegisters regs).one))

/-- Reconstruct the number of Boolean chunk assignments from runtime
parameters using fixed source syntax. -/
def initializeAssignmentCount
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [CombineTerm.copy (rangeRegisters regs).remaining
      (Layout.bankDigitCount regs),
      .basic
        (.sub (rangeRegisters regs).remaining
          (rangeRegisters regs).remaining (Layout.chunkCount regs)),
      .basic (.imm (rangeRegisters regs).count 1),
      .basic (.imm (rangeRegisters regs).one 1),
      .whileNonzero (rangeRegisters regs).remaining (countBody regs)]

/-- One repeated multiplication while restoring the assignment count after
the packed kernel has used that register as its continuation suffix. -/
def restoreCountBody
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (.basic
      (.mul (rangeRegisters regs).count
        (rangeRegisters regs).count (Layout.chunkRadix regs)))
    (.basic
      (.sub (countExponent regs) (countExponent regs)
        (rangeRegisters regs).one))

/-- Reconstruct the immutable assignment count without disturbing the live
assignment index or packed factor. -/
def restoreAssignmentCount
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [CombineTerm.copy (countExponent regs)
      (Layout.bankDigitCount regs),
      .basic
        (.sub (countExponent regs) (countExponent regs)
          (Layout.chunkCount regs)),
      .basic (.imm (rangeRegisters regs).count 1),
      .whileNonzero (countExponent regs) (restoreCountBody regs)]

/-- Stack-safe packed factor command.

The packed local word aliases the scheduler continuation word. Save that word
as the packed kernel's high-order suffix, run the factor computation, then
reconstruct the outer assignment count in its immutable range cell.
-/
def stackSafePacked
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [CombineTerm.copy (rangeRegisters regs).count
      (Layout.frameStackRegisters regs).word,
      PackedComputationKernel.command tm order controller regs,
      restoreAssignmentCount regs]

/-- Contextual packed-factor contract that additionally exposes exact
restoration of the aliased continuation word. -/
def StackSafePackedSpecAt
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
    store (rangeRegisters regs).remaining = assignment →
    store (rangeRegisters regs).modulus =
      NeighborhoodScheduler.fieldModulus instanceData →
    store (rangeRegisters regs).modulusPred =
      NeighborhoodScheduler.fieldModulus instanceData - 1 →
    store (rangeRegisters regs).one = 1 →
    ∃ final,
      Runs (stackSafePacked tm order controller regs) store final ∧
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
      final (Layout.frameStackRegisters regs).word =
        store (Layout.frameStackRegisters regs).word ∧
      final regs.layout.bank = store regs.layout.bank ∧
      Context regs instanceData frame tape slot interval logicalBank code
        outputChunk final

/-- Preserve the continuation while the tensor-basis kernel uses its
physical word cell as the basis-factor output. -/
def saveContinuation
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  CombineTerm.copy (rangeRegisters regs).count
    (Layout.frameStackRegisters regs).word

/-- Save the exact catalytic-bank word in the disjoint controller constant
cell while the basis kernel performs destructive packed reads. -/
def saveBank
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  CombineTerm.copy controller.one regs.layout.bank

/-- Move the basis factor out of the aliased continuation word. -/
def saveBasisFactor
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  CombineTerm.copy (rangeRegisters regs).term
    (CombineTerm.basisValue regs)

/-- Restore the saved continuation word from the range count cell. -/
def restoreContinuation
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  CombineTerm.copy (Layout.frameStackRegisters regs).word
    (rangeRegisters regs).count

/-- Restore the exact catalytic-bank word after tensor-basis evaluation. -/
def restoreBank
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  CombineTerm.copy regs.layout.bank controller.one

/-- Re-establish the controller's persistent constant after using its cell
as a temporary exact bank save. -/
def restoreControllerOne
    (controller : SearchProgram.Registers) : Cmd :=
  .basic (.imm controller.one 1)

/-- Multiply the two factors modulo the runtime field. The basis factor
aliases the result cell, which modular multiplication permits. -/
def multiplyFactors
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  RuntimeArithmetic.mulMod (CombineTerm.termReduceRegisters regs)
    (CombineTerm.packedValue regs) (rangeRegisters regs).term

/-- Fixed packed and tensor-basis term command with exact continuation and
assignment-count restoration. -/
def assignmentTerm
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [stackSafePacked tm order controller regs,
      saveBank controller regs,
      saveContinuation regs,
      CombineTerm.computationBasisKernel workTapeCount regs,
      saveBasisFactor regs,
      restoreContinuation regs,
      restoreBank controller regs,
      restoreControllerOne controller,
      restoreAssignmentCount regs,
      multiplyFactors regs]

/-- Full fixed provider for one runtime-selected grouped output chunk. -/
def command
    (tm : TM workTapeCount)
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [initializeAssignmentCount regs,
      CombineValue.rangeFold .add (rangeRegisters regs)
        (assignmentTerm tm order controller regs),
      CombineTerm.copy (CombineBranch.chunkValue regs)
        (rangeRegisters regs).accumulator]

/-- Correctness contract of the complete fixed computation-chunk provider
at one represented frame, movement code, and grouped output coordinate. -/
def SpecAt
    {tm : TM workTapeCount}
    (order :
      NeighborhoodExecutableEvaluation.FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
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
  ∀ store,
    PackedComputationKernel.Context regs instanceData frame tape slot
        interval logicalBank code outputChunk store →
    store controller.one = 1 →
    ∃ final,
      Runs (command tm order controller regs) store final ∧
      CombineBranch.ChunkPost regs
        (NeighborhoodExecutableEvaluation.Residue.evaluateNode
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount)
          (GuessedLocalEvaluation.booleanCombineAtGuess
            tm instanceData.blockLength instanceData.encoding
            instanceData.positive instanceData.guess interval tape slot)
          (CombineTerm.computationArguments frame logicalBank)
          outputChunk)
        outputChunk.val store final

end ComputationChunkKernel
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
