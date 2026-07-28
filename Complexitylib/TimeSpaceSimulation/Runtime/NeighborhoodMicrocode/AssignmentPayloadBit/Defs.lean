/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentBit.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.AssignmentCodeSemantics.Defs

/-!
# Uniform semantic payload-bit lookup

The grouped assignment code is streamed at runtime, as are its chunk count
and the requested semantic payload position. A child coordinate is fixed in
the command source. This module recovers `chunkBits` from the preserved radix
`2 ^ chunkBits`, computes the exact low-order binary index, and invokes the
uniform assignment-bit reader.

The recovery stack deliberately avoids the live assignment code, immutable
assignment count, payload-position cell, continuation word, and catalytic
bank word.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace AssignmentPayloadBit

open RAM Structured
open TreeEval CookMertz
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

/-- Seven-register division view used only to recover the exponent of the
runtime power-of-two chunk radix. -/
def exponentStackMap : Fin 7 → Fin 34 :=
  ![0, 1, 4, 5, 9, 11, 12]

theorem exponentStackMap_injective :
    Function.Injective exponentStackMap := by
  decide

/-- Collision-free stack registers for repeated division by two. -/
def exponentStackRegisters
    (regs : NeighborhoodTrial.Registers controller) :
    NeighborhoodProgram.StackRegisters where
  index := fun slot => regs.index (exponentStackMap slot)
  injective := regs.injective.comp exponentStackMap_injective

/-- Recovered runtime value of `chunkBits`. The assignment-bit reader later
reuses this cell as its destructive digit cursor. -/
abbrev recoveredChunkBits
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 20

/-- Runtime semantic payload coordinate. This cell is read-only throughout
payload-bit lookup. -/
abbrev payloadPosition
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  Layout.codecScratch regs

/-- Scratch used while recovering the exponent of `Layout.chunkRadix`. -/
def recoveryFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  (exponentStackRegisters regs).footprint ∪
    {recoveredChunkBits regs}

/-- Complete advertised write footprint of semantic payload-bit lookup. -/
def writeFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  recoveryFootprint regs ∪
    {AssignmentBit.digitIndex regs} ∪
      AssignmentBit.writeFootprint regs

/-- One division iteration while recovering the exponent of a power of two.
-/
def recoverChunkBitsBody
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let stack := exponentStackRegisters regs
  Cmd.seqList
    [NeighborhoodProgram.pop stack,
      .basic
        (.add (recoveredChunkBits regs)
          (recoveredChunkBits regs) stack.one),
      .basic (.sub stack.test stack.word stack.one)]

/-- Uniformly recover `chunkBits` from the preserved runtime value
`Layout.chunkRadix = 2 ^ chunkBits`. -/
def recoverChunkBits
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let stack := exponentStackRegisters regs
  Cmd.seqList
    [CombineTerm.copy stack.word (Layout.chunkRadix regs),
      .basic (.imm stack.base 2),
      .basic (.imm stack.basePred 1),
      .basic (.imm stack.one 1),
      .basic (.imm (recoveredChunkBits regs) 0),
      .basic (.sub stack.test stack.word stack.one),
      .whileNonzero stack.test (recoverChunkBitsBody regs)]

/-- Exact low-order binary index computed from runtime parameters. -/
def assignmentIndex
    (workTapeCount chunkCount chunkBits : ℕ)
    (child : Fin (graphFanIn workTapeCount))
    (position : ℕ) : ℕ :=
  graphFanIn workTapeCount * chunkCount * chunkBits -
    1 - (chunkBits * chunkCount * child.val + position)

/-- Compute `assignmentIndex` into `AssignmentBit.digitIndex`.

The command reads the runtime chunk count, recovered chunk width, and payload
position. Its only source-level data are `workTapeCount`, `child`, and the
fixed register allocation.
-/
def prepareIndex
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (child : Fin (graphFanIn workTapeCount)) : Cmd :=
  let stack := exponentStackRegisters regs
  let index := AssignmentBit.digitIndex regs
  Cmd.seqList
    [.basic (.imm index (graphFanIn workTapeCount)),
      .basic (.mul index index (Layout.chunkCount regs)),
      .basic (.mul index index (recoveredChunkBits regs)),
      .basic (.sub index index stack.one),
      .basic (.imm stack.word child.val),
      .basic (.mul stack.word stack.word (Layout.chunkCount regs)),
      .basic (.mul stack.word stack.word (recoveredChunkBits regs)),
      .basic (.add stack.word stack.word (payloadPosition regs)),
      .basic (.sub index index stack.word)]

/-- Uniformly read one semantic payload bit of a fixed child from the current
grouped assignment code. -/
def read
    (workTapeCount : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (child : Fin (graphFanIn workTapeCount)) : Cmd :=
  Cmd.seqList
    [recoverChunkBits regs,
      prepareIndex workTapeCount regs child,
      AssignmentBit.read regs]

/-- Observable result and frame of one semantic payload-bit lookup. -/
structure Post
    (workTapeCount payloadWidth code : ℕ)
    (regs : NeighborhoodTrial.Registers controller)
    (child : Fin (graphFanIn workTapeCount))
    (position : Fin payloadWidth)
    (initial final : Store) : Prop where
  /-- Numeric Boolean value supplied at this child payload coordinate. -/
  value_eq :
    final (CombineTerm.packedValue regs) =
      (AssignmentCodeSemantics.assignmentBits
        payloadWidth (graphFanIn workTapeCount) code
        child position).toNat
  /-- The exact computed low-order digit index remains observable. -/
  index_eq :
    final (AssignmentBit.digitIndex regs) =
      AssignmentCodeSemantics.lowOrderBitIndex
        payloadWidth (graphFanIn workTapeCount) child position
  /-- The runtime semantic payload position is preserved. -/
  position_eq :
    final (payloadPosition regs) = position.val
  /-- The outer fold accumulator is preserved. -/
  accumulator_eq :
    final (CombineValue.rangeRegisters regs).accumulator =
      initial (CombineValue.rangeRegisters regs).accumulator
  /-- The current assignment code is preserved. -/
  remaining_eq :
    final (CombineValue.rangeRegisters regs).remaining = code
  /-- The field modulus is preserved. -/
  modulus_eq :
    final (CombineValue.rangeRegisters regs).modulus =
      initial (CombineValue.rangeRegisters regs).modulus
  /-- The field-modulus predecessor is preserved. -/
  modulusPred_eq :
    final (CombineValue.rangeRegisters regs).modulusPred =
      initial (CombineValue.rangeRegisters regs).modulusPred
  /-- The outer fold constant one is preserved. -/
  one_eq :
    final (CombineValue.rangeRegisters regs).one =
      initial (CombineValue.rangeRegisters regs).one
  /-- The immutable assignment count is preserved. -/
  count_eq :
    final (CombineValue.rangeRegisters regs).count =
      initial (CombineValue.rangeRegisters regs).count
  /-- The outer term cell is not consumed by payload-bit lookup. -/
  term_eq :
    final (CombineValue.rangeRegisters regs).term =
      initial (CombineValue.rangeRegisters regs).term
  /-- The suspended continuation word is preserved. -/
  stack_eq :
    final (Layout.frameStackRegisters regs).word =
      initial (Layout.frameStackRegisters regs).word
  /-- The packed catalytic bank is preserved. -/
  bank_eq :
    final regs.layout.bank = initial regs.layout.bank
  /-- Every active-frame and runtime-parameter ABI field is preserved. -/
  abi :
    ControlDecode.PreservesABI regs initial final
  /-- Every address outside the advertised scratch footprint is preserved. -/
  eq_outside :
    ∀ address, address ∉ writeFootprint regs →
      final address = initial address

end AssignmentPayloadBit
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
