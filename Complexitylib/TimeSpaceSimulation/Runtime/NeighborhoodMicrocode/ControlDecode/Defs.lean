/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Structured.Footprint.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameCodec.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Layout.Defs

/-!
# Concrete control-field decoding for neighborhood microcode

The active node and phase are packed little-endian radix words.  This module
fixes a first-order decoder using only repeated subtraction, direct-register
arithmetic, and seven time-multiplexed physical workspace cells.

The node view exposes a tag, tape, and two payloads.  The phase view reuses
the same cells for a tag, two two-digit residue words, and two child cursors.
Neither decoder writes the active frame or the parameter ABI.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ControlDecode

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- The seven physical cells time-multiplexed by control decoding. -/
def scratchMap : Fin 7 → Fin 34 :=
  ![0, 6, 9, 10, 11, 12, 18]

theorem scratchMap_injective :
    Function.Injective scratchMap := by
  decide

/-- Exact finite write footprint of both concrete decoders. -/
def scratchFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  Finset.univ.image fun slot => regs.index (scratchMap slot)

/-- Streaming word scratch. -/
abbrev word
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 0

/-- Shared node/phase tag output. -/
abbrev tag
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 6

/-- Shared first decoded payload: tape for nodes, residue for phases. -/
abbrev first
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 9

/-- Shared second decoded payload: first node payload or residues-left. -/
abbrev second
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 10

/-- Shared third decoded payload: second node payload or phase child. -/
abbrev third
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 11

/-- Shared fourth decoded payload: zero for nodes or next phase child. -/
abbrev fourth
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 12

/-- Last division-loop scratch cell. -/
abbrev loopScratch
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  regs.index 18

/-- Node-field name for the shared first output. -/
abbrev nodeTape
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  first regs

/-- Node-field name for the shared second output. -/
abbrev nodePayload0
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  second regs

/-- Node-field name for the shared third output. -/
abbrev nodePayload1
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  third regs

/-- Phase-field name for the shared first output. -/
abbrev phaseResidue
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  first regs

/-- Phase-field name for the shared second output. -/
abbrev phaseResiduesLeft
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  second regs

/-- Phase-field name for the shared third output. -/
abbrev phaseChild
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  third regs

/-- Phase-field name for the shared fourth output. -/
abbrev phaseNext
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  fourth regs

/-- Five pairwise-distinct registers for one destructive quotient/remainder
step.  The divisor is read-only. -/
structure DivisionRegisters where
  /-- Allocation order: remainder word, quotient, test, one, divisor. -/
  index : Fin 5 → ℕ
  /-- Logical division registers are physically distinct. -/
  injective : Function.Injective index

namespace DivisionRegisters

/-- Dividend on entry and remainder on exit. -/
abbrev value (regs : DivisionRegisters) : ℕ := regs.index 0

/-- Quotient output. -/
abbrev quotient (regs : DivisionRegisters) : ℕ := regs.index 1

/-- Loop-test scratch, cleared on exit. -/
abbrev test (regs : DivisionRegisters) : ℕ := regs.index 2

/-- Constant-one scratch, equal to one on exit. -/
abbrev one (regs : DivisionRegisters) : ℕ := regs.index 3

/-- Positive read-only divisor. -/
abbrev divisor (regs : DivisionRegisters) : ℕ := regs.index 4

/-- The four mutable registers of one quotient/remainder step. -/
def writeFootprint (regs : DivisionRegisters) : Finset ℕ :=
  {regs.value, regs.quotient, regs.test, regs.one}

end DivisionRegisters

/-- Set the loop test to `value + 1 - divisor`, which is nonzero exactly
when a positive divisor is at most the current value. -/
def divRemTest (regs : DivisionRegisters) : Cmd :=
  Cmd.seq
    (.basic (.add regs.test regs.value regs.one))
    (.basic (.sub regs.test regs.test regs.divisor))

/-- One repeated-subtraction quotient/remainder iteration. -/
def divRemBody (regs : DivisionRegisters) : Cmd :=
  Cmd.seqList
    [.basic (.sub regs.value regs.value regs.divisor),
      .basic (.add regs.quotient regs.quotient regs.one),
      divRemTest regs]

/-- Compute quotient and remainder by a positive runtime divisor.

On exit `value` contains the remainder, `quotient` the quotient, `test` is
zero, and `one` is one. -/
def divRem (regs : DivisionRegisters) : Cmd :=
  Cmd.seqList
    [.basic (.imm regs.one 1),
      .basic (.imm regs.quotient 0),
      divRemTest regs,
      .whileNonzero regs.test (divRemBody regs)]

/-- Exact observable postcondition of one quotient/remainder command. -/
structure DivRemPost
    (regs : DivisionRegisters) (base input : ℕ)
    (initial final : Store) : Prop where
  /-- The destructive input cell holds the remainder. -/
  value_eq : final regs.value = input % base
  /-- The quotient is retained for the next streaming stage. -/
  quotient_eq : final regs.quotient = input / base
  /-- The terminating loop test is zero. -/
  test_eq : final regs.test = 0
  /-- The local constant-one cell is initialized. -/
  one_eq : final regs.one = 1
  /-- The divisor is read-only. -/
  divisor_eq : final regs.divisor = base
  /-- Every address outside the four direct destinations is preserved. -/
  eq_outside :
    ∀ address, address ∉ regs.writeFootprint →
      final address = initial address

/-- Copy one direct register without an indirect load. -/
def copy (destination source : ℕ) : Cmd :=
  Cmd.seq
    (.basic (.imm destination 0))
    (.basic (.add destination source destination))

/-- First base-radix split shared by node and phase decoding. -/
def firstStage
    (regs : NeighborhoodTrial.Registers controller) :
    DivisionRegisters where
  index := fun slot =>
    regs.index (![0, 9, 10, 11, 8] slot)
  injective := regs.injective.comp (by decide)

/-- Second base-radix split used by node decoding. -/
def nodeSecondStage
    (regs : NeighborhoodTrial.Registers controller) :
    DivisionRegisters where
  index := fun slot =>
    regs.index (![9, 10, 11, 12, 8] slot)
  injective := regs.injective.comp (by decide)

/-- Third base-radix split used by node decoding. -/
def nodeThirdStage
    (regs : NeighborhoodTrial.Registers controller) :
    DivisionRegisters where
  index := fun slot =>
    regs.index (![10, 11, 12, 18, 8] slot)
  injective := regs.injective.comp (by decide)

/-- First two-digit-radix split used by phase decoding. -/
def phaseSecondStage
    (regs : NeighborhoodTrial.Registers controller) :
    DivisionRegisters where
  index := fun slot =>
    regs.index (![9, 10, 11, 12, 14] slot)
  injective := regs.injective.comp (by decide)

/-- Second two-digit-radix split used by phase decoding. -/
def phaseThirdStage
    (regs : NeighborhoodTrial.Registers controller) :
    DivisionRegisters where
  index := fun slot =>
    regs.index (![10, 11, 12, 18, 14] slot)
  injective := regs.injective.comp (by decide)

/-- Final base-radix split used by phase decoding. -/
def phaseFourthStage
    (regs : NeighborhoodTrial.Registers controller) :
    DivisionRegisters where
  index := fun slot =>
    regs.index (![11, 12, 18, 0, 8] slot)
  injective := regs.injective.comp (by decide)

/-- Non-destructively decode four base-radix node fields. -/
def decodeNode
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [copy (word regs) (Layout.nodeCode regs),
      divRem (firstStage regs),
      copy (tag regs) (word regs),
      divRem (nodeSecondStage regs),
      divRem (nodeThirdStage regs)]

/-- Non-destructively decode a seven-digit phase as tag, two two-digit
residue words, child, and next-child. -/
def decodePhase
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [copy (word regs) (Layout.phaseCode regs),
      divRem (firstStage regs),
      copy (tag regs) (word regs),
      divRem (phaseSecondStage regs),
      divRem (phaseThirdStage regs),
      divRem (phaseFourthStage regs)]

/-- Pure four-field projection computed by `decodeNode`. -/
@[ext]
structure NodeValues where
  /-- Least-significant node tag. -/
  tag : ℕ
  /-- Tape digit. -/
  tape : ℕ
  /-- First node payload. -/
  payload0 : ℕ
  /-- Second node payload. -/
  payload1 : ℕ

/-- Exact arithmetic node projection, with no encoding assumption. -/
def nodeValues (base code : ℕ) : NodeValues where
  tag := code % base
  tape := code / base % base
  payload0 := code / base / base % base
  payload1 := code / base / base / base

/-- Semantic node fields before radix packing. -/
def expectedNodeValues :
    NeighborhoodEvaluator.QueryNode workTapeCount horizon → NodeValues
  | .failure =>
      ⟨0, 0, 0, 0⟩
  | .graph (.source tape block) =>
      ⟨1, tape.val, block, 0⟩
  | .graph (.computation tape slot interval) =>
      ⟨2, tape.val, slot.toFin.val, interval⟩

/-- Pure five-field projection computed by `decodePhase`. -/
@[ext]
structure PhaseValues where
  /-- Least-significant phase tag. -/
  tag : ℕ
  /-- First two-digit residue word. -/
  residue : ℕ
  /-- Second two-digit residue word. -/
  residuesLeft : ℕ
  /-- Current child cursor. -/
  child : ℕ
  /-- Next-child cursor. -/
  next : ℕ

/-- Exact arithmetic phase projection, with no encoding assumption. -/
def phaseValues (base residueBase code : ℕ) : PhaseValues where
  tag := code % base
  residue := code / base % residueBase
  residuesLeft := code / base / residueBase % residueBase
  child := code / base / residueBase / residueBase % base
  next := code / base / residueBase / residueBase / base

/-- Semantic phase fields before radix packing. -/
def expectedPhaseValues :
    NeighborhoodScheduler.Phase workTapeCount → PhaseValues
  | .enter =>
      ⟨0, 0, 0, 0, 0⟩
  | .prepare residue residuesLeft childIndex =>
      ⟨1, residue, residuesLeft, childIndex, 0⟩
  | .combine residue residuesLeft =>
      ⟨2, residue, residuesLeft, 0, 0⟩
  | .cleanupCall residue residuesLeft childIndex =>
      ⟨3, residue, residuesLeft, childIndex, 0⟩
  | .cleanupScale residue residuesLeft child nextChildIndex =>
      ⟨4, residue, residuesLeft, child.val, nextChildIndex⟩

/-- Exact decoded-node outputs. -/
structure NodePost
    (regs : NeighborhoodTrial.Registers controller)
    (base code : ℕ) (final : Store) : Prop where
  /-- Decoded node tag. -/
  tag_eq : final (tag regs) = (nodeValues base code).tag
  /-- Decoded tape digit. -/
  tape_eq : final (nodeTape regs) = (nodeValues base code).tape
  /-- Decoded first payload. -/
  payload0_eq :
    final (nodePayload0 regs) = (nodeValues base code).payload0
  /-- Decoded second payload. -/
  payload1_eq :
    final (nodePayload1 regs) = (nodeValues base code).payload1
  /-- The unused fifth field is canonical zero. -/
  fourth_eq : final (fourth regs) = 0

/-- Exact decoded-phase outputs. -/
structure PhasePost
    (regs : NeighborhoodTrial.Registers controller)
    (base residueBase code : ℕ) (final : Store) : Prop where
  /-- Decoded phase tag. -/
  tag_eq : final (tag regs) = (phaseValues base residueBase code).tag
  /-- Decoded residue. -/
  residue_eq :
    final (phaseResidue regs) =
      (phaseValues base residueBase code).residue
  /-- Decoded remaining-residue counter. -/
  residuesLeft_eq :
    final (phaseResiduesLeft regs) =
      (phaseValues base residueBase code).residuesLeft
  /-- Decoded child cursor. -/
  child_eq :
    final (phaseChild regs) =
      (phaseValues base residueBase code).child
  /-- Decoded next-child cursor. -/
  next_eq :
    final (phaseNext regs) =
      (phaseValues base residueBase code).next

/-- Semantic node fields recovered from a fitting packed node. -/
structure EncodedNodePost
    (regs : NeighborhoodTrial.Registers controller)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon)
    (final : Store) : Prop where
  /-- Semantic node tag. -/
  tag_eq : final (tag regs) = (expectedNodeValues node).tag
  /-- Semantic tape coordinate. -/
  tape_eq : final (nodeTape regs) = (expectedNodeValues node).tape
  /-- Semantic first payload. -/
  payload0_eq :
    final (nodePayload0 regs) = (expectedNodeValues node).payload0
  /-- Semantic second payload. -/
  payload1_eq :
    final (nodePayload1 regs) = (expectedNodeValues node).payload1

/-- Semantic phase fields recovered from a fitting packed phase. -/
structure EncodedPhasePost
    (regs : NeighborhoodTrial.Registers controller)
    (phase : NeighborhoodScheduler.Phase workTapeCount)
    (final : Store) : Prop where
  /-- Semantic phase tag. -/
  tag_eq : final (tag regs) = (expectedPhaseValues phase).tag
  /-- Semantic residue. -/
  residue_eq :
    final (phaseResidue regs) = (expectedPhaseValues phase).residue
  /-- Semantic remaining-residue counter. -/
  residuesLeft_eq :
    final (phaseResiduesLeft regs) =
      (expectedPhaseValues phase).residuesLeft
  /-- Semantic child cursor. -/
  child_eq :
    final (phaseChild regs) = (expectedPhaseValues phase).child
  /-- Semantic next-child cursor. -/
  next_eq :
    final (phaseNext regs) = (expectedPhaseValues phase).next

/-- Active-frame and parameter cells that both decoders preserve. -/
structure PreservesABI
    (regs : NeighborhoodTrial.Registers controller)
    (initial final : Store) : Prop where
  /-- Recursion fuel is preserved. -/
  fuel_eq : final (Layout.fuel regs) = initial (Layout.fuel regs)
  /-- Packed node code is preserved. -/
  nodeCode_eq :
    final (Layout.nodeCode regs) = initial (Layout.nodeCode regs)
  /-- Active scalar is preserved. -/
  scalar_eq : final (Layout.scalar regs) = initial (Layout.scalar regs)
  /-- Active output index is preserved. -/
  out_eq : final (Layout.out regs) = initial (Layout.out regs)
  /-- Packed phase code is preserved. -/
  phaseCode_eq :
    final (Layout.phaseCode regs) = initial (Layout.phaseCode regs)
  /-- Active-frame flag is preserved. -/
  active_eq : final (Layout.active regs) = initial (Layout.active regs)
  /-- Block length is preserved. -/
  blockLength_eq :
    final (Layout.blockLength regs) = initial (Layout.blockLength regs)
  /-- Horizon is preserved. -/
  horizon_eq :
    final (Layout.horizon regs) = initial (Layout.horizon regs)
  /-- Chunk count is preserved. -/
  chunkCount_eq :
    final (Layout.chunkCount regs) = initial (Layout.chunkCount regs)
  /-- Codec radix is preserved. -/
  chunkRadix_eq :
    final (Layout.chunkRadix regs) = initial (Layout.chunkRadix regs)
  /-- Frame radix is preserved. -/
  frameRadix_eq :
    final (Layout.frameRadix regs) = initial (Layout.frameRadix regs)
  /-- Catalytic-bank radix is preserved. -/
  bankRadix_eq :
    final (Layout.bankRadix regs) = initial (Layout.bankRadix regs)
  /-- Catalytic-bank digit count is preserved. -/
  bankDigitCount_eq :
    final (Layout.bankDigitCount regs) =
      initial (Layout.bankDigitCount regs)
  /-- Field-modulus predecessor is preserved. -/
  modulusPred_eq :
    final (Layout.modulusPred regs) = initial (Layout.modulusPred regs)
  /-- Field modulus is preserved. -/
  modulus_eq :
    final (Layout.modulus regs) = initial (Layout.modulus regs)

end ControlDecode
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
