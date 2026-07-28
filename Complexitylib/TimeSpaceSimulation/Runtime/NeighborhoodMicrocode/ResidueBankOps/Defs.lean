/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Layout
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodProgram

/-!
# Concrete catalytic residue-bank operations

These commands connect the shared neighborhood-trial layout to the verified
packed residue-bank primitives.  Active-frame fields remain read-only:
`scaleActiveRegister` streams every chunk of the register selected by
`Layout.out`, while `addScaledActiveChunk` consumes one provider-supplied
chunk from the residue operand cell and the chunk cursor in
`Layout.codecScratch`.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ResidueBankOps

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Direct-register copy in the structured RAM instruction set. -/
def copy (destination source : ℕ) : Cmd :=
  Cmd.seq
    (.basic (.imm destination 0))
    (.basic (.add destination source destination))

/-- Canonical all-zero logical catalytic bank. -/
def zeroRegisters
    {workTapeCount : ℕ} (tm : TM workTapeCount) (blockLength : ℕ) :
    NeighborhoodExecutableEvaluation.Residue.Registers tm blockLength :=
  fun _ _ => 0

/-- Clear the packed catalytic-bank word without touching active-frame
fields. -/
def clearBank
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  .basic
    (.imm
      (Layout.residueScaleRegisters regs).bank.bank.word 0)

/-- Establish the reusable packed-bank constants and an all-zero bank. -/
def initializeBankOps
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let scale := Layout.residueScaleRegisters regs
  Cmd.basics
    [.imm scale.bank.bank.word 0,
      .imm scale.bank.bank.one 1,
      .sub scale.bank.bank.basePred
        scale.bank.bank.base scale.bank.bank.one,
      .imm scale.bank.bank.indexCount 0]

/-- Establish the reusable packed-bank constants and an all-zero bank. -/
def initializeBank
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  initializeBankOps regs

/-- Load the active register, scalar, and chunk count into the verified
whole-register scaling interface. -/
def prepareScaleActiveOps
    (regs : NeighborhoodTrial.Registers controller) : List Basic :=
  let scale := Layout.residueScaleRegisters regs
  [.imm scale.bank.bank.one 1,
    .sub scale.bank.bank.basePred
      scale.bank.bank.base scale.bank.bank.one,
    .imm scale.bank.operand 0,
    .add scale.bank.operand
      (Layout.scalar regs) scale.bank.operand,
    .imm scale.remaining 0,
    .add scale.remaining
      (Layout.chunkCount regs) scale.remaining,
    .mul scale.bank.bank.indexCount
      (Layout.out regs) (Layout.chunkCount regs)]

/-- Load the active register, scalar, and chunk count into the verified
whole-register scaling interface. -/
def prepareScaleActive
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.basics (prepareScaleActiveOps regs)

/-- Scale every chunk of the active catalytic register by the preserved
active-frame scalar. -/
def scaleActiveRegister
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let scale := Layout.residueScaleRegisters regs
  Cmd.seq (prepareScaleActive regs)
    (NeighborhoodProgram.bankScaleRegister scale)

/-- Row-major dynamic coordinate selected by the active output register and
the provider's current chunk cursor. -/
def activeChunkIndex
    (out chunkCount chunk : ℕ) : ℕ :=
  out * chunkCount + chunk

/-- Straight-line setup for one active row-major bank coordinate. -/
def prepareActiveChunkIndexOps
    (regs : NeighborhoodTrial.Registers controller) : List Basic :=
  let bank := (Layout.residueScaleRegisters regs).bank
  [.imm bank.bank.one 1,
    .sub bank.bank.basePred bank.bank.base bank.bank.one,
    .mul bank.bank.indexCount
      (Layout.out regs) (Layout.chunkCount regs),
    .add bank.bank.indexCount bank.bank.indexCount
      (Layout.codecScratch regs)]

/-- Load the row-major coordinate for the active output and current provider
chunk. -/
def prepareActiveChunkIndex
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.basics (prepareActiveChunkIndexOps regs)

/-- Multiply one provider-supplied chunk by the active scalar modulo the
field modulus, then add it into the selected catalytic-bank coordinate.

The provider writes its chunk into `bank.operand` and its chunk number into
`Layout.codecScratch`; neither active-frame field is overwritten.
-/
def addScaledActiveChunk
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let bank := (Layout.residueScaleRegisters regs).bank
  Cmd.seqList
    [RuntimeArithmetic.mulMod bank.reduceRegisters
        bank.operand (Layout.scalar regs),
      copy bank.operand bank.bank.replacement,
      prepareActiveChunkIndex regs,
      NeighborhoodProgram.bankAddAt bank]

end ResidueBankOps
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
