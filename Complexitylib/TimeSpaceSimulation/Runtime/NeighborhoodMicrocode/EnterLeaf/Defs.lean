/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ResidueBankOps.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.SourceValue.Defs

/-!
# Entry transitions for failure and source leaves

Failure and source nodes stream one residue coordinate at a time into the
active catalytic register.  The active fuel cell is temporarily reused as
the loop counter; the original fuel is saved in the phase cell and restored
before the current frame is popped.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace EnterLeaf

open RAM Structured
open NeighborhoodExecutableEvaluation

variable {controller : SearchProgram.Registers}

/-- Direct-register copy in the structured RAM instruction set. -/
def copy (destination source : ℕ) : Cmd :=
  Cmd.seq
    (.basic (.imm destination 0))
    (.basic (.add destination source destination))

/-- Save active fuel, install the grouped-coordinate loop count, and clear
the grouped-coordinate cursor. -/
def initializeLeaf
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [copy (Layout.phaseCode regs) (Layout.fuel regs),
      copy (Layout.fuel regs) (Layout.chunkCount regs),
      .basic (.imm (Layout.codecScratch regs) 0)]

/-- Advance the grouped-coordinate cursor and decrement the temporary loop
counter. -/
def advanceChunk
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (.basic
      (.add (Layout.codecScratch regs)
        (Layout.codecScratch regs) controller.one))
    (.basic
      (.sub (Layout.fuel regs) (Layout.fuel regs) controller.one))

/-- Produce one source/failure chunk, add its scaled value into the active
bank coordinate, and advance to the next coordinate. -/
def chunkBody
    (regs : NeighborhoodTrial.Registers controller)
    (provider : Cmd) : Cmd :=
  Cmd.seq provider
    (Cmd.seq (ResidueBankOps.addScaledActiveChunk regs)
      (advanceChunk regs))

/-- Restore the active frame fields repurposed by the leaf loop.  Enter is
the all-zero phase code. -/
def restore
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (copy (Layout.fuel regs) (Layout.phaseCode regs))
    (.basic (.imm (Layout.phaseCode regs) 0))

/-- Generic leaf entry: stream every provider chunk, restore the current
frame, and expose the suspended parent (or the exact terminal state). -/
def enterWith
    (regs : NeighborhoodTrial.Registers controller)
    (provider : Cmd) : Cmd :=
  Cmd.seqList
    [initializeLeaf regs,
      .whileNonzero (Layout.fuel regs) (chunkBody regs provider),
      restore regs,
      FrameTransfer.popParent regs]

/-- Concrete failure-leaf entry transition. -/
def failure
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  enterWith regs (SourceValue.failureChunk regs)

/-- Re-decode the stable source node before producing each source chunk.
Source evaluation reuses the decoded-node cells, so decoding is deliberately
inside the loop. -/
def sourceProvider
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq (ControlDecode.decodeNode regs)
    (SourceValue.sourceChunk tm order regs)

/-- Concrete source-leaf entry transition. -/
def source
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  enterWith regs (sourceProvider tm order regs)

/-- Logical bank after the first `processed` coordinates of one leaf value
have been scaled and added to the active output register. -/
def addScaledPrefix
    (tm : TM workTapeCount) (blockLength scalar : ℕ)
    (original : Residue.Registers tm blockLength)
    (out : Fin (graphFanIn workTapeCount + 1))
    (value : ResidueValue tm blockLength)
    (processed : ℕ) :
    Residue.Registers tm blockLength :=
  fun register chunk =>
    if register = out ∧ chunk.val < processed then
      NeighborhoodProgram.ResidueBankOp.add.apply
        (modulus tm blockLength)
        (original register chunk)
        ((value chunk * scalar) % modulus tm blockLength)
    else
      original register chunk

/-- Provider endpoint needed by the generic leaf loop.  It records the
operand and the complete state that must survive until the bank update. -/
structure ProviderPost
    (regs : NeighborhoodTrial.Registers controller)
    (input : List Bool) (expected : ℕ)
    (initial final : Store) : Prop where
  /-- The current logical chunk is installed as the bank operand. -/
  operand_eq :
    final (SourceValue.operand regs) = expected
  /-- Collision-safe public-input access remains valid. -/
  inputFrame :
    SearchProgram.InputFrame controller regs.footprint input final
  /-- Active fields and retained parameters are preserved. -/
  abi : ControlDecode.PreservesABI regs initial final
  /-- The grouped-coordinate cursor is preserved. -/
  cursor_eq :
    final (Layout.codecScratch regs) =
      initial (Layout.codecScratch regs)
  /-- The suspended continuation word is preserved. -/
  stack_eq :
    final regs.layout.stack = initial regs.layout.stack
  /-- The packed catalytic bank is preserved. -/
  bank_eq :
    final regs.layout.bank = initial regs.layout.bank
  /-- The public input length is preserved. -/
  inputLength_eq :
    final controller.inputLength = initial controller.inputLength
  /-- The shared constant one is preserved. -/
  one_eq : final controller.one = initial controller.one

/-- Uniform semantic contract for a per-coordinate provider. -/
def ProviderSpec
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (node :
      NeighborhoodEvaluator.QueryNode
        workTapeCount instanceData.horizon)
    (input : List Bool) (provider : Cmd)
    (value : ResidueValue tm instanceData.blockLength) : Prop :=
  ∀ (chunk :
      Fin
        (TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
          (payloadWidth tm instanceData.blockLength)
          (graphFanIn workTapeCount)))
      (initial : Store),
    initial (Layout.nodeCode regs) =
        FrameCodec.encodeNode
          (Representation.digitBase instanceData) node →
    initial (Layout.codecScratch regs) = chunk.val →
    Representation.Parameters regs instanceData initial →
    SearchProgram.InputFrame
      controller regs.footprint input initial →
    initial controller.inputLength = input.length →
    initial controller.one = 1 →
    ∃ final,
      Runs provider initial final ∧
      ProviderPost regs input (value chunk) initial final

/-- Exact semantic invariant at the head of the generic leaf loop. -/
structure LoopState
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (rest : List (NeighborhoodScheduler.Frame tm instanceData))
    (input : List Bool)
    (value : ResidueValue tm instanceData.blockLength)
    (original : Residue.Registers tm instanceData.blockLength)
    (processed remaining : ℕ) (store : Store) : Prop where
  /-- Processed and remaining coordinates partition the exact chunk count. -/
  balance :
    processed + remaining =
      TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
        (payloadWidth tm instanceData.blockLength)
        (graphFanIn workTapeCount)
  /-- Active fuel is temporarily the loop counter. -/
  remaining_eq : store (Layout.fuel regs) = remaining
  /-- The codec scratch cell is the current grouped-coordinate cursor. -/
  cursor_eq : store (Layout.codecScratch regs) = processed
  /-- The original active fuel is saved in the phase cell. -/
  savedFuel_eq : store (Layout.phaseCode regs) = frame.fuel
  /-- The stable node code is unchanged. -/
  node_eq :
    store (Layout.nodeCode regs) =
      FrameCodec.encodeNode
        (Representation.digitBase instanceData) frame.node
  /-- The active scalar is unchanged. -/
  scalar_eq : store (Layout.scalar regs) = frame.scalar
  /-- The active output register is unchanged. -/
  out_eq : store (Layout.out regs) = frame.out.val
  /-- The active flag remains set. -/
  active_eq : store (Layout.active regs) = 1
  /-- All retained instance parameters remain exact. -/
  parameters : Representation.Parameters regs instanceData store
  /-- The logical suspended tail remains packed exactly. -/
  suspended :
    FrameTransfer.RepresentsStack regs
      (Representation.digitBase instanceData)
      (Representation.frameBase instanceData) rest store
  /-- The bank contains exactly the prefix processed so far. -/
  bank :
    NeighborhoodProgram.RepresentsResidueBank
      tm instanceData.blockLength
      (Representation.fieldBase instanceData)
      (store regs.layout.bank)
      (addScaledPrefix tm instanceData.blockLength frame.scalar
        original frame.out value processed)
  /-- The packed bank stays inside its canonical digit capacity. -/
  bank_lt :
    store regs.layout.bank <
      Representation.fieldBase instanceData ^
        ((graphFanIn workTapeCount + 1) *
          TreeEval.CookMertz.PrimeGrouped.Logarithmic.chunkCount
            (payloadWidth tm instanceData.blockLength)
            (graphFanIn workTapeCount))
  /-- Collision-safe public-input access remains valid. -/
  inputFrame :
    SearchProgram.InputFrame controller regs.footprint input store
  /-- The public input length remains exact. -/
  inputLength_eq : store controller.inputLength = input.length
  /-- The shared increment/decrement constant remains one. -/
  one_eq : store controller.one = 1

end EnterLeaf
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
