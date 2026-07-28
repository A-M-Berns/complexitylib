/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Dispatcher.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Representation.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ResidueBankOps.Defs

/-!
# Uniform combine-branch composition

This definitions layer implements the uniform control surrounding one
runtime-cursor computation-chunk provider.  The provider is invoked once for
each grouped output chunk, in descending order.  Its result is multiplied by
the negative active scalar and added to the active catalytic register.  The
original scalar is restored after every update, and the final command
installs `cleanupCall residue residuesLeft 0`.

The provider contract is deliberately explicit.  It must preserve the active
ABI, packed continuation word, and packed bank while returning the chunk
selected by the temporary runtime cursor in `Layout.active`.  This is the
remaining uniform lowering boundary for the frame-specialized combine-term
kernels.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace CombineBranch

open RAM Structured
open TreeEval CookMertz

variable {controller : SearchProgram.Registers}

/-- Direct-register copy used by the uniform combine driver. -/
def copy (destination source : ℕ) : Cmd :=
  Cmd.seq
    (.basic (.imm destination 0))
    (.basic (.add destination source destination))

/-- The residue operand cell in which a chunk provider returns its result. -/
abbrev chunkValue
    (regs : NeighborhoodTrial.Registers controller) : ℕ :=
  (Layout.residueScaleRegisters regs).bank.operand

/-- Save the active scalar and install its negative field representative.

The command uses the representative `p - scalar`.  When `scalar = 0` this is
`p` rather than the canonical zero, but the immediately following scaled-bank
operation reduces the product modulo `p`, so both representatives act
identically.  The provider result in `chunkValue` is not overwritten.  The
temporary countdown is also copied to the residue-bank cursor, since a
provider may use the shared codec scratch internally.
-/
def installNegativeScalar
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [copy (Layout.frameCode regs) (Layout.scalar regs),
      copy (Layout.codecScratch regs) (Layout.active regs),
      .basic
        (.sub (Layout.scalar regs) (Layout.modulus regs)
          (Layout.frameCode regs))]

/-- Restore the active scalar saved immediately before one bank update. -/
def restoreScalar
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  copy (Layout.scalar regs) (Layout.frameCode regs)

/-- Add one provider result, scaled by the negative active scalar, to the
active output register and restore the original scalar. -/
def addNegativeScaledChunk
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [installNegativeScalar regs,
      ResidueBankOps.addScaledActiveChunk regs,
      restoreScalar regs]

/-- One dynamic chunk iteration.

The active flag is temporarily a positive remaining-count register.  It is
decremented before invoking the provider, so the provider observes the
zero-based output chunk in descending order.
-/
def streamBody
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (chunkKernel : Cmd) : Cmd :=
  Cmd.seqList
    [.basic
      (.sub (Layout.active regs) (Layout.active regs) controller.one),
      chunkKernel,
      addNegativeScaledChunk regs]

/-- Invoke one uniform provider for every runtime grouped output chunk.

The active flag is restored to one after the temporary countdown reaches
zero.
-/
def streamChunks
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (chunkKernel : Cmd) : Cmd :=
  Cmd.seqList
    [copy (Layout.active regs) (Layout.chunkCount regs),
      .whileNonzero (Layout.active regs)
        (streamBody controller regs chunkKernel),
      .basic (.imm (Layout.active regs) 1)]

/-- Decode the preserved combine phase and install its cleanup-call
successor with child cursor zero. -/
def installCleanupCall
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seq
    (ControlDecode.decodePhase regs)
    (Dispatcher.encodeCleanupCallPhase regs)

/-- Uniform combine-branch command around one runtime-cursor chunk provider. -/
def step
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (chunkKernel : Cmd) : Cmd :=
  Cmd.seq
    (streamChunks controller regs chunkKernel)
    (installCleanupCall regs)

/-- Logical child rows visible to one active computation frame. -/
def computationArguments
    {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    Fin (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount) →
      NeighborhoodExecutableEvaluation.ResidueValue
        tm instanceData.blockLength :=
  fun child => logicalBank (frame.childTarget child)

/-- Store representation needed by a uniform computation-chunk provider.

Unlike `Representation.QueryState`, this context does not constrain the
active flag, because the combine driver temporarily uses that cell as its
chunk cursor.
-/
structure ComputationContext
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store) : Prop where
  /-- Runtime parameters retain their exact instance values. -/
  parameters :
    Representation.Parameters regs instanceData store
  /-- The active node is this exact computation node. -/
  nodeCode_eq :
    store (Layout.nodeCode regs) =
      FrameCodec.encodeNode (Representation.digitBase instanceData)
        (show
          NeighborhoodEvaluator.QueryNode
            workTapeCount instanceData.horizon
          from .graph (.computation tape slot interval))
  /-- The active output coordinate is represented literally. -/
  out_eq : store (Layout.out regs) = frame.out.val
  /-- The packed catalytic bank has this exact logical meaning. -/
  bank :
    NeighborhoodProgram.RepresentsResidueBank
      tm instanceData.blockLength
      (Representation.fieldBase instanceData)
      (store regs.layout.bank) logicalBank

/-- Observable contract of one runtime-cursor chunk-provider invocation. -/
structure ChunkPost
    (regs : NeighborhoodTrial.Registers controller)
    (value cursor : ℕ) (initial final : Store) : Prop where
  /-- Exact provider result in the shared residue operand cell. -/
  value_eq : final (chunkValue regs) = value
  /-- The complete active-frame and parameter ABI is preserved. -/
  abi : ControlDecode.PreservesABI regs initial final
  /-- The suspended continuation word is restored exactly. -/
  stack_eq :
    final (Layout.frameStackRegisters regs).word =
      initial (Layout.frameStackRegisters regs).word
  /-- The packed catalytic bank is restored exactly. -/
  bank_eq : final regs.layout.bank = initial regs.layout.bank
  /-- In particular, the dynamic chunk cursor is preserved. -/
  cursor_eq : final (Layout.active regs) = cursor
  /-- The controller's persistent constant one is preserved. -/
  one_eq : final controller.one = initial controller.one

/-- Exact remaining boundary for a uniform computation-chunk provider.

The same `kernel` must work for every runtime cursor and every logically
represented catalytic bank.  Static frame data occur only in this semantic
contract; they are not arguments to the command.
-/
def ComputationChunkKernelSpecAt
    {tm : TM workTapeCount}
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ)
    (kernel : Cmd) : Prop :=
  ∀ (logicalBank :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength)
    (store : Store)
    (chunk :
      Fin
        (PrimeGrouped.Logarithmic.chunkCount
          (NeighborhoodExecutableEvaluation.payloadWidth
            tm instanceData.blockLength)
          (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount))),
    ComputationContext regs instanceData frame tape slot interval
        logicalBank store →
    store (Layout.active regs) = chunk.val →
    ∃ final,
      Runs kernel store final ∧
      ChunkPost regs
        (NeighborhoodExecutableEvaluation.combineResidues
          tm instanceData.x instanceData.blockLength
          instanceData.encoding instanceData.positive tape slot
          interval (computationArguments frame logicalBank) chunk)
        chunk.val store final

/-- One fixed provider command satisfies the computation-chunk contract for
every runtime instance and represented computation frame. -/
def ComputationChunkKernelSpec
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (kernel : Cmd) : Prop :=
  ∀ (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (tape : TapeIndex workTapeCount)
    (slot : NeighborhoodGraph.Slot)
    (interval : ℕ),
    ComputationChunkKernelSpecAt
      regs instanceData frame tape slot interval kernel

end CombineBranch
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
