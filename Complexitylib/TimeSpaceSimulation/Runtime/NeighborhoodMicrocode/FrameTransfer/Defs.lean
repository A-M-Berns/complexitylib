/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.FrameCodec
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.Layout.Defs

/-!
# First-order transfer of neighborhood-scheduler frames

These commands are the concrete bridge between the six active-frame scalar
registers and the packed suspended-parent stack.  They contain only fixed
direct-register RAM operations and the already verified packed-word division
loops.

The active scalar encodings use the allocation fixed by `FrameCodec`:

* one radix digit for fuel;
* four digits for the query node;
* two digits for the field scalar;
* one digit for the output index;
* seven digits for the scheduler phase.

The nine reserved high digits are zero, so they need not be materialized.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace FrameTransfer

open RAM Structured

variable {controller : SearchProgram.Registers}

/-- Exact fixed write footprint of active-frame transfer commands. -/
def writeFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  {regs.index 0, regs.index 1, regs.index 4, regs.index 5,
    regs.index 17, regs.index 22, regs.index 23, regs.index 25,
    regs.index 26, regs.index 27, regs.index 28, regs.index 29,
    regs.index 30, regs.index 32}

/-- Exact five-cell write footprint of parent suspension alone. -/
def pushWriteFootprint
    (regs : NeighborhoodTrial.Registers controller) : Finset ℕ :=
  {regs.index 4, regs.index 17, regs.index 29,
    regs.index 30, regs.index 32}

/-- Direct-register copy, expressed using the source RAM instruction set. -/
def copy (destination source : ℕ) : Cmd :=
  Cmd.seq
    (.basic (.imm destination 0))
    (.basic (.add destination source destination))

/-- Pure numeral encoded by the active-field packing command. -/
def activeCode
    (radix bankRadix fuel node scalar out phase : ℕ) : ℕ :=
  fuel +
    radix *
      (node +
        bankRadix * bankRadix *
          (scalar + bankRadix * (out + radix * phase)))

/-- Word remaining after a fixed number of radix pops. -/
def poppedCode (radix code count : ℕ) : ℕ :=
  (PackedDigits.pop radix)^[count] code

/-- Fuel digit decoded by `loadActive`. -/
def decodedFuel (radix code : ℕ) : ℕ :=
  PackedDigits.digit radix code 0

/-- Four-digit node subword decoded by `loadActive`. -/
def decodedNodeCode
    (radix bankRadix code : ℕ) : ℕ :=
  poppedCode radix code 1 -
    bankRadix * bankRadix * poppedCode radix code 5

/-- Two-digit scalar subword decoded by `loadActive`. -/
def decodedScalar
    (radix bankRadix code : ℕ) : ℕ :=
  poppedCode radix code 5 -
    bankRadix * poppedCode radix code 7

/-- Output-index digit decoded by `loadActive`. -/
def decodedOut (radix code : ℕ) : ℕ :=
  PackedDigits.digit radix (poppedCode radix code 7) 0

/-- Seven-digit high phase subword decoded by `loadActive`. -/
def decodedPhase (radix code : ℕ) : ℕ :=
  poppedCode radix code 8

/-- Observable correctness relation for active-frame decoding. -/
structure LoadPost
    (regs : NeighborhoodTrial.Registers controller)
    (radix bankRadix code : ℕ) (final : Store) : Prop where
  /-- Fuel is the least-significant digit. -/
  fuel_eq :
    final (Layout.fuel regs) = decodedFuel radix code
  /-- The next four digits form the query-node code. -/
  nodeCode_eq :
    final (Layout.nodeCode regs) =
      decodedNodeCode radix bankRadix code
  /-- The next two digits form the field scalar. -/
  scalar_eq :
    final (Layout.scalar regs) =
      decodedScalar radix bankRadix code
  /-- The next digit is the catalytic output index. -/
  out_eq :
    final (Layout.out regs) = decodedOut radix code
  /-- The remaining low seven digits form the phase code. -/
  phaseCode_eq :
    final (Layout.phaseCode regs) = decodedPhase radix code
  /-- A loaded frame is live. -/
  active_eq :
    final (Layout.active regs) = 1

/-- Exact observable state obtained by decoding one fitting scheduler frame. -/
structure FrameLoadPost
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (base : ℕ)
    (frame : NeighborhoodScheduler.Frame tm instanceData)
    (final : Store) : Prop where
  /-- The recursion-fuel field is restored. -/
  fuel_eq :
    final (Layout.fuel regs) = frame.fuel
  /-- The active query node is restored in its four-digit representation. -/
  nodeCode_eq :
    final (Layout.nodeCode regs) =
      FrameCodec.encodeNode base frame.node
  /-- The field scalar is restored exactly. -/
  scalar_eq :
    final (Layout.scalar regs) = frame.scalar
  /-- The catalytic output coordinate is restored. -/
  out_eq :
    final (Layout.out regs) = frame.out.val
  /-- The scheduler phase is restored in its seven-digit representation. -/
  phaseCode_eq :
    final (Layout.phaseCode regs) =
      FrameCodec.encodePhase base frame.phase
  /-- A restored frame is live. -/
  active_eq :
    final (Layout.active regs) = 1

/-- Packed least-significant-first representation of suspended frames.

Each stored frame code is shifted by one.  Thus even the all-zero logical
frame contributes a positive least-significant digit and cannot be confused
with the empty stack word. -/
def encodeStack
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (digitBase frameBase : ℕ) :
    List (NeighborhoodScheduler.Frame tm instanceData) → ℕ
  | [] => 0
  | frame :: rest =>
      PackedDigits.push frameBase
        (FrameCodec.encodeFrame digitBase frame + 1)
        (encodeStack digitBase frameBase rest)

/-- One packed continuation word represents a logical suspended-frame stack. -/
def RepresentsStack
    {workTapeCount : ℕ} {tm : TM workTapeCount}
    {instanceData : NeighborhoodProgram.ResidueInstance tm}
    (regs : NeighborhoodTrial.Registers controller)
    (digitBase frameBase : ℕ)
    (frames : List (NeighborhoodScheduler.Frame tm instanceData))
    (store : Store) : Prop :=
  store (Layout.frameStackRegisters regs).word =
    encodeStack digitBase frameBase frames

/-- Straight-line instructions implementing `activeCode`. -/
def encodeActiveOps
    (regs : NeighborhoodTrial.Registers controller) : List Basic :=
  let codec := Layout.frameCodecRegisters regs
  [.imm (Layout.frameCode regs) 0,
    .add (Layout.frameCode regs)
      (Layout.phaseCode regs) (Layout.frameCode regs),
    .mul codec.quotient
      (Layout.chunkRadix regs) (Layout.frameCode regs),
    .add (Layout.frameCode regs)
      (Layout.out regs) codec.quotient,
    .mul codec.quotient
      (Layout.bankRadix regs) (Layout.frameCode regs),
    .add (Layout.frameCode regs)
      (Layout.scalar regs) codec.quotient,
    .mul (Layout.codecDigit regs)
      (Layout.bankRadix regs) (Layout.bankRadix regs),
    .mul codec.quotient
      (Layout.codecDigit regs) (Layout.frameCode regs),
    .add (Layout.frameCode regs)
      (Layout.nodeCode regs) codec.quotient,
    .mul codec.quotient
      (Layout.chunkRadix regs) (Layout.frameCode regs),
    .add (Layout.frameCode regs)
      (Layout.fuel regs) codec.quotient,
    .imm codec.quotient 0,
    .imm (Layout.codecDigit regs) 0]

/-- Repeat packed-word division by the codec radix a fixed number of times. -/
def popMany
    (regs : NeighborhoodTrial.Registers controller) : ℕ → Cmd
  | 0 => .skip
  | count + 1 =>
      Cmd.seq
        (NeighborhoodProgram.pop (Layout.frameCodecRegisters regs))
        (popMany regs count)

/-- Divide the transient frame-code word by the codec radix four times. -/
def popNodeCode
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  popMany regs 4

/-- Divide the transient frame-code word by the codec radix twice. -/
def popScalar
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  popMany regs 2

/-- Pack the six active scalar fields into `Layout.frameCode`.

The existing runtime parameter cells provide `r = 2^q` and `r^2`.
Consequently the straight-line arithmetic realizes

`fuel + r * (node + r^4 * (scalar + r^2 * (out + r * phase)))`.
-/
def encodeActive
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.basics (encodeActiveOps regs)

/-- Establish the positive codec divisor ABI. -/
def initializeCodec
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let codec := Layout.frameCodecRegisters regs
  Cmd.basics
    [.imm codec.one 1,
      .sub codec.basePred codec.base codec.one]

/-- Read the least-significant frame digit into the active fuel cell. -/
def readFuel
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let codec := Layout.frameCodecRegisters regs
  Cmd.seq (NeighborhoodProgram.peek codec)
    (copy (Layout.fuel regs) codec.value)

/-- Remove fuel and snapshot the four-digit node subword. -/
def captureNode
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let codec := Layout.frameCodecRegisters regs
  Cmd.seq (NeighborhoodProgram.pop codec)
    (copy (Layout.nodeCode regs) codec.word)

/-- Remove the four node digits and subtract the remaining high word. -/
def recoverNode
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let codec := Layout.frameCodecRegisters regs
  Cmd.seq (popNodeCode regs)
    (Cmd.basics
      [.mul (Layout.codecDigit regs)
          (Layout.bankRadix regs) (Layout.bankRadix regs),
        .mul codec.quotient
          (Layout.codecDigit regs) codec.word,
        .sub (Layout.nodeCode regs)
          (Layout.nodeCode regs) codec.quotient])

/-- Snapshot the two-digit scalar subword. -/
def captureScalar
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  copy (Layout.scalar regs)
    (Layout.frameCodecRegisters regs).word

/-- Remove the two scalar digits and subtract the remaining high word. -/
def recoverScalar
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let codec := Layout.frameCodecRegisters regs
  Cmd.seq (popScalar regs)
    (Cmd.basics
      [.mul codec.quotient
          (Layout.bankRadix regs) codec.word,
        .sub (Layout.scalar regs)
          (Layout.scalar regs) codec.quotient])

/-- Read and remove the one-digit catalytic output index. -/
def readOut
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let codec := Layout.frameCodecRegisters regs
  Cmd.seq (NeighborhoodProgram.peek codec)
    (Cmd.seq
      (copy (Layout.out regs) codec.value)
      (NeighborhoodProgram.pop codec))

/-- Install the remaining seven-digit phase code and canonicalize transient
codec cells. -/
def finishLoad
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let codec := Layout.frameCodecRegisters regs
  Cmd.seq
    (copy (Layout.phaseCode regs) codec.word)
    (Cmd.basics
      [.imm (Layout.active regs) 1,
        .imm codec.word 0,
        .imm codec.quotient 0,
        .imm codec.test 0,
        .imm codec.value 0])

/-- Decode `Layout.frameCode` into the six active scalar fields.

The command streams divisions by `r`; subtraction of the known quotient
times `r^4` or `r^2` recovers the packed node and scalar subwords exactly.
-/
def loadActive
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  Cmd.seqList
    [initializeCodec regs,
      readFuel regs,
      captureNode regs,
      recoverNode regs,
      captureScalar regs,
      recoverScalar regs,
      readOut regs,
      finishLoad regs]

/-- Encode, shift, and push the current active frame as one suspended
parent.  The shift makes zero-valued frames distinguishable from the empty
stack. -/
def pushParent
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let stack := Layout.frameStackRegisters regs
  Cmd.seqList
    [encodeActive regs,
      .basic (.imm stack.one 1),
      .basic (.add stack.value stack.value stack.one),
      NeighborhoodProgram.push stack]

/-- Pop and decode one suspended parent, or clear the active flag when the
packed continuation stack is empty. -/
def popParent
    (regs : NeighborhoodTrial.Registers controller) : Cmd :=
  let stack := Layout.frameStackRegisters regs
  .ifZero stack.word
    (.basic (.imm (Layout.active regs) 0))
    (Cmd.seqList
      [.basic (.imm stack.one 1),
        .basic (.sub stack.basePred stack.base stack.one),
        NeighborhoodProgram.peek stack,
        .basic (.sub stack.value stack.value stack.one),
        NeighborhoodProgram.pop stack,
        loadActive regs])

end FrameTransfer
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
