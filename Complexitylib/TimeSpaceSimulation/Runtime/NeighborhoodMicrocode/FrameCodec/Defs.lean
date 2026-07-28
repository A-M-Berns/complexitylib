/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.StackDepth.Defs

/-!
# Radix codec for neighborhood-scheduler frames

One frame occupies exactly twenty-four base-`2^q` digits. The allocation is
little-endian:

* digit 0: recursion fuel;
* digits 1--4: query node;
* digits 5--6: field scalar;
* digit 7: catalytic output index;
* digits 8--14: scheduler phase;
* digits 15--23: reserved zero digits.

Natural field residues use two digits. Query nodes use tag, tape, and two
payload digits. Phases use a tag, two residues of two digits each, and two
child cursors. These are proof-level codec definitions; the concrete RAM
commands stream the same digits through the packed-stack primitives.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace FrameCodec

open NeighborhoodGraph
open NeighborhoodExecutableEvaluation

/-- Number of base-`2^q` digits assigned to one query node. -/
def nodeDigitCount : ℕ := 4

/-- Number of base-`2^q` digits assigned to one field scalar. -/
def scalarDigitCount : ℕ := 2

/-- Number of base-`2^q` digits assigned to one scheduler phase. -/
def phaseDigitCount : ℕ := 7

/-- Total number of base-`2^q` digits in one suspended frame. -/
def frameDigitCount : ℕ := 24

/-- Reserved high zero digits in one suspended frame. -/
def reservedDigitCount : ℕ := 9

/-- Encode a little-endian list as one packed radix word. -/
def encodeList (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | digit :: rest =>
      PackedDigits.push base digit (encodeList base rest)

/-- The two least-significant digits of one natural value. -/
def scalarDigits (base value : ℕ) : List ℕ :=
  [PackedDigits.digit base value 0,
    PackedDigits.digit base value 1]

/-- Four-digit query-node encoding. -/
def nodeDigits :
    NeighborhoodEvaluator.QueryNode workTapeCount horizon → List ℕ
  | .failure => [0, 0, 0, 0]
  | .graph (.source tape block) =>
      [1, tape.val, block, 0]
  | .graph (.computation tape slot interval) =>
      [2, tape.val, slot.toFin.val, interval]

/-- Packed four-digit query-node code held in the active-frame cell. -/
def encodeNode
    (base : ℕ)
    (node : NeighborhoodEvaluator.QueryNode workTapeCount horizon) : ℕ :=
  encodeList base (nodeDigits node)

/-- Seven-digit scheduler-phase encoding. -/
def phaseDigits
    (base : ℕ) :
    NeighborhoodScheduler.Phase workTapeCount → List ℕ
  | .enter => [0, 0, 0, 0, 0, 0, 0]
  | .prepare residue residuesLeft childIndex =>
      [1] ++ scalarDigits base residue ++
        scalarDigits base residuesLeft ++ [childIndex, 0]
  | .combine residue residuesLeft =>
      [2] ++ scalarDigits base residue ++
        scalarDigits base residuesLeft ++ [0, 0]
  | .cleanupCall residue residuesLeft childIndex =>
      [3] ++ scalarDigits base residue ++
        scalarDigits base residuesLeft ++ [childIndex, 0]
  | .cleanupScale residue residuesLeft child nextChildIndex =>
      [4] ++ scalarDigits base residue ++
        scalarDigits base residuesLeft ++
          [child.val, nextChildIndex]

/-- Packed seven-digit phase code held in the active-frame cell. -/
def encodePhase
    (base : ℕ) (phase : NeighborhoodScheduler.Phase workTapeCount) : ℕ :=
  encodeList base (phaseDigits base phase)

/-- Exact twenty-four-digit allocation of one complete scheduler frame. -/
def frameDigits
    (base : ℕ)
    (frame : NeighborhoodScheduler.Frame tm instanceData) : List ℕ :=
  frame.fuel ::
    (nodeDigits frame.node ++
      (scalarDigits base frame.scalar ++
        (frame.out.val ::
          (phaseDigits base frame.phase ++
            List.replicate reservedDigitCount 0))))

/-- Complete packed code of one suspended scheduler frame. -/
def encodeFrame
    (base : ℕ)
    (frame : NeighborhoodScheduler.Frame tm instanceData) : ℕ :=
  encodeList base (frameDigits base frame)

/-- Every physical codec digit of a frame is a valid radix digit. -/
def FrameFits
    (base : ℕ)
    (frame : NeighborhoodScheduler.Frame tm instanceData) : Prop :=
  ∀ digit ∈ frameDigits base frame, digit < base

end FrameCodec
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
