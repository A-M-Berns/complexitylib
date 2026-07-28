/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine

/-!
# Block-respecting multitape computations

This file defines the machine-independent vocabulary needed for the
Hopcroft--Paul--Valiant block-respecting normalization used by Williams.
There are `n + 2` named tapes in the library's machine model: the read-only
input tape, `n` work tapes, and the output tape.

A block of length `b` consists of positions `q * b` through
`(q + 1) * b - 1`. A run is block respecting when, during configurations
`q * b, ..., q * b + (b - 1)` of every time block, each named head stays in
the tape block occupied at configuration `q * b`. Thus a transition into
configuration `(q + 1) * b` may cross a tape-block boundary.

The deterministic run is represented by `TM.configurationAt`, the frozen
trace of `TM.toNTM`. It remains constant after halting and is reachable from
the initial configuration at every time.

## Main definitions

- `TimeSpaceSimulation.TapeIndex` -- input/work/output tape indices
- `TimeSpaceSimulation.blockIndex` -- tape block containing a position
- `TimeSpaceSimulation.InBlock` -- membership in one contiguous tape block
- `TimeSpaceSimulation.blockContents` -- the symbols in one tape block
- `TM.configurationAt` -- frozen deterministic configuration at a time
- `TM.BlockRespectingOnInput` -- block residence for one input and length
- `TM.BlockRespecting` -- input-length-indexed block residence
-/

namespace Complexity

namespace TimeSpaceSimulation

/-- Input/work/output tape indices in their canonical order. -/
abbrev TapeIndex (workTapeCount : ℕ) := Fin (workTapeCount + 2)

namespace TapeIndex

/-- The read-only input tape has index zero. -/
def input (workTapeCount : ℕ) : TapeIndex workTapeCount :=
  ⟨0, by omega⟩

/-- Work tape `index` has named-tape index `index + 1`. -/
def work (index : Fin workTapeCount) : TapeIndex workTapeCount :=
  ⟨index.val + 1, by omega⟩

/-- The output tape follows all work tapes. -/
def output (workTapeCount : ℕ) : TapeIndex workTapeCount :=
  ⟨workTapeCount + 1, by omega⟩

end TapeIndex

/-- Select a named input/work/output tape from a configuration. -/
def tapeAt (cfg : Cfg workTapeCount Q)
    (tape : TapeIndex workTapeCount) : Tape :=
  if hinput : tape.val = 0 then
    cfg.input
  else if houtput : tape.val = workTapeCount + 1 then
    cfg.output
  else
    cfg.work ⟨tape.val - 1, by omega⟩

/-- The zero-based tape-block index containing `position`. -/
def blockIndex (blockLength position : ℕ) : ℕ :=
  position / blockLength

/-- `position` lies in the contiguous zero-based tape block `block`. -/
def InBlock (blockLength block position : ℕ) : Prop :=
  block * blockLength ≤ position ∧
    position < (block + 1) * blockLength

/-- The `blockLength` symbols in one contiguous block of a tape. -/
def blockContents (tape : Tape) (blockLength block : ℕ) :
    Fin blockLength → Γ :=
  fun offset => tape.cells (block * blockLength + offset.val)

/-- The tape block occupied by one named head. -/
def headBlock (blockLength : ℕ) (cfg : Cfg workTapeCount Q)
    (tape : TapeIndex workTapeCount) : ℕ :=
  blockIndex blockLength (tapeAt cfg tape).head

/-- The first configuration time in a time block. -/
def timeBlockStart (blockLength timeBlock : ℕ) : ℕ :=
  timeBlock * blockLength

end TimeSpaceSimulation

namespace TM

open TimeSpaceSimulation

variable {workTapeCount : ℕ}

/-- The deterministic configuration at `time`, frozen after halting.

Using the deterministic NTM embedding gives a total executable run without
changing the underlying configuration type. -/
def configurationAt (tm : TM workTapeCount) (x : List Bool) (time : ℕ) :
    Cfg workTapeCount tm.Q :=
  tm.toNTM.trace time (fun _ => false) (tm.initCfg x)

/-- Each named head stays in one tape block throughout each time block on one
fixed input.

The positive-length conjunct rules out the vacuous `Fin 0` case. -/
def BlockRespectingOnInput (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) : Prop :=
  0 < blockLength ∧
    ∀ (timeBlock : ℕ) (offset : Fin blockLength)
        (tape : TapeIndex workTapeCount),
      headBlock blockLength
          (tm.configurationAt x
            (timeBlockStart blockLength timeBlock + offset.val))
          tape =
        headBlock blockLength
          (tm.configurationAt x (timeBlockStart blockLength timeBlock))
          tape

/-- A machine is block respecting for an input-length-indexed block size. -/
def BlockRespecting (tm : TM workTapeCount)
    (blockLength : ℕ → ℕ) : Prop :=
  ∀ x, tm.BlockRespectingOnInput x (blockLength x.length)

/-- The tape block active for one named tape during a time block. -/
def activeBlock (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) : ℕ :=
  headBlock blockLength
    (tm.configurationAt x (timeBlockStart blockLength timeBlock)) tape

end TM

end Complexity
