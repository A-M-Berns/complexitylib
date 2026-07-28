/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Contents.Defs

/-!
# Local time-block simulation relations

This file defines agreement restricted to one block of every named tape.
Williams's local node function does not receive whole configurations: it gets
the state and heads from chronological predecessors and the active tape-block
contents from last-visit predecessors. `CfgBlockAgreement` is the semantic
relation needed to prove that those data suffice for a whole time block.

## Main definitions

- `TapeBlockAgreement` -- equal heads and equal cells inside one tape block
- `CfgBlockAgreement` -- state and named-tape block agreement
- `activeBlocks` -- the block selected for every named tape in a time block
-/

namespace Complexity

namespace TimeSpaceSimulation

/-- Two tapes have equal heads and agree on every cell of one block. Cells
outside the block are deliberately unconstrained. -/
structure TapeBlockAgreement (blockLength block : ℕ)
    (left right : Tape) : Prop where
  /-- Both tapes place their heads at the same absolute position. -/
  head_eq : left.head = right.head
  /-- Every cell inside the selected block has the same symbol. -/
  cells_eq : ∀ position, InBlock blockLength block position →
    left.cells position = right.cells position

/-- Two configurations agree on the state, every named head, and the contents
of one selected block per named tape. -/
structure CfgBlockAgreement (blockLength : ℕ)
    (blocks : TapeIndex workTapeCount → ℕ)
    (left right : Cfg workTapeCount Q) : Prop where
  /-- Machine states agree. -/
  state_eq : left.state = right.state
  /-- Input tapes agree on the selected input block. -/
  input : TapeBlockAgreement blockLength
    (blocks (TapeIndex.input workTapeCount)) left.input right.input
  /-- Every work tape agrees on its selected work block. -/
  work : ∀ index, TapeBlockAgreement blockLength
    (blocks (TapeIndex.work index))
    (left.work index) (right.work index)
  /-- Output tapes agree on the selected output block. -/
  output : TapeBlockAgreement blockLength
    (blocks (TapeIndex.output workTapeCount)) left.output right.output

/-- The selected block of every named tape during one block-respecting time
block. -/
def activeBlocks (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) :
    TapeIndex workTapeCount → ℕ :=
  fun tape => tm.activeBlock x blockLength timeBlock tape

end TimeSpaceSimulation

end Complexity
