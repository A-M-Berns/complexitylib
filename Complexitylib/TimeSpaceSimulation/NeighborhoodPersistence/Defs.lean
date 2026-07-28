/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Contents.Defs
import Complexitylib.TimeSpaceSimulation.Locality.Defs

/-!
# Tape-block persistence outside local three-block neighborhoods

For arbitrary machines, a length-`b` interval can modify only the three
canonical blocks around each starting head. This file names the interval
center and the finite block-membership predicate used by the neighborhood
computation graph.

## Main definitions

- `ContainsBlock` -- membership among center-1, center, center+1
- `centerBlock` -- starting head block for one interval and tape
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodPersistence

/-- A canonical tape block belongs to the truncated three-block neighborhood
around `center`. At center zero, the first two alternatives both denote block
zero. -/
def ContainsBlock (center block : ℕ) : Prop :=
  block = center - 1 ∨ block = center ∨ block = center + 1

/-- Starting head block of one length-`blockLength` interval. -/
def centerBlock
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength interval : ℕ)
    (tape : TapeIndex workTapeCount) : ℕ :=
  blockIndex blockLength
    (tapeAt
      (tm.configurationAt x
        (timeBlockStart blockLength interval))
      tape).head

end NeighborhoodPersistence

end TimeSpaceSimulation

end Complexity
