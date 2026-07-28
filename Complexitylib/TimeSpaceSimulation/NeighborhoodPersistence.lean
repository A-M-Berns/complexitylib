/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodPersistence.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodPersistence.Internal

/-!
# Correct tape-block persistence outside local neighborhoods

Every head remains in its three-block starting neighborhood for a complete
length-`b` interval. Hence any block outside that neighborhood is unchanged,
and a range of intervals avoiding a block preserves it exactly.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodPersistence

/-- After at most `blockLength` transitions, a head's canonical block belongs
to its three-block starting neighborhood. -/
theorem headBlock_containsBlock
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength start steps : ℕ)
    (tape : TapeIndex workTapeCount)
    (hpositive : 0 < blockLength)
    (hsteps : steps ≤ blockLength) :
    ContainsBlock
      (blockIndex blockLength
        (tapeAt (tm.configurationAt x start) tape).head)
      (headBlock blockLength
        (tm.configurationAt x (start + steps)) tape) :=
  Internal.headBlock_containsBlock_internal
    tm x blockLength start steps tape hpositive hsteps

/-- One length-`blockLength` interval preserves every block outside its
starting three-block neighborhood. -/
theorem inactive_interval_preserves
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength interval block : ℕ)
    (tape : TapeIndex workTapeCount)
    (hpositive : 0 < blockLength)
    (hinactive :
      ¬ContainsBlock
        (centerBlock tm x blockLength interval tape)
        block) :
    ComputationGraph.blockContentsAt tm x blockLength
        (timeBlockStart blockLength (interval + 1))
        tape block =
      ComputationGraph.blockContentsAt tm x blockLength
        (timeBlockStart blockLength interval)
        tape block :=
  Internal.inactive_interval_preserves_internal
    tm x blockLength interval block tape
      hpositive hinactive

/-- Any consecutive range of intervals whose neighborhoods avoid a block
preserves that block exactly. -/
theorem inactive_intervals_preserve
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength first count block : ℕ)
    (tape : TapeIndex workTapeCount)
    (hpositive : 0 < blockLength)
    (hinactive : ∀ offset, offset < count →
      ¬ContainsBlock
        (centerBlock tm x blockLength (first + offset) tape)
        block) :
    ComputationGraph.blockContentsAt tm x blockLength
        (timeBlockStart blockLength (first + count))
        tape block =
      ComputationGraph.blockContentsAt tm x blockLength
        (timeBlockStart blockLength first)
        tape block :=
  Internal.inactive_intervals_preserve_internal
    tm x blockLength first count block tape
      hpositive hinactive

end NeighborhoodPersistence

end TimeSpaceSimulation

end Complexity
