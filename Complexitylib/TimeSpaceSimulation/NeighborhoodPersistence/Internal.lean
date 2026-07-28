/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Contents
import Complexitylib.TimeSpaceSimulation.Locality
import Complexitylib.TimeSpaceSimulation.NeighborhoodPersistence.Defs

/-!
# Correctness of neighborhood tape-block persistence
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodPersistence

namespace Internal

theorem headBlock_containsBlock_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength start steps : ℕ)
    (tape : TapeIndex workTapeCount)
    (hpositive : 0 < blockLength)
    (hsteps : steps ≤ blockLength) :
    ContainsBlock
      (blockIndex blockLength
        (tapeAt (tm.configurationAt x start) tape).head)
      (headBlock blockLength
        (tm.configurationAt x (start + steps)) tape) := by
  have hin :=
    tm.configurationAt_head_in_threeBlockNeighborhood
      x blockLength start steps tape hpositive hsteps
  rw [inThreeBlockNeighborhood_iff_three_blocks] at hin
  unfold ContainsBlock
  rcases hin with hleft | hcenter | hright
  · left
    exact ComputationGraph.blockIndex_eq_of_inBlock hleft
  · right
    left
    exact ComputationGraph.blockIndex_eq_of_inBlock hcenter
  · right
    right
    exact ComputationGraph.blockIndex_eq_of_inBlock hright

theorem inactive_interval_preserves_internal
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
        tape block := by
  have hpersist :=
    ComputationGraph.blockContentsAt_add_eq_of_headBlock_ne
      tm x blockLength block
        (timeBlockStart blockLength interval)
        blockLength tape
  rw [show timeBlockStart blockLength interval + blockLength =
      timeBlockStart blockLength (interval + 1) by
        simp [timeBlockStart, Nat.add_mul]] at hpersist
  apply hpersist
  intro offset hoffset heq
  apply hinactive
  rw [← heq]
  exact headBlock_containsBlock_internal
    tm x blockLength
      (timeBlockStart blockLength interval)
      offset tape hpositive (by omega)

theorem inactive_intervals_preserve_internal
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
        tape block := by
  induction count with
  | zero =>
      simp
  | succ count ih =>
      calc
        ComputationGraph.blockContentsAt tm x blockLength
            (timeBlockStart blockLength
              (first + (count + 1)))
            tape block =
            ComputationGraph.blockContentsAt tm x blockLength
              (timeBlockStart blockLength
                (first + count))
              tape block := by
          have hpersist :=
            inactive_interval_preserves_internal
              tm x blockLength (first + count)
                block tape hpositive
                (hinactive count (Nat.lt_succ_self count))
          simpa [Nat.add_assoc] using hpersist
        _ =
            ComputationGraph.blockContentsAt tm x blockLength
              (timeBlockStart blockLength first)
              tape block := by
          apply ih
          intro offset hoffset
          exact hinactive offset
            (Nat.lt_succ_of_lt hoffset)

end Internal

end NeighborhoodPersistence

end TimeSpaceSimulation

end Complexity
