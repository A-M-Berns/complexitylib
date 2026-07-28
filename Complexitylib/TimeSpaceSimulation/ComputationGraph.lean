/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Internal

/-!
# Implicit computation-graph topology

This file exposes the bounded-indegree, well-founded predecessor topology of
the computation graph in Williams's simulation. Every non-source node has two
ordered predecessor roles per named tape, so its fixed input index has size
exactly `2 * (workTapeCount + 2)`. Every generated predecessor has strictly
smaller time-block rank.

The greatest-prior-visit query is executable as a finite search. No
Turing-machine workspace bound is claimed for it here.

## Main theorems

- `previousVisit_some_lt` -- a returned visit is genuinely earlier
- `previousVisit_some_maximal` -- it is the greatest matching earlier visit
- `previousVisit_eq_none_iff` -- absence is exactly first access
- `card_predecessorIndex` -- the input count is `2 * (workTapeCount + 2)`
- `predecessor_rank_lt` -- every generated edge strictly decreases rank
- `predecessorAt_rank_lt` -- the same result for the tree evaluator's
  `Fin (2 * (workTapeCount + 2))` child interface
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

/-- Membership in the finite prior-visit set. -/
theorem mem_priorVisits {active : ℕ → ℕ} {time previous : ℕ} :
    previous ∈ priorVisits active time ↔
      previous < time ∧ active previous = active time :=
  Internal.mem_priorVisits_internal

/-- A successful greatest-prior-visit query returns a member of the search
set. -/
theorem previousVisit_some_mem {active : ℕ → ℕ}
    {time previous : ℕ}
    (h : previousVisit active time = some previous) :
    previous ∈ priorVisits active time :=
  Internal.previousVisit_some_mem_internal h

/-- A returned previous visit is strictly earlier than the target. -/
theorem previousVisit_some_lt {active : ℕ → ℕ}
    {time previous : ℕ}
    (h : previousVisit active time = some previous) :
    previous < time :=
  Internal.previousVisit_some_lt_internal h

/-- A returned previous visit has the same active value as the target. -/
theorem previousVisit_some_active {active : ℕ → ℕ}
    {time previous : ℕ}
    (h : previousVisit active time = some previous) :
    active previous = active time :=
  Internal.previousVisit_some_active_internal h

/-- Every other matching earlier visit occurs no later than the returned
visit. -/
theorem previousVisit_some_maximal {active : ℕ → ℕ}
    {time previous : ℕ}
    (h : previousVisit active time = some previous)
    {candidate : ℕ} (hcandidate : candidate < time)
    (hactive : active candidate = active time) :
    candidate ≤ previous :=
  Internal.previousVisit_some_maximal_internal
    h hcandidate hactive

/-- A previous-visit search returns no result exactly when the current active
value has never occurred earlier. -/
theorem previousVisit_eq_none_iff {active : ℕ → ℕ} {time : ℕ} :
    previousVisit active time = none ↔
      ∀ previous, previous < time →
        active previous ≠ active time :=
  Internal.previousVisit_eq_none_iff_internal

/-- There are exactly two predecessor roles. -/
@[simp] theorem card_predecessorKind :
    Fintype.card PredecessorKind = 2 :=
  Internal.card_predecessorKind_internal

/-- Every computation node has exactly two ordered predecessor inputs per
named input/work/output tape. -/
theorem card_predecessorIndex (workTapeCount : ℕ) :
    Fintype.card (PredecessorIndex workTapeCount) =
      2 * (workTapeCount + 2) :=
  Internal.card_predecessorIndex_internal workTapeCount

/-- A content predecessor carries the requested named tape. -/
@[simp] theorem contentPredecessor_tape
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (tape : TapeIndex workTapeCount) :
    (contentPredecessor tm x blockLength timeBlock tape).tape = tape :=
  Internal.contentPredecessor_tape_internal
    tm x blockLength timeBlock tape

/-- A chronological predecessor carries the requested named tape. -/
@[simp] theorem chronologicalPredecessor_tape
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (tape : TapeIndex workTapeCount) :
    (chronologicalPredecessor tm x blockLength timeBlock tape).tape =
      tape :=
  Internal.chronologicalPredecessor_tape_internal
    tm x blockLength timeBlock tape

/-- The ordered predecessor oracle preserves the tape component of its
index. -/
@[simp] theorem predecessor_tape
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (index : PredecessorIndex workTapeCount) :
    (predecessor tm x blockLength timeBlock index).tape = index.2 :=
  Internal.predecessor_tape_internal
    tm x blockLength timeBlock index

/-- Every content edge points from a strictly smaller time-block rank. -/
theorem contentPredecessor_rank_lt
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape targetTape : TapeIndex workTapeCount) :
    (contentPredecessor tm x blockLength timeBlock tape).rank <
      (Node.computation targetTape timeBlock).rank :=
  Internal.contentPredecessor_rank_lt_internal
    tm x blockLength timeBlock tape targetTape

/-- Every chronological edge points from a strictly smaller time-block rank. -/
theorem chronologicalPredecessor_rank_lt
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape targetTape : TapeIndex workTapeCount) :
    (chronologicalPredecessor tm x blockLength timeBlock tape).rank <
      (Node.computation targetTape timeBlock).rank :=
  Internal.chronologicalPredecessor_rank_lt_internal
    tm x blockLength timeBlock tape targetTape

/-- Every edge generated by the ordered predecessor oracle strictly decreases
the target node's time-block rank. -/
theorem predecessor_rank_lt
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (index : PredecessorIndex workTapeCount) :
    (predecessor tm x blockLength timeBlock index).rank <
      (Node.computation targetTape timeBlock).rank :=
  Internal.predecessor_rank_lt_internal
    tm x blockLength timeBlock targetTape index

/-- Every edge generated by the explicitly Fin-indexed child oracle strictly
decreases the target node's time-block rank. -/
theorem predecessorAt_rank_lt
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (targetTape : TapeIndex workTapeCount)
    (index : Fin (2 * (workTapeCount + 2))) :
    (predecessorAt tm x blockLength timeBlock index).rank <
      (Node.computation targetTape timeBlock).rank :=
  Internal.predecessorAt_rank_lt_internal
    tm x blockLength timeBlock targetTape index

end ComputationGraph

end TimeSpaceSimulation

end Complexity
