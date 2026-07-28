/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.BlockRespecting
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Implicit computation-graph topology

Williams's computation graph gives each non-source time-block node two
predecessor roles for every named tape:

1. the immediately preceding time block, carrying state and head information;
2. the last earlier time block that accessed the same tape block, or an
   initial source node if this is the first access.

This file defines that topology as an executable predecessor oracle. A finite
search below the target time selects the greatest prior visit. The ordered
predecessor index has cardinality exactly `2 * (workTapeCount + 2)`.

Node contents and their local transition functions are deliberately absent.
The later semantic layer must prove that the contents of a target node are a
function of these predecessors, and the machine layer must implement the
finite search with a concrete workspace bound.

## Main definitions

- `ComputationGraph.previousVisit` -- greatest earlier occurrence of a value
- `ComputationGraph.Node` -- an initial source or a time-block computation
- `ComputationGraph.PredecessorKind` -- content or chronological input
- `ComputationGraph.predecessor` -- the fixed ordered predecessor oracle
- `ComputationGraph.Node.rank` -- source rank zero and time-block rank plus one
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

/-- Earlier times at which `active` has its current value. -/
def priorVisits (active : ℕ → ℕ) (time : ℕ) : Finset ℕ :=
  (Finset.range time).filter fun previous =>
    active previous = active time

/-- The greatest earlier time at which `active` has its current value, if one
exists. -/
def previousVisit (active : ℕ → ℕ) (time : ℕ) : Option ℕ :=
  if h : (priorVisits active time).Nonempty then
    some ((priorVisits active time).max' h)
  else
    none

/-- The active-block trajectory of one named tape. -/
def activeTrajectory (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (tape : TapeIndex workTapeCount) : ℕ → ℕ :=
  fun timeBlock => tm.activeBlock x blockLength timeBlock tape

/-- A source block from the initial configuration or a computed tape block
after one time block. -/
inductive Node (workTapeCount : ℕ) where
  /-- Initial contents of one tape block. -/
  | source (tape : TapeIndex workTapeCount) (block : ℕ)
  /-- Contents of one named tape block after `timeBlock`. -/
  | computation (tape : TapeIndex workTapeCount) (timeBlock : ℕ)
  deriving DecidableEq

namespace Node

/-- Every source has rank zero; a computation at time block `i` has rank
`i + 1`. Every computation-graph predecessor strictly decreases this rank. -/
def rank : Node workTapeCount → ℕ
  | .source _ _ => 0
  | .computation _ timeBlock => timeBlock + 1

/-- The named tape carried by a computation-graph node. -/
def tape : Node workTapeCount → TapeIndex workTapeCount
  | .source tape _ => tape
  | .computation tape _ => tape

end Node

/-- The two predecessor roles contributed by each named tape. -/
inductive PredecessorKind where
  /-- The last value of the tape block needed in the target time block. -/
  | content
  /-- State and head data from the immediately preceding time block. -/
  | chronological
  deriving DecidableEq, Fintype

namespace PredecessorKind

/-- Content inputs precede chronological inputs in the fixed ordering. -/
def toFin : PredecessorKind → Fin 2
  | .content => ⟨0, by omega⟩
  | .chronological => ⟨1, by omega⟩

/-- Decode one of the two predecessor roles. -/
def ofFin (index : Fin 2) : PredecessorKind :=
  if index.val = 0 then .content else .chronological

/-- Explicit ordering of the two predecessor roles. -/
def equivFin : PredecessorKind ≃ Fin 2 where
  toFun := toFin
  invFun := ofFin
  left_inv kind := by cases kind <;> rfl
  right_inv index := by
    apply Fin.ext
    by_cases hzero : index.val = 0
    · simp [ofFin, hzero, toFin]
    · have hone : index.val = 1 := by omega
      simp [ofFin, toFin, hone]

end PredecessorKind

/-- The fixed ordered inputs of every non-source computation node. -/
abbrev PredecessorIndex (workTapeCount : ℕ) :=
  PredecessorKind × TapeIndex workTapeCount

/-- Explicit content-first, tape-major ordering of all predecessor inputs. -/
def predecessorIndexEquiv (workTapeCount : ℕ) :
    PredecessorIndex workTapeCount ≃
      Fin (2 * (workTapeCount + 2)) :=
  (Equiv.prodCongr PredecessorKind.equivFin (Equiv.refl _)).trans
    finProdFinEquiv

/-- The previous computed version of the active block, or its initial source
when the target time block is its first visit. -/
def contentPredecessor (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (tape : TapeIndex workTapeCount) :
    Node workTapeCount :=
  let active := activeTrajectory tm x blockLength tape
  match previousVisit active timeBlock with
  | none => .source tape (active timeBlock)
  | some previous => .computation tape previous

/-- The immediately preceding computed node for one tape, or its initial
source at the first time block. -/
def chronologicalPredecessor (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (tape : TapeIndex workTapeCount) :
    Node workTapeCount :=
  match timeBlock with
  | 0 =>
      .source tape
        (activeTrajectory tm x blockLength tape 0)
  | previous + 1 => .computation tape previous

/-- Select one of the two predecessor roles for one named tape. -/
def predecessor (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (index : PredecessorIndex workTapeCount) :
    Node workTapeCount :=
  match index.1 with
  | .content =>
      contentPredecessor tm x blockLength timeBlock index.2
  | .chronological =>
      chronologicalPredecessor tm x blockLength timeBlock index.2

/-- Fin-indexed form of the predecessor oracle, matching the child interface
of the fixed-arity tree evaluator. -/
def predecessorAt (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (index : Fin (2 * (workTapeCount + 2))) :
    Node workTapeCount :=
  predecessor tm x blockLength timeBlock
    ((predecessorIndexEquiv workTapeCount).symm index)

end ComputationGraph

end TimeSpaceSimulation

end Complexity
