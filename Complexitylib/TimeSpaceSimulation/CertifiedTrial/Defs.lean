/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.DecisionRecovery.Defs
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.EvaluatedProvider.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Search.Defs

/-!
# One locally certified candidate-time trial

A trial engine contains only executable callbacks:

* an Option-valued evaluator for one guessed neighborhood-graph node;
* an Option-valued evaluator for the two decision roots.

The trial streams all ternary movement guesses, selects the first one passing
the local consistency check, evaluates its snapshot, and returns a Boolean
only when the recovered state is halted and the verdict symbol is `0` or `1`.
No true trajectory or source time-bound function occurs in `run`.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace CertifiedTrial

open NeighborhoodGraph
open NeighborhoodGraph.Guess

/-- Executable callbacks needed by one fixed block/horizon trial. -/
structure Engine (tm : TM workTapeCount)
    (blockLength horizon : ℕ) where
  /-- Evaluate one node of a guessed graph, with explicit failure. -/
  node :
    EvaluatedProvider.NodeContentCallback
      workTapeCount tm blockLength horizon
  /-- Evaluate the state and verdict roots for a guessed graph. -/
  snapshot :
    CenterGuess workTapeCount horizon →
      Option (DecisionRecovery.Snapshot tm.Q)

/-- Decode a legal decision symbol. Other alphabet symbols are rejected. -/
def decodeVerdict (symbol : Γ) : Option Bool :=
  if symbol = Γ.one then
    some true
  else if symbol = Γ.zero then
    some false
  else
    none

/-- Run one block/horizon trial by searching all movement guesses.

The consistency provider is computed from `engine.node`; `engine.snapshot`
is invoked only for the first locally accepted guess. -/
def run (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (engine : Engine tm blockLength horizon) :
    Option Bool :=
  match Search.firstPassingCode tm x blockLength
      (EvaluatedProvider.provider engine.node) with
  | none => none
  | some code =>
      let guess :=
        Enumeration.candidateGuess
          (Fin.cast (by simp [Search.guessCount]) code :
            Fin (3 ^ Enumeration.movementCount
              workTapeCount horizon))
      match engine.snapshot guess with
      | none => none
      | some snapshot =>
          if snapshot.state = tm.qhalt then
            decodeVerdict snapshot.verdict
          else
            none

/-- Proof-only correctness contract for an executable trial engine. -/
def Engine.IsExact {workTapeCount : ℕ}
    {tm : TM workTapeCount}
    (engine : Engine tm blockLength horizon)
    (x : List Bool) (hpositive : 0 < blockLength) : Prop :=
  EvaluatedProvider.IsPrefixExact
      tm x blockLength hpositive engine.node ∧
    ∀ guess : CenterGuess workTapeCount horizon,
      guess.IsValidFor
          (actualCenterTrajectory tm x blockLength) →
        engine.snapshot guess =
          some (DecisionRecovery.decisionSnapshot
            tm x blockLength hpositive horizon)

end CertifiedTrial

end TimeSpaceSimulation

end Complexity
