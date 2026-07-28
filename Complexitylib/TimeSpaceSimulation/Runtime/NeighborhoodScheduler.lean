/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.Internal

/-!
# Concrete finite-phase neighborhood scheduler

This module exposes the termination and result-correctness interface of the
defunctionalized natural-residue evaluator. The scheduler uses numeric loop
cursors and an explicit recursive-call stack; it contains no higher-order
continuations and no runtime-sized residue list.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodScheduler

open NeighborhoodExecutableEvaluation NeighborhoodEvaluator

variable {workTapeCount : ℕ}
variable {tm : TM workTapeCount}
variable {instanceData : NeighborhoodProgram.ResidueInstance tm}

/-- Every nonterminal query microstep strictly decreases the exact rank. -/
theorem schedulerRank_decreases
    (state : State tm instanceData)
    (hstate : ¬state.Terminal) :
    Work.rank state.next < Work.rank state :=
  Work.rank_next_lt state hstate

/-- Exact-rank iteration reaches an empty query continuation stack. -/
theorem schedulerRun_terminal
    (state : State tm instanceData) :
    (run state).Terminal :=
  run_terminal state

/--
Running a fresh query returns exactly the register bank computed by
`Residue.profileAccumulate`.
-/
theorem schedulerRun_profileAccumulate
    (fuel : ℕ)
    (node : QueryNode workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin (graphFanIn workTapeCount + 1))
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    (run (State.initial fuel node scalar out registers)).registers =
      (NeighborhoodExecutableEvaluation.Residue.profileAccumulate
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess
        fuel node scalar out registers).result :=
  Semantics.run_initial_registers_eq_profileAccumulate
    fuel node scalar out registers

/--
Running a fresh arbitrary-node query with a zero catalytic bank returns
exactly `Residue.profileEvaluate` in the distinguished output coordinate.
This is the scheduler boundary used by local-consistency provider queries.
-/
theorem schedulerRun_profileEvaluate
    (fuel : ℕ)
    (node : QueryNode workTapeCount instanceData.horizon) :
    (run
      (State.initial fuel node
        (TreeEval.CookMertz.PrimeField.Runtime.normalize
          (fieldModulus instanceData) 1)
        (Fin.last (graphFanIn workTapeCount))
        (fun _ =>
          NeighborhoodExecutableEvaluation.Residue.zeroValue
            tm instanceData.blockLength))).registers
        (Fin.last (graphFanIn workTapeCount)) =
      (NeighborhoodExecutableEvaluation.Residue.profileEvaluate
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess fuel node).result :=
  Semantics.run_initial_evaluate_result fuel node

namespace Decision

/-- Every nonterminal decision microstep strictly decreases its exact rank. -/
theorem schedulerRank_decreases
    (state : State tm instanceData)
    (hstate : ¬Terminal state) :
    rank (next state) < rank state :=
  rank_next_lt state hstate

/-- Exact-rank iteration reaches the terminal decision phase. -/
theorem schedulerRun_terminal
    (state : State tm instanceData) :
    Terminal (run state) :=
  run_terminal state

/--
The terminal pair produced by the concrete sequential scheduler is exactly
the ordinary result component of `Residue.profileDecision`.
-/
theorem schedulerRun_profileDecision :
    result (run (initial (instanceData := instanceData))) =
      (NeighborhoodExecutableEvaluation.Residue.profileDecision
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess).result :=
  run_initial_result_eq_profileDecision

end Decision

end NeighborhoodScheduler
end Runtime
end TimeSpaceSimulation
end Complexity
