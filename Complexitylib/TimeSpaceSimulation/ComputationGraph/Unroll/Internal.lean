/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Unroll.Defs

/-!
# Implicit computation-graph unrolling internals

This file proves that semantic tree unrolling preserves recursive node
evaluation and that its height is bounded by the source/time-block rank.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace Internal

variable {workTapeCount : ℕ} {V : Type*}

theorem value_unroll_internal
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → ℕ →
      (Fin (2 * (workTapeCount + 2)) → V) → V)
    (node : Node workTapeCount) :
    (unroll tm x blockLength sourceValue combine node).value =
      nodeValue tm x blockLength sourceValue combine node := by
  induction node using (measure Node.rank).wf.induction with
  | h node ih =>
      cases node with
      | source tape block =>
          rw [unroll, nodeValue, TreeEval.Tree.value_leaf]
      | computation tape timeBlock =>
          rw [unroll, nodeValue, TreeEval.Tree.value_node]
          apply congrArg (combine tape timeBlock)
          funext index
          exact ih _
            (predecessorAt_rank_lt
              tm x blockLength timeBlock tape index)

theorem height_unroll_le_rank_internal
    (tm : TM workTapeCount) (x : List Bool) (blockLength : ℕ)
    (sourceValue : TapeIndex workTapeCount → ℕ → V)
    (combine : TapeIndex workTapeCount → ℕ →
      (Fin (2 * (workTapeCount + 2)) → V) → V)
    (node : Node workTapeCount) :
    (unroll tm x blockLength sourceValue combine node).height ≤
      node.rank := by
  induction node using (measure Node.rank).wf.induction with
  | h node ih =>
      cases node with
      | source tape block =>
          rw [unroll, TreeEval.Tree.height_leaf]
          rfl
      | computation tape timeBlock =>
          rw [unroll, TreeEval.Tree.height_node]
          have hsup :
              Finset.univ.sup (fun index =>
                (unroll tm x blockLength sourceValue combine
                  (predecessorAt tm x blockLength timeBlock index)).height) ≤
                timeBlock := by
            rw [Finset.sup_le_iff]
            intro index _
            exact
              (ih _
                (predecessorAt_rank_lt
                  tm x blockLength timeBlock tape index)).trans
                (Nat.lt_succ_iff.mp
                  (predecessorAt_rank_lt
                    tm x blockLength timeBlock tape index))
          simpa [Node.rank, Nat.add_comm] using
            Nat.add_le_add_left hsup 1

end Internal

end ComputationGraph

end TimeSpaceSimulation

end Complexity
