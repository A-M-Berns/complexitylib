/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LocalFunction
import Complexitylib.TimeSpaceSimulation.ComputationGraph.LocalTree.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Unroll

/-!
# Tree-evaluation instance correctness internals

This file proves by well-founded induction that recursive evaluation with the
local time-block function returns the rich semantic value of every node. The
generic unrolling theorem then transfers this result to the fixed-arity tree.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace LocalTree

namespace Internal

theorem localNodeValue_eq_nodeContent_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength)
    (node : Node workTapeCount) :
    localNodeValue tm x blockLength node =
      nodeContent tm x blockLength node := by
  induction node using (measure Node.rank).wf.induction with
  | h node ih =>
      cases node with
      | source tape block =>
          rw [localNodeValue, nodeValue]
          rfl
      | computation tape timeBlock =>
          rw [localNodeValue, nodeValue]
          change LocalFunction.localNodeFunction
              tm x blockLength timeBlock tape
              (fun index =>
                nodeValue tm x blockLength
                  (localSourceFunction tm x blockLength)
                  (localCombineFunction tm x blockLength)
                  (predecessorAt tm x blockLength timeBlock
                    (predecessorIndexEquiv workTapeCount index))) = _
          have hinputs :
              (fun index =>
                nodeValue tm x blockLength
                  (localSourceFunction tm x blockLength)
                  (localCombineFunction tm x blockLength)
                  (predecessorAt tm x blockLength timeBlock
                    (predecessorIndexEquiv workTapeCount index))) =
                LocalFunction.predecessorNodeContents
                  tm x blockLength timeBlock := by
            funext index
            change localNodeValue tm x blockLength
              (predecessorAt tm x blockLength timeBlock
                (predecessorIndexEquiv workTapeCount index)) = _
            rw [ih _
              (predecessorAt_rank_lt
                tm x blockLength timeBlock tape
                  (predecessorIndexEquiv workTapeCount index))]
            simp [LocalFunction.predecessorNodeContents, predecessorAt]
          rw [hinputs]
          exact LocalFunction.localNodeFunction_semantic
            tm x blockLength timeBlock tape h

theorem localTree_value_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ)
    (h : tm.BlockRespectingOnInput x blockLength)
    (node : Node workTapeCount) :
    (localTree tm x blockLength node).value =
      nodeContent tm x blockLength node := by
  calc
    (localTree tm x blockLength node).value =
        localNodeValue tm x blockLength node := by
      exact value_unroll
        tm x blockLength
          (localSourceFunction tm x blockLength)
          (localCombineFunction tm x blockLength) node
    _ = nodeContent tm x blockLength node :=
      localNodeValue_eq_nodeContent_internal
        tm x blockLength h node

theorem localTree_height_le_rank_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (node : Node workTapeCount) :
    (localTree tm x blockLength node).height ≤ node.rank := by
  exact height_unroll_le_rank
    tm x blockLength
      (localSourceFunction tm x blockLength)
      (localCombineFunction tm x blockLength) node

end Internal

end LocalTree

end ComputationGraph

end TimeSpaceSimulation

end Complexity
