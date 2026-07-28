/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactContent
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactTree.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.Unroll

/-!
# Correctness of compact tree evaluation

The recursive compact graph evaluator agrees with the compact semantic value
at every node. Generic unrolling transfers the result and the graph-rank
height bound to the fixed-arity tree.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace CompactTree

namespace Internal

theorem nodeValue_eq_nodeContent_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (h : tm.BlockRespectingOnInput x blockLength)
    (node : Node workTapeCount) :
    nodeValue tm x blockLength hpositive node =
      CompactContent.nodeContent
        tm x blockLength hpositive node := by
  induction node using (measure Node.rank).wf.induction with
  | h node ih =>
      cases node with
      | source tape block =>
          rw [nodeValue, ComputationGraph.nodeValue]
          rfl
      | computation tape timeBlock =>
          rw [nodeValue, ComputationGraph.nodeValue]
          change CompactContent.localNodeFunction
              tm x blockLength hpositive timeBlock tape
              (fun index =>
                ComputationGraph.nodeValue tm x blockLength
                  (sourceFunction tm x blockLength hpositive)
                  (combineFunction tm x blockLength hpositive)
                  (predecessorAt tm x blockLength timeBlock
                    (predecessorIndexEquiv workTapeCount index))) = _
          have hinputs :
              (fun index =>
                ComputationGraph.nodeValue tm x blockLength
                  (sourceFunction tm x blockLength hpositive)
                  (combineFunction tm x blockLength hpositive)
                  (predecessorAt tm x blockLength timeBlock
                    (predecessorIndexEquiv workTapeCount index))) =
                CompactContent.predecessorContents
                  tm x blockLength timeBlock hpositive := by
            funext index
            change nodeValue tm x blockLength hpositive
              (predecessorAt tm x blockLength timeBlock
                (predecessorIndexEquiv workTapeCount index)) = _
            rw [ih _
              (predecessorAt_rank_lt
                tm x blockLength timeBlock tape
                  (predecessorIndexEquiv workTapeCount index))]
            simp [CompactContent.predecessorContents, predecessorAt]
          rw [hinputs]
          simpa using
            CompactContent.localNodeFunction_semantic
              tm x blockLength timeBlock tape h

theorem tree_value_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (h : tm.BlockRespectingOnInput x blockLength)
    (node : Node workTapeCount) :
    (tree tm x blockLength hpositive node).value =
      CompactContent.nodeContent
        tm x blockLength hpositive node := by
  calc
    (tree tm x blockLength hpositive node).value =
        nodeValue tm x blockLength hpositive node := by
      exact value_unroll tm x blockLength
        (sourceFunction tm x blockLength hpositive)
        (combineFunction tm x blockLength hpositive) node
    _ = CompactContent.nodeContent
          tm x blockLength hpositive node :=
      nodeValue_eq_nodeContent_internal
        tm x blockLength hpositive h node

theorem tree_height_le_rank_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    (tree tm x blockLength hpositive node).height ≤ node.rank := by
  exact height_unroll_le_rank tm x blockLength
    (sourceFunction tm x blockLength hpositive)
    (combineFunction tm x blockLength hpositive) node

end Internal

end CompactTree

end ComputationGraph

end TimeSpaceSimulation

end Complexity
