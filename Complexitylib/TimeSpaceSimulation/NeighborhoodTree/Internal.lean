/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.BooleanTree
import Complexitylib.TimeSpaceSimulation.NeighborhoodContent
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph
import Complexitylib.TimeSpaceSimulation.NeighborhoodTree.Defs

/-!
# Correctness internals for compact neighborhood trees
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodTree

open NeighborhoodGraph

namespace Internal

theorem compactNodeValue_eq_nodeContent_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    compactNodeValue tm x blockLength hpositive node =
      NeighborhoodContent.nodeContent
        tm x blockLength hpositive node := by
  induction node using (measure Node.rank).wf.induction with
  | h node ih =>
      cases node with
      | source tape block =>
          rw [compactNodeValue, NeighborhoodGraph.nodeValue]
          rfl
      | computation tape slot timeBlock =>
          rw [compactNodeValue, NeighborhoodGraph.nodeValue]
          change NeighborhoodContent.localNodeFunction
              tm x blockLength hpositive timeBlock tape slot
              (fun index =>
                NeighborhoodGraph.nodeValue tm x blockLength
                  (sourceFunction tm x blockLength hpositive)
                  (combineFunction tm x blockLength hpositive)
                  (predecessorAt tm x blockLength timeBlock
                    (predecessorIndexEquiv workTapeCount index))) = _
          have hinputs :
              (fun index =>
                NeighborhoodGraph.nodeValue tm x blockLength
                  (sourceFunction tm x blockLength hpositive)
                  (combineFunction tm x blockLength hpositive)
                  (predecessorAt tm x blockLength timeBlock
                    (predecessorIndexEquiv workTapeCount index))) =
                NeighborhoodContent.predecessorContents
                  tm x blockLength timeBlock hpositive := by
            funext index
            change compactNodeValue tm x blockLength hpositive
              (predecessorAt tm x blockLength timeBlock
                (predecessorIndexEquiv workTapeCount index)) = _
            rw [ih _
              (predecessorAt_rank_lt
                tm x blockLength timeBlock tape slot
                  (predecessorIndexEquiv workTapeCount index))]
            simp [NeighborhoodContent.predecessorContents,
              predecessorAt]
          rw [hinputs]
          exact NeighborhoodContent.localNodeFunction_semantic
            tm x blockLength timeBlock hpositive tape slot

theorem compactTree_value_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    (compactTree tm x blockLength hpositive node).value =
      NeighborhoodContent.nodeContent
        tm x blockLength hpositive node := by
  calc
    (compactTree tm x blockLength hpositive node).value =
        compactNodeValue tm x blockLength hpositive node := by
      exact NeighborhoodGraph.value_unroll
        tm x blockLength
          (sourceFunction tm x blockLength hpositive)
          (combineFunction tm x blockLength hpositive)
          node
    _ = NeighborhoodContent.nodeContent
          tm x blockLength hpositive node :=
      compactNodeValue_eq_nodeContent_internal
        tm x blockLength hpositive node

theorem compactTree_height_le_rank_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    (compactTree tm x blockLength hpositive node).height ≤
      node.rank := by
  exact NeighborhoodGraph.height_unroll_le_rank
    tm x blockLength
      (sourceFunction tm x blockLength hpositive)
      (combineFunction tm x blockLength hpositive)
      node

theorem booleanTree_value_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    (booleanTree tm x blockLength hpositive node).value =
      ComputationGraph.CompactEncoding.encode
        (NeighborhoodContent.nodeContent
          tm x blockLength hpositive node) := by
  unfold booleanTree
  calc
    (ComputationGraph.BooleanTree.encodeTree tm.qstart hpositive
        (compactTree tm x blockLength hpositive node)).value =
        ComputationGraph.CompactEncoding.encode
          (compactTree tm x blockLength hpositive node).value := by
      exact ComputationGraph.BooleanTree.encodeTree_value
        tm.qstart hpositive
          (compactTree tm x blockLength hpositive node)
    _ = ComputationGraph.CompactEncoding.encode
          (NeighborhoodContent.nodeContent
            tm x blockLength hpositive node) := by
      exact congrArg ComputationGraph.CompactEncoding.encode
        (compactTree_value_internal
          tm x blockLength hpositive node)

theorem booleanTree_height_le_rank_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    (booleanTree tm x blockLength hpositive node).height ≤
      node.rank := by
  unfold booleanTree
  calc
    (ComputationGraph.BooleanTree.encodeTree tm.qstart hpositive
        (compactTree tm x blockLength hpositive node)).height =
        (compactTree tm x blockLength hpositive node).height := by
      exact ComputationGraph.BooleanTree.encodeTree_height
        tm.qstart hpositive
          (compactTree tm x blockLength hpositive node)
    _ ≤ node.rank :=
      compactTree_height_le_rank_internal
        tm x blockLength hpositive node

end Internal

end NeighborhoodTree

end TimeSpaceSimulation

end Complexity
