/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.BooleanTree.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactEncoding
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactTree

/-!
# Correctness of Boolean computation trees

Encoding a compact tree preserves both its value, up to the one-hot
representation, and its exact height.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace BooleanTree

namespace Internal

theorem encodeTree_value_internal
    [Fintype Q] [DecidableEq Q]
    (defaultState : Q) (hpositive : 0 < blockLength)
    (compactTree :
      TreeEval.Tree d (CompactContent.Content blockLength Q)) :
    (encodeTree defaultState hpositive compactTree).value =
      CompactEncoding.encode compactTree.value := by
  induction compactTree with
  | leaf value =>
      rfl
  | node children combine ih =>
      rw [encodeTree, TreeEval.Tree.value_node]
      have hchildren :
          (fun index =>
            CompactEncoding.decode defaultState hpositive
              ((encodeTree defaultState hpositive
                (children index)).value)) =
            (fun index => (children index).value) := by
        funext index
        rw [ih index]
        exact CompactEncoding.decode_encode
          defaultState hpositive (children index).value
      rw [hchildren]
      rfl

theorem encodeTree_height_internal
    [Fintype Q] [DecidableEq Q]
    (defaultState : Q) (hpositive : 0 < blockLength)
    (compactTree :
      TreeEval.Tree d (CompactContent.Content blockLength Q)) :
    (encodeTree defaultState hpositive compactTree).height =
      compactTree.height := by
  induction compactTree with
  | leaf value =>
      rfl
  | node children combine ih =>
      simp only [encodeTree, TreeEval.Tree.height_node]
      congr 2
      funext index
      exact ih index

theorem tree_value_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (h : tm.BlockRespectingOnInput x blockLength)
    (node : Node workTapeCount) :
    (tree tm x blockLength hpositive node).value =
      CompactEncoding.encode
        (CompactContent.nodeContent
          tm x blockLength hpositive node) := by
  rw [tree, encodeTree_value_internal]
  congr 1
  exact CompactTree.tree_value
    tm x blockLength hpositive h node

theorem tree_height_le_rank_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    (tree tm x blockLength hpositive node).height ≤ node.rank := by
  rw [tree, encodeTree_height_internal]
  exact CompactTree.tree_height_le_rank
    tm x blockLength hpositive node

end Internal

end BooleanTree

end ComputationGraph

end TimeSpaceSimulation

end Complexity
