/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactEncoding.Defs
import Complexitylib.TimeSpaceSimulation.ComputationGraph.CompactTree.Defs

/-!
# Boolean encoding of compact computation trees

This file transports an arbitrary compact-value tree to a fixed-width Boolean
tree. Leaves are one-hot encoded. At each internal node, child vectors are
decoded, the original compact combining function is run, and its result is
encoded again. Decoding is total, so the Boolean node function is defined on
every bit vector, including malformed encodings.

## Main definitions

- `encodeTree` -- generic compact-to-Boolean tree transport
- `tree` -- Boolean tree for one computation-graph node
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace ComputationGraph

namespace BooleanTree

/-- Transport a compact-value tree to its fixed-width Boolean encoding. -/
noncomputable def encodeTree
    [Fintype Q] [DecidableEq Q]
    (defaultState : Q) (hpositive : 0 < blockLength) :
    TreeEval.Tree d (CompactContent.Content blockLength Q) →
      TreeEval.Tree d
        (Fin (CompactEncoding.width blockLength Q) → Bool)
  | .leaf value =>
      .leaf (CompactEncoding.encode value)
  | .node children combine =>
      .node
        (fun index =>
          encodeTree defaultState hpositive (children index))
        (fun inputs =>
          CompactEncoding.encode
            (combine fun index =>
              CompactEncoding.decode defaultState hpositive
                (inputs index)))

/-- Fixed-width Boolean Tree Evaluation instance for one compact computation
tree. -/
noncomputable def tree
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    TreeEval.Tree (2 * (workTapeCount + 2))
      (Fin (CompactEncoding.width blockLength tm.Q) → Bool) :=
  encodeTree tm.qstart hpositive
    (CompactTree.tree tm x blockLength hpositive node)

end BooleanTree

end ComputationGraph

end TimeSpaceSimulation

end Complexity
