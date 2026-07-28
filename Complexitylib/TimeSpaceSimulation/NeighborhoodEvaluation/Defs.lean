/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.DecisionRecovery.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodTree.Defs
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic.Decoding.Defs

/-!
# Logarithmic grouped evaluation of neighborhood trees

This module runs the logarithmic-chunk Cook--Mertz evaluator on the Boolean
tree for a neighborhood-graph node, decodes the searched-prime output, and
then decodes the compact one-hot machine value. Two such node queries produce
the state/verdict snapshot at a requested horizon.

## Main definitions

- `evaluateNode` -- grouped prime-field evaluation of one Boolean tree
- `decodedNodeBits` -- executable field and chunk decoding
- `decodedNodeContent` -- total compact-value decoding
- `evaluatedDecisionSnapshot` -- state and verdict from two evaluated roots
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodEvaluation

open NeighborhoodGraph
open TreeEval.CookMertz.PrimeGrouped

/-- Logarithmic grouped Cook--Mertz output for one neighborhood node. -/
noncomputable def evaluateNode
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    Fin (Logarithmic.chunkCount
      (NeighborhoodTree.width tm blockLength)
      (NeighborhoodTree.fanIn workTapeCount)) →
        Logarithmic.Field
          (NeighborhoodTree.width tm blockLength)
          (NeighborhoodTree.fanIn workTapeCount) :=
  Logarithmic.evaluateTree
    (NeighborhoodTree.width tm blockLength)
    (NeighborhoodTree.fanIn workTapeCount)
    (NeighborhoodTree.booleanTree
      tm x blockLength hpositive node)

/-- Decode the grouped field output to the fixed-width Boolean root value. -/
noncomputable def decodedNodeBits
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    Fin (NeighborhoodTree.width tm blockLength) → Bool :=
  Logarithmic.Decoding.decodeValue
    (NeighborhoodTree.width tm blockLength)
    (NeighborhoodTree.fanIn workTapeCount)
    (evaluateNode tm x blockLength hpositive node)

/-- Totally decode the Boolean root as a compact machine value. -/
noncomputable def decodedNodeContent
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    NeighborhoodContent.Content blockLength tm.Q :=
  ComputationGraph.CompactEncoding.decode tm.qstart hpositive
    (decodedNodeBits tm x blockLength hpositive node)

/-- Recover the horizon state and verdict from two evaluated neighborhood
roots. -/
noncomputable def evaluatedDecisionSnapshot
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (horizon : ℕ) :
    DecisionRecovery.Snapshot tm.Q :=
  { state :=
      (decodedNodeContent tm x blockLength hpositive
        (DecisionRecovery.stateNode
          tm x blockLength horizon)).state
    verdict :=
      (decodedNodeContent tm x blockLength hpositive
        (DecisionRecovery.verdictBlockNode
          tm x blockLength horizon)).cells
        (DecisionRecovery.verdictOffset
          blockLength hpositive) }

end NeighborhoodEvaluation

end TimeSpaceSimulation

end Complexity
