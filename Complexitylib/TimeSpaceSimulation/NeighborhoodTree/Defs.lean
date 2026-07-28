/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.ComputationGraph.BooleanTree.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodContent.Defs

/-!
# Compact and Boolean trees for the neighborhood graph

This module instantiates the generic neighborhood-graph recursion with the
compact local machine transition, then transports the resulting tree through
the exact one-hot Boolean encoding.

## Main definitions

- `fanIn` -- four predecessor roles for every named tape
- `compactNodeValue` -- recursive compact graph evaluation
- `compactTree` -- the corresponding compact Tree Evaluation instance
- `booleanTree` -- its fixed-width Boolean encoding
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodTree

open NeighborhoodGraph

/-- Fixed fan-in of the arbitrary-machine neighborhood graph. -/
def fanIn (workTapeCount : ℕ) : ℕ :=
  4 * (workTapeCount + 2)

/-- Bit width of one compact state/head/block value. -/
def width (tm : TM workTapeCount) (blockLength : ℕ) : ℕ :=
  ComputationGraph.CompactEncoding.width blockLength tm.Q

/-- Compact semantic value of one source block. -/
def sourceFunction
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (block : ℕ) :
    NeighborhoodContent.Content blockLength tm.Q :=
  NeighborhoodContent.nodeContent tm x blockLength hpositive
    (.source tape block)

/-- Fixed-arity wrapper around one compact neighborhood transition. -/
def combineFunction
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (slot : Slot)
    (timeBlock : ℕ)
    (children : Fin (fanIn workTapeCount) →
      NeighborhoodContent.Content blockLength tm.Q) :
    NeighborhoodContent.Content blockLength tm.Q :=
  NeighborhoodContent.localNodeFunction
    tm x blockLength hpositive timeBlock tape slot fun index =>
      children (predecessorIndexEquiv workTapeCount index)

/-- Recursive compact evaluation of the implicit neighborhood graph. -/
def compactNodeValue
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength) :
    Node workTapeCount →
      NeighborhoodContent.Content blockLength tm.Q :=
  NeighborhoodGraph.nodeValue tm x blockLength
    (sourceFunction tm x blockLength hpositive)
    (combineFunction tm x blockLength hpositive)

/-- Fixed-arity compact Tree Evaluation instance. -/
def compactTree
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength) :
    Node workTapeCount →
      TreeEval.Tree (fanIn workTapeCount)
        (NeighborhoodContent.Content blockLength tm.Q) :=
  NeighborhoodGraph.unroll tm x blockLength
    (sourceFunction tm x blockLength hpositive)
    (combineFunction tm x blockLength hpositive)

/-- Fixed-width Boolean Tree Evaluation instance. -/
noncomputable def booleanTree
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    TreeEval.Tree (fanIn workTapeCount)
      (Fin (width tm blockLength) → Bool) :=
  ComputationGraph.BooleanTree.encodeTree
    tm.qstart hpositive
      (compactTree tm x blockLength hpositive node)

end NeighborhoodTree

end TimeSpaceSimulation

end Complexity
