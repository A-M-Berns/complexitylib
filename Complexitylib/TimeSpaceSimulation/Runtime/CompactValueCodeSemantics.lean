/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.CompactValueCodeSemantics.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.CompactValueCodeSemantics.Internal

/-!
# Arithmetic coordinates of compact neighborhood values

This surface identifies the explicit natural-coordinate layout used by the
fixed state order with the evaluator's typed compact encoding.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace CompactValueCodeSemantics

open NeighborhoodExecutableEvaluation

/-- The hardwired finite-coordinate encoding is exactly the arithmetic
state/head/cell layout at every in-range payload coordinate. -/
theorem encodeBits_eq_coordinateBit
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (blockLength : ℕ)
    (value :
      ComputationGraph.CompactContent.Content blockLength tm.Q)
    (index : Fin (payloadWidth tm blockLength)) :
    encodeBits (FiniteEncoding.ofStateOrder order blockLength)
        value index =
      coordinateBit tm order blockLength index.val value :=
  Internal.encodeBits_eq_coordinateBit_internal
    tm order blockLength value index

end CompactValueCodeSemantics
end Runtime
end TimeSpaceSimulation
end Complexity
