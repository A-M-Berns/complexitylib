/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodEvaluation.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodEvaluation.Internal

/-!
# Correct logarithmic grouped evaluation of neighborhood trees

The searched-prime Cook--Mertz evaluator, executable residue decoder, and
total compact decoder recover the actual semantic value of every direct
neighborhood-graph node. Evaluating the two decision roots therefore returns
the exact state and output symbol of any halted source configuration covered
by the chosen horizon.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodEvaluation

open NeighborhoodGraph

/-- Decoded grouped evaluation equals the exact Boolean encoding of the
actual compact node value. -/
theorem decodedNodeBits_eq_encode
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    decodedNodeBits tm x blockLength hpositive node =
      ComputationGraph.CompactEncoding.encode
        (NeighborhoodContent.nodeContent
          tm x blockLength hpositive node) :=
  Internal.decodedNodeBits_eq_encode_internal
    tm x blockLength hpositive node

/-- Total compact decoding recovers the actual semantic node value. -/
theorem decodedNodeContent_eq
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    decodedNodeContent tm x blockLength hpositive node =
      NeighborhoodContent.nodeContent
        tm x blockLength hpositive node :=
  Internal.decodedNodeContent_eq_internal
    tm x blockLength hpositive node

/-- The two grouped-evaluation queries equal the semantic horizon snapshot. -/
theorem evaluatedDecisionSnapshot_eq
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (horizon : ℕ) :
    evaluatedDecisionSnapshot
        tm x blockLength hpositive horizon =
      DecisionRecovery.decisionSnapshot
        tm x blockLength hpositive horizon :=
  Internal.evaluatedDecisionSnapshot_eq_internal
    tm x blockLength hpositive horizon

/-- If a halted source run is covered by the horizon, the two decoded
Cook--Mertz queries recover exactly its state and verdict cell. -/
theorem evaluatedDecisionSnapshot_eq_of_reachesIn
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon haltTime : ℕ)
    (hpositive : 0 < blockLength)
    (cfg : Cfg workTapeCount tm.Q)
    (hreach : tm.reachesIn haltTime (tm.initCfg x) cfg)
    (hhalt : tm.halted cfg)
    (hle :
      haltTime ≤ timeBlockStart blockLength horizon) :
    evaluatedDecisionSnapshot
        tm x blockLength hpositive horizon =
      { state := cfg.state
        verdict := cfg.output.cells 1 } :=
  Internal.evaluatedDecisionSnapshot_eq_of_reachesIn_internal
    tm x blockLength horizon haltTime hpositive
      cfg hreach hhalt hle

end NeighborhoodEvaluation

end TimeSpaceSimulation

end Complexity
