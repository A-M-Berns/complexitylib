/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodEvaluation.Defs
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.DecisionRecovery
import Complexitylib.TimeSpaceSimulation.NeighborhoodTree
import
  Complexitylib.TreeEvaluation.CookMertz.PrimeGrouped.Logarithmic.Decoding

/-!
# Correctness internals for logarithmic neighborhood evaluation
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodEvaluation

open NeighborhoodGraph
open TreeEval.CookMertz.PrimeGrouped

namespace Internal

theorem decodedNodeBits_eq_encode_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    decodedNodeBits tm x blockLength hpositive node =
      ComputationGraph.CompactEncoding.encode
        (NeighborhoodContent.nodeContent
          tm x blockLength hpositive node) := by
  unfold decodedNodeBits evaluateNode
  rw [Logarithmic.Decoding.decodeValue_evaluateTree]
  exact NeighborhoodTree.booleanTree_value
    tm x blockLength hpositive node

theorem decodedNodeContent_eq_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (node : Node workTapeCount) :
    decodedNodeContent tm x blockLength hpositive node =
      NeighborhoodContent.nodeContent
        tm x blockLength hpositive node := by
  unfold decodedNodeContent
  rw [decodedNodeBits_eq_encode_internal]
  exact ComputationGraph.CompactEncoding.decode_encode
    tm.qstart hpositive
      (NeighborhoodContent.nodeContent
        tm x blockLength hpositive node)

theorem evaluatedDecisionSnapshot_eq_internal
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (horizon : ℕ) :
    evaluatedDecisionSnapshot
        tm x blockLength hpositive horizon =
      DecisionRecovery.decisionSnapshot
        tm x blockLength hpositive horizon := by
  apply DecisionRecovery.Snapshot.ext
  · exact congrArg
      ComputationGraph.CompactContent.Content.state
      (decodedNodeContent_eq_internal
        tm x blockLength hpositive
          (DecisionRecovery.stateNode
            tm x blockLength horizon))
  · exact congrFun
      (congrArg
        ComputationGraph.CompactContent.Content.cells
        (decodedNodeContent_eq_internal
          tm x blockLength hpositive
            (DecisionRecovery.verdictBlockNode
              tm x blockLength horizon)))
      (DecisionRecovery.verdictOffset
        blockLength hpositive)

theorem evaluatedDecisionSnapshot_eq_of_reachesIn_internal
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
        verdict := cfg.output.cells 1 } := by
  rw [evaluatedDecisionSnapshot_eq_internal]
  exact DecisionRecovery.decisionSnapshot_eq_of_reachesIn
    tm x blockLength horizon haltTime hpositive
      cfg hreach hhalt hle

end Internal

end NeighborhoodEvaluation

end TimeSpaceSimulation

end Complexity
