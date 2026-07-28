/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.NeighborhoodContent.Defs
import Complexitylib.TimeSpaceSimulation.NeighborhoodContent.Internal

/-!
# Compact semantic values for the three-block neighborhood graph

The local node function reconstructs only the three blocks around every
interval-start head. Direct head-movement locality makes this enough for an
arbitrary deterministic machine: on actual predecessor values, one local
interval computes exactly the compact semantic value of the target node.

## Main results

- `tapeFromNeighborhood_agreement` -- exact local tape reconstruction
- `nodeContent_contentPredecessor_cells` -- historical edges carry current data
- `predecessorCfg_eq_localizedCfg` -- actual inputs rebuild the local start
- `localNodeFunction_semantic` -- the compact local function is correct
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NeighborhoodContent

open NeighborhoodGraph

/-- Reconstructing a tape from its actual lower, center, and upper blocks
preserves the head and all cells in that neighborhood. -/
theorem tapeFromNeighborhood_agreement
    (blockLength center : ℕ) (hpositive : 0 < blockLength)
    (tape : Tape) :
    TapeNeighborhoodAgreement blockLength center tape
      (tapeFromNeighborhood blockLength center tape.head
        (fun slot =>
          blockContents tape blockLength
            (neighborBlock center slot))) :=
  Internal.tapeFromNeighborhood_agreement_internal
    blockLength center hpositive tape

/-- Canonically restricting every named tape to its three starting blocks
preserves exactly the local data required for one interval. -/
theorem cfg_localized_agreement
    (blockLength : ℕ) (hpositive : 0 < blockLength)
    (cfg : Cfg workTapeCount Q) :
    CfgThreeBlockAgreement blockLength cfg
      (localizedCfg blockLength cfg) :=
  Internal.cfg_localized_agreement_internal
    blockLength hpositive cfg

/-- Select one named-tape component of configuration-neighborhood
agreement. -/
theorem CfgNeighborhoodAgreement.tapeAt
    {blockLength : ℕ}
    {centers : TapeIndex workTapeCount → ℕ}
    {left right : Cfg workTapeCount Q}
    (h : CfgNeighborhoodAgreement blockLength centers left right)
    (tape : TapeIndex workTapeCount) :
    TapeNeighborhoodAgreement blockLength (centers tape)
      (tapeAt left tape) (tapeAt right tape) :=
  Internal.cfgNeighborhoodAgreement_tapeAt_internal h tape

/-- A chronological edge is sampled at the target interval's start. -/
theorem nodeConfigurationTime_chronologicalPredecessor
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ)
    (tape : TapeIndex workTapeCount) :
    nodeConfigurationTime blockLength
        (chronologicalPredecessor
          tm x blockLength timeBlock tape) =
      timeBlockStart blockLength timeBlock :=
  Internal.nodeConfigurationTime_chronologicalPredecessor_internal
    tm x blockLength timeBlock tape

/-- A chronological edge carries the real interval-start state. -/
theorem nodeContent_chronologicalPredecessor_state
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) :
    (nodeContent tm x blockLength hpositive
      (chronologicalPredecessor
        tm x blockLength timeBlock tape)).state =
      (tm.configurationAt x
        (timeBlockStart blockLength timeBlock)).state :=
  Internal.nodeContent_chronologicalPredecessor_state_internal
    tm x blockLength timeBlock hpositive tape

/-- A chronological edge carries the real interval-start head remainder. -/
theorem nodeContent_chronologicalPredecessor_headRemainder
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) :
    (nodeContent tm x blockLength hpositive
      (chronologicalPredecessor tm x blockLength
        timeBlock tape)).headRemainder.val =
      (tapeAt
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock))
        tape).head % blockLength :=
  Internal.nodeContent_chronologicalPredecessor_headRemainder_internal
    tm x blockLength timeBlock hpositive tape

/-- A greatest-prior content edge carries the requested block exactly as it
appears at the target interval's start. -/
theorem nodeContent_contentPredecessor_cells
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (hpositive : 0 < blockLength)
    (tape : TapeIndex workTapeCount) (slot : Slot) :
    (nodeContent tm x blockLength hpositive
      (contentPredecessor tm x blockLength
        timeBlock tape slot)).cells =
      ComputationGraph.blockContentsAt tm x blockLength
        (timeBlockStart blockLength timeBlock) tape
        (requestedBlock tm x blockLength timeBlock tape slot) :=
  Internal.nodeContent_contentPredecessor_cells_internal
    tm x blockLength timeBlock hpositive tape slot

/-- Supplying all actual predecessor values reconstructs the canonical
three-block localization of the real interval-start configuration. -/
theorem predecessorCfg_eq_localizedCfg
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (hpositive : 0 < blockLength) :
    predecessorCfg tm x blockLength timeBlock
        (predecessorContents tm x blockLength
          timeBlock hpositive) =
      localizedCfg blockLength
        (tm.configurationAt x
          (timeBlockStart blockLength timeBlock)) :=
  Internal.predecessorCfg_eq_localizedCfg_internal
    tm x blockLength timeBlock hpositive

/-- On actual compact predecessor values, executing one local interval
returns exactly the target neighborhood node's compact semantic value. -/
theorem localNodeFunction_semantic
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength timeBlock : ℕ) (hpositive : 0 < blockLength)
    (targetTape : TapeIndex workTapeCount) (targetSlot : Slot) :
    localNodeFunction tm x blockLength hpositive
        timeBlock targetTape targetSlot
        (predecessorContents tm x blockLength
          timeBlock hpositive) =
      nodeContent tm x blockLength hpositive
        (.computation targetTape targetSlot timeBlock) :=
  Internal.localNodeFunction_semantic_internal
    tm x blockLength timeBlock hpositive targetTape targetSlot

end NeighborhoodContent

end TimeSpaceSimulation

end Complexity
