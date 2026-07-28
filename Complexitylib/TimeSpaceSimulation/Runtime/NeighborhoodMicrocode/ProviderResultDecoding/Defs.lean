/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderQueryEvaluation.Defs

/-!
# Decoding completed provider-query results

A completed provider query leaves its logical scheduler register family in
the packed catalytic bank.  The distinguished `Fin.last` row is the queried
node value.  This module names both its logical and packed-store views and
the compact content obtained by the canonical residue decoder.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ProviderResultDecoding

open RAM Structured
open NeighborhoodExecutableEvaluation

/-- Distinguished logical residue vector returned by a completed provider
query. -/
def resultResidues
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount)) :
    ResidueValue tm instanceData.blockLength :=
  (NeighborhoodScheduler.run
    (NeighborhoodScheduler.Decision.queryInitial
      (ProviderRootInitialization.providerRoot
        instanceData interval child))).registers
    (Fin.last (graphFanIn workTapeCount))

/-- Read the distinguished scheduler row directly from a packed runtime
bank. -/
def storedResultResidues
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (store : Store) :
    ResidueValue tm instanceData.blockLength :=
  fun chunk =>
    PackedDigits.digit
      (Representation.fieldBase instanceData)
      (store regs.layout.bank)
      (NeighborhoodProgram.residueBankIndex
        tm instanceData.blockLength
        (Fin.last (graphFanIn workTapeCount)) chunk)

/-- Canonically decode the logical result of one provider query. -/
def decodedResult
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount)) :
    NeighborhoodContent.Content instanceData.blockLength tm.Q :=
  Residue.decodeValue
    tm instanceData.blockLength instanceData.encoding
      instanceData.positive
      (resultResidues tm instanceData interval child)

/-- Canonically decode the distinguished row of a packed runtime bank. -/
def decodedStoredResult
    (tm : TM workTapeCount)
    (regs : NeighborhoodTrial.Registers controller)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (store : Store) :
    NeighborhoodContent.Content instanceData.blockLength tm.Q :=
  Residue.decodeValue
    tm instanceData.blockLength instanceData.encoding
      instanceData.positive
      (storedResultResidues tm regs instanceData store)

/-- Semantic predecessor content selected by the role-major child cursor. -/
def expectedContent
    (tm : TM workTapeCount)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount)) :
    NeighborhoodContent.Content instanceData.blockLength tm.Q :=
  NeighborhoodContent.predecessorContents
    tm instanceData.x instanceData.blockLength interval.val
      instanceData.positive
      ((NeighborhoodGraph.predecessorIndexEquiv
        workTapeCount).symm child)

end ProviderResultDecoding
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
