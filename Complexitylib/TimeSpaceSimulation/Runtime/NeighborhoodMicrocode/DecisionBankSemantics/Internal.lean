/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodExecutableEvaluation
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.DecisionBankSemantics.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler

/-!
# Correctness internals for the retained two-query catalytic bank
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace DecisionBankSemantics
namespace Internal

open NeighborhoodExecutableEvaluation NeighborhoodEvaluator
open TreeEval CookMertz

variable {workTapeCount : ℕ}
variable {tm : TM workTapeCount}

private theorem zeroRegisters_canonical
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    ∀ register chunk,
      NeighborhoodScheduler.Decision.zeroRegisters
          (instanceData := instanceData) register chunk <
        modulus tm instanceData.blockLength := by
  intro register chunk
  exact PrimeField.Runtime.normalize_lt
    (PrimeField.Search.searchModulus_prime _).pos

private theorem addScaledOne_zero
    (tm : TM workTapeCount) (blockLength : ℕ)
    (value : ResidueValue tm blockLength)
    (hvalue :
      ∀ chunk, value chunk < modulus tm blockLength) :
    Residue.addValue tm blockLength
        (Residue.zeroValue tm blockLength)
        (Residue.scaleValue tm blockLength
          (PrimeField.Runtime.normalize
            (modulus tm blockLength) 1)
          value) =
      value := by
  funext chunk
  have hp :
      1 < modulus tm blockLength :=
    (PrimeField.Search.searchModulus_prime _).one_lt
  simp [Residue.addValue, Residue.zeroValue,
    Residue.scaleValue, PrimeField.Runtime.add,
    PrimeField.Runtime.addInput, PrimeField.Runtime.mul,
    PrimeField.Runtime.mulInput, PrimeField.Runtime.normalize,
    Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt (hvalue chunk)]

private theorem last_ne_verdictOutput (workTapeCount : ℕ) :
    Fin.last (graphFanIn workTapeCount) ≠
      verdictOutput workTapeCount := by
  intro heq
  have hval := congrArg Fin.val heq
  simp [verdictOutput, NeighborhoodEvaluator.fanIn] at hval

theorem stateBank_last_internal
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    stateBank instanceData (Fin.last (graphFanIn workTapeCount)) =
      (Residue.profileDecision
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess).result.1 := by
  unfold stateBank stateInitial
    NeighborhoodScheduler.Decision.queryInitial
    NeighborhoodScheduler.Decision.zeroRegisters
  rw [NeighborhoodScheduler.schedulerRun_profileEvaluate]
  rfl

private theorem stateBank_eq_addAt
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    stateBank instanceData =
      Residue.addAt tm instanceData.blockLength
        NeighborhoodScheduler.Decision.zeroRegisters
        (Fin.last (graphFanIn workTapeCount))
        (Residue.scaleValue tm instanceData.blockLength
          (PrimeField.Runtime.normalize
            (NeighborhoodScheduler.fieldModulus instanceData) 1)
          (Residue.profileEvaluate
            tm instanceData.x instanceData.blockLength
            instanceData.encoding instanceData.positive
            instanceData.horizon instanceData.guess
            instanceData.horizon
            (NeighborhoodEvaluator.stateRoot
              instanceData.guess)).result) := by
  unfold stateBank stateInitial
    NeighborhoodScheduler.Decision.queryInitial
  rw [NeighborhoodScheduler.schedulerRun_profileAccumulate]
  exact Residue.profileAccumulate_result
    tm instanceData.x instanceData.blockLength
      instanceData.encoding instanceData.positive
      instanceData.horizon instanceData.guess
      instanceData.horizon
      (NeighborhoodEvaluator.stateRoot instanceData.guess)
      (PrimeField.Runtime.normalize
        (NeighborhoodScheduler.fieldModulus instanceData) 1)
      (Fin.last (graphFanIn workTapeCount))
      NeighborhoodScheduler.Decision.zeroRegisters
      (zeroRegisters_canonical instanceData)

theorem stateBank_eq_zero_of_ne_internal
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (register : Fin (graphFanIn workTapeCount + 1))
    (hne : register ≠ Fin.last (graphFanIn workTapeCount)) :
    stateBank instanceData register =
      Residue.zeroValue tm instanceData.blockLength := by
  rw [stateBank_eq_addAt instanceData]
  simp [Residue.addAt, hne,
    NeighborhoodScheduler.Decision.zeroRegisters]

theorem stateBank_canonical_internal
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    ∀ register chunk,
      stateBank instanceData register chunk <
        modulus tm instanceData.blockLength := by
  unfold stateBank stateInitial
    NeighborhoodScheduler.Decision.queryInitial
  rw [NeighborhoodScheduler.schedulerRun_profileAccumulate]
  exact Residue.profileAccumulate_canonical
    tm instanceData.x instanceData.blockLength
      instanceData.encoding instanceData.positive
      instanceData.horizon instanceData.guess
      instanceData.horizon
      (NeighborhoodEvaluator.stateRoot instanceData.guess)
      (PrimeField.Runtime.normalize
        (NeighborhoodScheduler.fieldModulus instanceData) 1)
      (Fin.last (graphFanIn workTapeCount))
      NeighborhoodScheduler.Decision.zeroRegisters
      (zeroRegisters_canonical instanceData)

private theorem decisionBank_eq_addAt
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    decisionBank instanceData =
      Residue.addAt tm instanceData.blockLength
        (stateBank instanceData)
        (verdictOutput workTapeCount)
        (Residue.scaleValue tm instanceData.blockLength
          (PrimeField.Runtime.normalize
            (NeighborhoodScheduler.fieldModulus instanceData) 1)
          (Residue.profileEvaluate
            tm instanceData.x instanceData.blockLength
            instanceData.encoding instanceData.positive
            instanceData.horizon instanceData.guess
            instanceData.horizon
            (NeighborhoodEvaluator.verdictRoot
              instanceData.guess
              instanceData.blockLength)).result) := by
  unfold decisionBank verdictInitial
  rw [NeighborhoodScheduler.schedulerRun_profileAccumulate]
  exact Residue.profileAccumulate_result
    tm instanceData.x instanceData.blockLength
      instanceData.encoding instanceData.positive
      instanceData.horizon instanceData.guess
      instanceData.horizon
      (NeighborhoodEvaluator.verdictRoot
        instanceData.guess instanceData.blockLength)
      (PrimeField.Runtime.normalize
        (NeighborhoodScheduler.fieldModulus instanceData) 1)
      (verdictOutput workTapeCount)
      (stateBank instanceData)
      (stateBank_canonical_internal instanceData)

theorem decisionBank_last_internal
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    decisionBank instanceData (Fin.last (graphFanIn workTapeCount)) =
      (Residue.profileDecision
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess).result.1 := by
  rw [decisionBank_eq_addAt instanceData]
  rw [Residue.addAt, Function.update_of_ne
    (last_ne_verdictOutput workTapeCount)]
  exact stateBank_last_internal instanceData

theorem decisionBank_verdict_internal
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    decisionBank instanceData (verdictOutput workTapeCount) =
      (Residue.profileDecision
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess).result.2 := by
  rw [decisionBank_eq_addAt instanceData]
  simp only [Residue.addAt, Function.update_self]
  rw [stateBank_eq_zero_of_ne_internal instanceData
    (verdictOutput workTapeCount)
    (Ne.symm (last_ne_verdictOutput workTapeCount))]
  simpa [NeighborhoodScheduler.fieldModulus,
    Residue.profileDecision] using
      addScaledOne_zero
        tm instanceData.blockLength
        (Residue.profileEvaluate
          tm instanceData.x instanceData.blockLength
          instanceData.encoding instanceData.positive
          instanceData.horizon instanceData.guess
          instanceData.horizon
          (NeighborhoodEvaluator.verdictRoot
            instanceData.guess instanceData.blockLength)).result
        (Residue.profileEvaluate_canonical
          tm instanceData.x instanceData.blockLength
          instanceData.encoding instanceData.positive
          instanceData.horizon instanceData.guess
          instanceData.horizon
          (NeighborhoodEvaluator.verdictRoot
            instanceData.guess instanceData.blockLength))

theorem decisionResult_eq_profileDecision_internal
    (instanceData : NeighborhoodProgram.ResidueInstance tm) :
    decisionResult instanceData =
      (Residue.profileDecision
        tm instanceData.x instanceData.blockLength
        instanceData.encoding instanceData.positive
        instanceData.horizon instanceData.guess).result := by
  apply Prod.ext
  · exact decisionBank_last_internal instanceData
  · exact decisionBank_verdict_internal instanceData

end Internal
end DecisionBankSemantics
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
