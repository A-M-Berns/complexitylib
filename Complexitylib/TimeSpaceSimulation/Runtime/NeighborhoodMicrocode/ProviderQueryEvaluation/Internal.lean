/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderQueryEvaluation.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.ProviderRootInitialization
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryLoop

/-!
# Complete uniform evaluation of one consistency-provider coordinate -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace ProviderQueryEvaluation
namespace Internal

open RAM Structured
open NeighborhoodExecutableEvaluation

private theorem cmdWritesWithin_mono
    {small large : Finset ℕ} {command : Cmd}
    (hwrites : Footprint.CmdWritesWithin small command)
    (hsubset : small ⊆ large) :
    Footprint.CmdWritesWithin large command := by
  induction command with
  | skip =>
      trivial
  | basic operation =>
      cases operation <;>
        simp only [Footprint.CmdWritesWithin,
          Footprint.BasicWritesWithin] at hwrites ⊢
      all_goals exact hsubset hwrites
  | seq first second ihFirst ihSecond =>
      exact ⟨ihFirst hwrites.1, ihSecond hwrites.2⟩
  | ifZero test onZero onNonzero ihZero ihNonzero =>
      exact ⟨ihZero hwrites.1, ihNonzero hwrites.2⟩
  | whileNonzero test body ih =>
      exact ih hwrites

theorem evaluate_writesWithin_internal
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (hcombine :
      Footprint.CmdWritesWithin regs.layout.footprint combine) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (evaluate tm order controller regs combine) :=
  ⟨ProviderRootInitialization.initializeProviderQuery_writesWithin
      workTapeCount controller regs,
    QueryLoop.run_writesWithin
      tm order controller regs combine hcombine⟩

theorem evaluate_runs_internal
    {tm : TM workTapeCount}
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (instanceData : NeighborhoodProgram.ResidueInstance tm)
    (code :
      Fin
        (3 ^
          NeighborhoodGraph.Guess.Enumeration.movementCount
            workTapeCount instanceData.horizon))
    (interval : Fin instanceData.horizon)
    (child : Fin (graphFanIn workTapeCount))
    (store : Store)
    (hcombineWrites :
      Footprint.CmdWritesWithin regs.layout.footprint combine)
    (hcombine : SchedulerStep.CombineSpec tm order regs combine)
    (hencoding :
      instanceData.encoding =
        FiniteEncoding.ofStateOrder order instanceData.blockLength)
    (hguess :
      instanceData.guess =
        NeighborhoodGraph.Guess.Enumeration.candidateGuess code)
    (hstoreGuess : store controller.guess = code.val)
    (hstoreInterval : store controller.success = interval.val)
    (hstoreChild : store controller.verdict = child.val)
    (hparameters :
      Representation.Parameters regs instanceData store)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (evaluate tm order controller regs combine) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.run
          (NeighborhoodScheduler.Decision.queryInitial
            (ProviderRootInitialization.providerRoot
              instanceData interval child)))
        final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = code.val ∧
      final controller.success = interval.val ∧
      final controller.verdict = child.val := by
  obtain ⟨initialized, hinitialize, hquery, hframeInitialized,
      hinputLengthInitialized, honeInitialized, hguessInitialized,
      hintervalInitialized, hchildInitialized⟩ :=
    ProviderRootInitialization.initializeProviderQuery_runs_preserving_abi
      controller regs instanceData code interval child store
      hguess hstoreGuess hstoreInterval hstoreChild hparameters
      hframe hinputLength hone
  have hcoherent :
      NeighborhoodScheduler.Coherence.StateCoherent
        (NeighborhoodScheduler.Decision.queryInitial
          (ProviderRootInitialization.providerRoot
            instanceData interval child)) :=
    NeighborhoodScheduler.Coherence.stateCoherent_initial
      instanceData.horizon
      (ProviderRootInitialization.providerRoot
        instanceData interval child)
      (TreeEval.CookMertz.PrimeField.Runtime.normalize
        (NeighborhoodScheduler.fieldModulus instanceData) 1)
      (Fin.last (graphFanIn workTapeCount))
      NeighborhoodScheduler.Decision.zeroRegisters
  obtain ⟨final, hloop, hqueryFinal, hframeFinal,
      hinputLengthFinal, honeFinal, hguessFinal⟩ :=
    QueryLoop.run_runs
      order controller regs combine instanceData code
      (NeighborhoodScheduler.Decision.queryInitial
        (ProviderRootInitialization.providerRoot
          instanceData interval child))
      initialized hcombineWrites hcombine hencoding hguess
      hguessInitialized hquery hcoherent hframeInitialized
      hinputLengthInitialized honeInitialized
  have hcontroller (slot : Fin 17) :
      final (controller.index slot) =
        initialized (controller.index slot) := by
    apply Footprint.runs_eq_outside
      (QueryLoop.run_writesWithin
        tm order controller regs combine hcombineWrites)
      hloop
    exact fun hlayout =>
      Finset.disjoint_left.mp
        (NeighborhoodTrial.Registers.layout_disjoint_controller regs)
        hlayout (controller.index_mem_footprint slot)
  exact
    ⟨final, by
      simpa [evaluate] using Runs.seq hinitialize hloop,
      hqueryFinal, hframeFinal, hinputLengthFinal, honeFinal,
      hguessFinal,
      (hcontroller 3).trans hintervalInitialized,
      (hcontroller 4).trans hchildInitialized⟩

end Internal
end ProviderQueryEvaluation
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
