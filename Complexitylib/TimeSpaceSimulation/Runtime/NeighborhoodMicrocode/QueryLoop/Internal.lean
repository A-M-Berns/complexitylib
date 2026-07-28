/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.QueryLoop.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodMicrocode.SchedulerStep
import Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler

/-!
# Uniform iteration of neighborhood query microsteps -- proofs
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodMicrocode
namespace QueryLoop
namespace Internal

open RAM Structured
open NeighborhoodExecutableEvaluation

private theorem cmdWritesWithin_mono
    {smaller larger : Finset ℕ} {command : Cmd}
    (hwrites : Footprint.CmdWritesWithin smaller command)
    (hsubset : smaller ⊆ larger) :
    Footprint.CmdWritesWithin larger command := by
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

private theorem layoutWritesWithin_trial
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd}
    (hwrites :
      Footprint.CmdWritesWithin regs.layout.footprint command) :
    Footprint.CmdWritesWithin regs.footprint command :=
  cmdWritesWithin_mono hwrites (by
    intro address haddress
    exact Finset.mem_union_left _ haddress)

private theorem guess_of_layout_run
    (regs : NeighborhoodTrial.Registers controller)
    {command : Cmd} {initial final : Store}
    (hwrites :
      Footprint.CmdWritesWithin regs.layout.footprint command)
    (hrun : Runs command initial final) :
    final controller.guess = initial controller.guess :=
  NeighborhoodTrial.Registers.runs_preserves_controller_index
    regs (layoutWritesWithin_trial regs hwrites) hrun
    (2 : Fin 17) (by decide) (by decide) (by decide)

theorem run_writesWithin_internal
    (tm : TM workTapeCount)
    (order : FiniteEncoding.StateOrder tm)
    (controller : SearchProgram.Registers)
    (regs : NeighborhoodTrial.Registers controller)
    (combine : Cmd)
    (hcombine :
      Footprint.CmdWritesWithin regs.layout.footprint combine) :
    Footprint.CmdWritesWithin regs.layout.footprint
      (run tm order controller regs combine) :=
  SchedulerStep.step_writesWithin
    tm order controller regs combine hcombine

theorem run_runs_internal
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
    (state : NeighborhoodScheduler.State tm instanceData)
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
    (hquery :
      Representation.QueryState regs instanceData state store)
    (hcoherent :
      NeighborhoodScheduler.Coherence.StateCoherent state)
    (hframe :
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x store)
    (hinputLength :
      store controller.inputLength = instanceData.x.length)
    (hone : store controller.one = 1) :
    ∃ final,
      Runs (run tm order controller regs combine) store final ∧
      Representation.QueryState regs instanceData
        (NeighborhoodScheduler.run state) final ∧
      SearchProgram.InputFrame
        controller regs.footprint instanceData.x final ∧
      final controller.inputLength = instanceData.x.length ∧
      final controller.one = 1 ∧
      final controller.guess = code.val := by
  induction hrank : NeighborhoodScheduler.Work.rank state using
      Nat.strong_induction_on generalizing state store with
  | h currentRank ih =>
      by_cases hterminal : state.Terminal
      · have hactiveZero :
            store (Layout.active regs) = 0 :=
          (Representation.QueryState.active_zero_iff_terminal
            regs state store hquery).2 hterminal
        have hrankZero :
            NeighborhoodScheduler.Work.rank state = 0 :=
          (NeighborhoodScheduler.Work.rank_eq_zero_iff state).2
            hterminal
        refine ⟨store, ?_, ?_, hframe, hinputLength, hone,
          hstoreGuess⟩
        · simpa [run] using Runs.whileZero hactiveZero
        · simpa [NeighborhoodScheduler.run, hrankZero] using hquery
      · have hactiveNonzero :
            store (Layout.active regs) ≠ 0 := by
          intro hzero
          exact hterminal
            ((Representation.QueryState.active_zero_iff_terminal
              regs state store hquery).1 hzero)
        have hstackNe : state.stack ≠ [] := by
          intro hempty
          apply hterminal
          simp [NeighborhoodScheduler.State.Terminal, hempty]
        obtain ⟨frame, rest, hstack⟩ :=
          List.exists_cons_of_ne_nil hstackNe
        have hstate :
            ({ stack := frame :: rest
               registers := state.registers } :
              NeighborhoodScheduler.State tm instanceData) =
                state := by
          cases state
          simp_all
        obtain ⟨afterStep, hstep, hqueryStep, hframeStep,
            hinputLengthStep, honeStep⟩ :=
          SchedulerStep.step_runs
            order controller regs combine instanceData code
            frame rest state.registers store hcombineWrites hcombine
            hencoding hguess hstoreGuess (hstate ▸ hquery)
            (hstate ▸ hcoherent) hframe hinputLength hone
        have hstepWrites :
            Footprint.CmdWritesWithin regs.layout.footprint
              (SchedulerStep.step
                tm order controller regs combine) :=
          SchedulerStep.step_writesWithin
            tm order controller regs combine hcombineWrites
        have hguessStep :
            afterStep controller.guess = code.val :=
          (guess_of_layout_run regs hstepWrites hstep).trans
            hstoreGuess
        have hcoherentStep :
            NeighborhoodScheduler.Coherence.StateCoherent
              state.next :=
          NeighborhoodScheduler.Coherence.StateCoherent.next
            state hcoherent
        have hrankLt :
            NeighborhoodScheduler.Work.rank state.next <
              currentRank := by
          rw [← hrank]
          exact NeighborhoodScheduler.schedulerRank_decreases
            state hterminal
        obtain ⟨final, hloop, hqueryFinal, hframeFinal,
            hinputLengthFinal, honeFinal, hguessFinal⟩ :=
          ih (NeighborhoodScheduler.Work.rank state.next)
            hrankLt state.next afterStep hguessStep
            (by simpa only [hstate] using hqueryStep)
            hcoherentStep hframeStep hinputLengthStep honeStep rfl
        have hrankNext :=
          NeighborhoodScheduler.Work.rank_next state hterminal
        have hrunEq :
            NeighborhoodScheduler.run state =
              NeighborhoodScheduler.run state.next := by
          rw [NeighborhoodScheduler.run, ← hrankNext,
            Function.iterate_succ_apply]
          rfl
        refine ⟨final, ?_, ?_, hframeFinal, hinputLengthFinal,
          honeFinal, hguessFinal⟩
        · simpa [run] using
            Runs.whileNonzero hactiveNonzero hstep hloop
        · simpa [hrunEq] using hqueryFinal

end Internal
end QueryLoop
end NeighborhoodMicrocode
end Runtime
end TimeSpaceSimulation
end Complexity
