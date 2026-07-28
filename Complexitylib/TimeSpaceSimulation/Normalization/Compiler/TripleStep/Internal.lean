/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Internal
import Complexitylib.TimeSpaceSimulation.Normalization.Compiler.TripleStep.Defs

/-!
# Correctness of the three-microstep normalization compiler

This file proves exact tape restoration, one-source-step simulation, lifted
run simulation, and length-three block residence.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace NormalizationCompiler

open TM

variable {workTapeCount : ℕ} {Q : Type}

@[simp] theorem namedRead_input_internal (inputHead : Γ)
    (workHeads : Fin workTapeCount → Γ) (outputHead : Γ) :
    namedRead inputHead workHeads outputHead (TapeIndex.input workTapeCount) =
      inputHead := by
  simp [namedRead, TapeIndex.input]

@[simp] theorem namedRead_work_internal (inputHead : Γ)
    (workHeads : Fin workTapeCount → Γ) (outputHead : Γ)
    (index : Fin workTapeCount) :
    namedRead inputHead workHeads outputHead (TapeIndex.work index) =
      workHeads index := by
  have hne : index.val ≠ workTapeCount := Nat.ne_of_lt index.isLt
  simp [namedRead, TapeIndex.work, hne]

@[simp] theorem namedRead_output_internal (inputHead : Γ)
    (workHeads : Fin workTapeCount → Γ) (outputHead : Γ) :
    namedRead inputHead workHeads outputHead (TapeIndex.output workTapeCount) =
      outputHead := by
  simp [namedRead, TapeIndex.output]

@[simp] theorem originFlags_input_internal (inputHead : Γ)
    (workHeads : Fin workTapeCount → Γ) (outputHead : Γ) :
    originFlags inputHead workHeads outputHead (TapeIndex.input workTapeCount) =
      decide (inputHead = Γ.start) := by
  simp [originFlags]

@[simp] theorem originFlags_work_internal (inputHead : Γ)
    (workHeads : Fin workTapeCount → Γ) (outputHead : Γ)
    (index : Fin workTapeCount) :
    originFlags inputHead workHeads outputHead (TapeIndex.work index) =
      decide (workHeads index = Γ.start) := by
  simp [originFlags]

@[simp] theorem originFlags_output_internal (inputHead : Γ)
    (workHeads : Fin workTapeCount → Γ) (outputHead : Γ) :
    originFlags inputHead workHeads outputHead (TapeIndex.output workTapeCount) =
      decide (outputHead = Γ.start) := by
  simp [originFlags]

theorem bounceOutTape_eq_move_internal (tape : Tape)
    (hinvariant : tape.StartInvariant) :
    bounceOutTape tape = tape.move (TM.idleDir tape.read) := by
  by_cases hhead : tape.head = 0
  · simp [bounceOutTape, Tape.writeAndMove, Tape.write, hhead]
  · have hpositive : 1 ≤ tape.head := by omega
    have hread : tape.read ≠ Γ.start :=
      hinvariant.read_ne_start hpositive
    exact TM.writeAndMove_readBack tape hread _

theorem move_idle_read_ne_start_internal (tape : Tape)
    (hinvariant : tape.StartInvariant) :
    (tape.move (TM.idleDir tape.read)).read ≠ Γ.start := by
  by_cases hhead : tape.head = 0
  · have hread : tape.read = Γ.start := by
      simp [Tape.read, hhead, hinvariant.1]
    have hfirst :
        tape.move (TM.idleDir tape.read) = { tape with head := 1 } := by
      apply Tape.ext
      · simp [TM.idleDir, hread, Tape.move, hhead]
      · simp [Tape.move_cells]
    rw [hfirst]
    simpa [Tape.read] using hinvariant.2 1 (by omega)
  · have hpositive : 1 ≤ tape.head := by omega
    have hread : tape.read ≠ Γ.start :=
      hinvariant.read_ne_start hpositive
    simp [TM.idleDir, hread, Tape.move]

theorem move_bounce_restore_internal (tape : Tape)
    (hinvariant : tape.StartInvariant) :
    ((tape.move (TM.idleDir tape.read)).move
      (bounceBackDir (decide (tape.read = Γ.start))
        (tape.move (TM.idleDir tape.read)).read)) = tape := by
  by_cases hhead : tape.head = 0
  · have hread : tape.read = Γ.start := by
      simp [Tape.read, hhead, hinvariant.1]
    have hfirst :
        tape.move (TM.idleDir tape.read) = { tape with head := 1 } := by
      apply Tape.ext
      · simp [TM.idleDir, hread, Tape.move, hhead]
      · simp [Tape.move_cells]
    have hnextRead : ({ tape with head := 1 } : Tape).read ≠ Γ.start := by
      simpa [Tape.read] using hinvariant.2 1 (by omega)
    rw [hfirst]
    have horigin : decide (tape.read = Γ.start) = true := by
      simp [hread]
    rw [horigin]
    apply Tape.ext
    · simp [bounceBackDir, hnextRead, Tape.move, hhead]
    · simp [Tape.move_cells]
  · have hpositive : 1 ≤ tape.head := by omega
    have hread : tape.read ≠ Γ.start :=
      hinvariant.read_ne_start hpositive
    simp [TM.idleDir, hread, bounceBackDir, Tape.move]

theorem bounceBackTape_bounceOutTape_internal (tape : Tape)
    (hinvariant : tape.StartInvariant) :
    bounceBackTape (decide (tape.read = Γ.start)) (bounceOutTape tape) =
      tape := by
  rw [bounceOutTape_eq_move_internal tape hinvariant]
  unfold bounceBackTape
  rw [TM.writeAndMove_readBack _
    (move_idle_read_ne_start_internal tape hinvariant)]
  exact move_bounce_restore_internal tape hinvariant

theorem cfgStartInvariant_init_internal (source : TM workTapeCount)
    (x : List Bool) :
    CfgStartInvariant (source.initCfg x) := by
  exact source.toNTM.trace_initCfg_startInvariant x 0 (fun i => i.elim0)

theorem cfgStartInvariant_of_step_internal (source : TM workTapeCount)
    {cfg cfg' : Cfg workTapeCount source.Q}
    (hinvariant : CfgStartInvariant cfg)
    (hstep : source.step cfg = some cfg') :
    CfgStartInvariant cfg' := by
  have hne : cfg.state ≠ source.qhalt :=
    source.state_ne_qhalt_of_step hstep
  simp only [TM.step, hne, ↓reduceIte] at hstep
  obtain ⟨rfl, rfl, rfl, rfl⟩ := Option.some.inj hstep
  exact ⟨hinvariant.1.move _,
    fun i => (hinvariant.2.1 i).writeAndMove _ _,
    hinvariant.2.2.writeAndMove _ _⟩

theorem tripleStepTM_step_boundaryCfg_internal
    (source : TM workTapeCount)
    (cfg : Cfg workTapeCount source.Q)
    (hne : cfg.state ≠ source.qhalt) :
    source.tripleStepTM.step (boundaryCfg source cfg) =
      some (phase1Cfg source cfg) := by
  simp [TM.step, boundaryCfg, wrapState, hne, TM.tripleStepTM,
    phase1Cfg, bounceOutTape]

theorem tripleStepTM_step_phase1Cfg_internal
    (source : TM workTapeCount)
    (cfg : Cfg workTapeCount source.Q)
    (hinvariant : CfgStartInvariant cfg) :
    source.tripleStepTM.step (phase1Cfg source cfg) =
      some (phase2Cfg source cfg) := by
  simp only [TM.step, phase1Cfg, phase2Cfg, TM.tripleStepTM,
    reduceCtorEq, ↓reduceIte, originFlags_input_internal,
    originFlags_work_internal, originFlags_output_internal]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · exact move_bounce_restore_internal cfg.input hinvariant.1
  · funext i
    exact bounceBackTape_bounceOutTape_internal
      (cfg.work i) (hinvariant.2.1 i)
  · exact bounceBackTape_bounceOutTape_internal
      cfg.output hinvariant.2.2

theorem tripleStepTM_step_phase2Cfg_internal
    (source : TM workTapeCount)
    {cfg cfg' : Cfg workTapeCount source.Q}
    (hstep : source.step cfg = some cfg') :
    source.tripleStepTM.step (phase2Cfg source cfg) =
      some (boundaryCfg source cfg') := by
  have hne : cfg.state ≠ source.qhalt :=
    source.state_ne_qhalt_of_step hstep
  simp only [TM.step, hne, ↓reduceIte] at hstep
  simp only [TM.step, phase2Cfg, TM.tripleStepTM, reduceCtorEq,
    ↓reduceIte, hne]
  obtain ⟨rfl, rfl, rfl, rfl⟩ := Option.some.inj hstep
  rfl

theorem tripleStepTM_reachesIn_three_internal
    (source : TM workTapeCount)
    {cfg cfg' : Cfg workTapeCount source.Q}
    (hinvariant : CfgStartInvariant cfg)
    (hstep : source.step cfg = some cfg') :
    source.tripleStepTM.reachesIn 3
      (boundaryCfg source cfg) (boundaryCfg source cfg') := by
  exact .step
    (tripleStepTM_step_boundaryCfg_internal source cfg
      (source.state_ne_qhalt_of_step hstep))
    (.step (tripleStepTM_step_phase1Cfg_internal source cfg hinvariant)
      (.step (tripleStepTM_step_phase2Cfg_internal source hstep) .zero))

theorem tripleStepTM_reachesIn_boundaryCfg_internal
    (source : TM workTapeCount)
    {time : ℕ} {cfg cfg' : Cfg workTapeCount source.Q}
    (hinvariant : CfgStartInvariant cfg)
    (hreach : source.reachesIn time cfg cfg') :
    source.tripleStepTM.reachesIn (3 * time)
      (boundaryCfg source cfg) (boundaryCfg source cfg') := by
  induction hreach with
  | zero => exact .zero
  | step hstep htail ih =>
      have hmiddleInvariant :=
        cfgStartInvariant_of_step_internal source hinvariant hstep
      have hfirst :=
        tripleStepTM_reachesIn_three_internal source hinvariant hstep
      have hrest := ih hmiddleInvariant
      simpa [Nat.mul_succ, Nat.add_comm] using
        source.tripleStepTM.reachesIn_trans hfirst hrest

@[simp] theorem boundaryCfg_init_internal (source : TM workTapeCount)
    (x : List Bool) :
    boundaryCfg source (source.initCfg x) =
      source.tripleStepTM.initCfg x := rfl

@[simp] theorem boundaryCfg_halted_iff_internal
    (source : TM workTapeCount)
    (cfg : Cfg workTapeCount source.Q) :
    source.tripleStepTM.halted (boundaryCfg source cfg) ↔
      source.halted cfg := by
  change
    (if cfg.state = source.qhalt then TripleStepState.halt
      else TripleStepState.phase0 cfg.state) =
        TripleStepState.halt ↔ cfg.state = source.qhalt
  simp

theorem tripleStepTM_reachesIn_init_internal
    (source : TM workTapeCount) (x : List Bool)
    {time : ℕ} {cfg : Cfg workTapeCount source.Q}
    (hreach : source.reachesIn time (source.initCfg x) cfg) :
    source.tripleStepTM.reachesIn (3 * time)
      (source.tripleStepTM.initCfg x) (boundaryCfg source cfg) := by
  rw [← boundaryCfg_init_internal]
  exact tripleStepTM_reachesIn_boundaryCfg_internal source
    (cfgStartInvariant_init_internal source x) hreach

private theorem toNTM_trace_step_exact_internal
    (machine : TM workTapeCount)
    {cfg : Cfg workTapeCount machine.Q} (time : ℕ)
    (choices : Fin (time + 1) → Bool)
    (hne : cfg.state ≠ machine.qhalt) :
    machine.toNTM.trace (time + 1) choices cfg =
      machine.toNTM.trace time
        (fun i => choices ⟨i.val + 1, by omega⟩)
        ((machine.step cfg).get (by simp [TM.step, hne])) := by
  simp [NTM.trace, hne, TM.toNTM, TM.step]

theorem toNTM_trace_of_reachesIn_exact_internal
    (machine : TM workTapeCount)
    {cfg cfg' : Cfg workTapeCount machine.Q} {time : ℕ}
    (hreach : machine.reachesIn time cfg cfg')
    (choices : Fin time → Bool) :
    machine.toNTM.trace time choices cfg = cfg' := by
  induction hreach with
  | zero => rfl
  | @step cfg₀ cfgMiddle time cfgFinal hstep htail ih =>
      have hne := machine.state_ne_qhalt_of_step hstep
      rw [toNTM_trace_step_exact_internal machine time choices hne]
      have hget :
          (machine.step cfg₀).get (by simp [TM.step, hne]) =
            cfgMiddle := by
        simp [hstep]
      rw [hget]
      exact ih _

/-- A target configuration at a block boundary is either halted or is the
canonical embedding of a well-formed, nonhalted source configuration. -/
def BoundaryFormInternal (source : TM workTapeCount)
    (cfg : Cfg workTapeCount source.tripleStepTM.Q) : Prop :=
  source.tripleStepTM.halted cfg ∨
    ∃ sourceCfg : Cfg workTapeCount source.Q,
      sourceCfg.state ≠ source.qhalt ∧
        CfgStartInvariant sourceCfg ∧
        cfg = boundaryCfg source sourceCfg

theorem boundaryForm_init_internal (source : TM workTapeCount)
    (x : List Bool) :
    BoundaryFormInternal source (source.tripleStepTM.initCfg x) := by
  by_cases hhalt : source.qstart = source.qhalt
  · left
    change wrapState source source.qstart = TripleStepState.halt
    simp [wrapState, hhalt]
  · right
    exact ⟨source.initCfg x, hhalt,
      cfgStartInvariant_init_internal source x, rfl⟩

theorem boundaryForm_trace_three_internal
    (source : TM workTapeCount)
    (cfg : Cfg workTapeCount source.tripleStepTM.Q)
    (hform : BoundaryFormInternal source cfg) :
    BoundaryFormInternal source
      (source.tripleStepTM.toNTM.trace 3 (fun _ => false) cfg) := by
  rcases hform with hhalt |
    ⟨sourceCfg, hstate, hinvariant, rfl⟩
  · left
    rw [source.tripleStepTM.toNTM.trace_halted 3
      (fun _ => false) hhalt]
    exact hhalt
  · have hnotnone : source.step sourceCfg ≠ none := by
      intro hnone
      exact hstate (TM.step_eq_none_iff_halted.mp hnone)
    obtain ⟨sourceCfg', hstep'⟩ :=
      Option.ne_none_iff_exists.mp hnotnone
    have hstep : source.step sourceCfg = some sourceCfg' :=
      hstep'.symm
    have htrace :
        source.tripleStepTM.toNTM.trace 3 (fun _ => false)
            (boundaryCfg source sourceCfg) =
          boundaryCfg source sourceCfg' :=
      toNTM_trace_of_reachesIn_exact_internal source.tripleStepTM
        (tripleStepTM_reachesIn_three_internal
          source hinvariant hstep) _
    rw [htrace]
    by_cases hhalt' : sourceCfg'.state = source.qhalt
    · left
      change wrapState source sourceCfg'.state = TripleStepState.halt
      simp [wrapState, hhalt']
    · right
      exact ⟨sourceCfg', hhalt',
        cfgStartInvariant_of_step_internal source hinvariant hstep, rfl⟩

theorem configurationAt_add_internal (machine : TM workTapeCount)
    (x : List Bool) (time offset : ℕ) :
    machine.configurationAt x (time + offset) =
      machine.toNTM.trace offset (fun _ => false)
        (machine.configurationAt x time) := by
  unfold TM.configurationAt
  simpa using machine.toNTM.trace_add_fun time offset
    (fun _ => false) (machine.initCfg x)

theorem boundaryForm_configurationAt_internal
    (source : TM workTapeCount) (x : List Bool) (timeBlock : ℕ) :
    BoundaryFormInternal source
      (source.tripleStepTM.configurationAt x
        (timeBlockStart 3 timeBlock)) := by
  induction timeBlock with
  | zero =>
      simpa [timeBlockStart] using
        boundaryForm_init_internal source x
  | succ timeBlock ih =>
      rw [show timeBlockStart 3 (timeBlock + 1) =
        timeBlockStart 3 timeBlock + 3 by
          simp [timeBlockStart]
          omega]
      rw [configurationAt_add_internal]
      exact boundaryForm_trace_three_internal source _ ih

theorem blockIndex_three_move_idle_internal (tape : Tape)
    (hinvariant : tape.StartInvariant) :
    blockIndex 3 (tape.move (TM.idleDir tape.read)).head =
      blockIndex 3 tape.head := by
  by_cases hhead : tape.head = 0
  · have hread : tape.read = Γ.start := by
      simp [Tape.read, hhead, hinvariant.1]
    simp [blockIndex, TM.idleDir, hread, Tape.move, hhead]
  · have hpositive : 1 ≤ tape.head := by omega
    have hread : tape.read ≠ Γ.start :=
      hinvariant.read_ne_start hpositive
    simp [blockIndex, TM.idleDir, hread, Tape.move]

theorem blockIndex_three_bounceOutTape_internal (tape : Tape)
    (hinvariant : tape.StartInvariant) :
    blockIndex 3 (bounceOutTape tape).head =
      blockIndex 3 tape.head := by
  rw [bounceOutTape_eq_move_internal tape hinvariant]
  exact blockIndex_three_move_idle_internal tape hinvariant

theorem headBlock_phase1Cfg_internal (source : TM workTapeCount)
    (cfg : Cfg workTapeCount source.Q)
    (hinvariant : CfgStartInvariant cfg)
    (tape : TapeIndex workTapeCount) :
    headBlock 3 (phase1Cfg source cfg) tape =
      headBlock 3 (boundaryCfg source cfg) tape := by
  unfold headBlock tapeAt
  split
  · exact blockIndex_three_move_idle_internal cfg.input hinvariant.1
  · split
    · exact blockIndex_three_bounceOutTape_internal
        cfg.output hinvariant.2.2
    · exact blockIndex_three_bounceOutTape_internal _
        (hinvariant.2.1 _)

theorem headBlock_trace_offset_boundaryCfg_internal
    (source : TM workTapeCount)
    (cfg : Cfg workTapeCount source.Q)
    (hinvariant : CfgStartInvariant cfg)
    (hstate : cfg.state ≠ source.qhalt)
    (offset : Fin 3) (tape : TapeIndex workTapeCount) :
    headBlock 3
        (source.tripleStepTM.toNTM.trace offset.val
          (fun _ => false) (boundaryCfg source cfg)) tape =
      headBlock 3 (boundaryCfg source cfg) tape := by
  fin_cases offset
  · rfl
  · have hstep :=
      tripleStepTM_step_boundaryCfg_internal source cfg hstate
    have htrace :=
      toNTM_trace_of_reachesIn_exact_internal source.tripleStepTM
        (TM.reachesIn.step hstep TM.reachesIn.zero)
        (fun _ => false)
    rw [htrace]
    exact headBlock_phase1Cfg_internal source cfg hinvariant tape
  · have hstep₀ :=
      tripleStepTM_step_boundaryCfg_internal source cfg hstate
    have hstep₁ :=
      tripleStepTM_step_phase1Cfg_internal source cfg hinvariant
    have hreach : source.tripleStepTM.reachesIn 2
        (boundaryCfg source cfg) (phase2Cfg source cfg) :=
      .step hstep₀ (.step hstep₁ .zero)
    have htrace :=
      toNTM_trace_of_reachesIn_exact_internal source.tripleStepTM
        hreach (fun _ => false)
    rw [htrace]
    rfl

theorem headBlock_trace_offset_boundaryForm_internal
    (source : TM workTapeCount)
    (cfg : Cfg workTapeCount source.tripleStepTM.Q)
    (hform : BoundaryFormInternal source cfg)
    (offset : Fin 3) (tape : TapeIndex workTapeCount) :
    headBlock 3
        (source.tripleStepTM.toNTM.trace offset.val
          (fun _ => false) cfg) tape =
      headBlock 3 cfg tape := by
  rcases hform with hhalt |
    ⟨sourceCfg, hstate, hinvariant, rfl⟩
  · rw [source.tripleStepTM.toNTM.trace_halted offset.val
      (fun _ => false) hhalt]
    rfl
  · exact headBlock_trace_offset_boundaryCfg_internal
      source sourceCfg hinvariant hstate offset tape

theorem tripleStepTM_blockRespecting_internal
    (source : TM workTapeCount) :
    source.tripleStepTM.BlockRespecting (fun _ => 3) := by
  intro x
  change 0 < 3 ∧ _
  refine ⟨by decide, ?_⟩
  intro timeBlock offset tape
  rw [configurationAt_add_internal]
  exact headBlock_trace_offset_boundaryForm_internal source _
    (boundaryForm_configurationAt_internal source x timeBlock)
    offset tape

/-- The executable three-microstep compiler packaged as a linear
block-normalization certificate. -/
def tripleStepNormalizationInternal (source : TM workTapeCount)
    (timeBound : ℕ → ℕ) :
    TM.LinearBlockNormalization source timeBound (fun _ => 3) where
  workTapeCount := workTapeCount
  machine := source.tripleStepTM
  workTapeCount_le := by omega
  constant := 3
  constant_pos := by omega
  blockRespecting := tripleStepTM_blockRespecting_internal source
  simulatesBoundedHaltedRun := by
    intro x cfg time htime hreach hhalt
    refine ⟨boundaryCfg source cfg, 3 * time, ?_,
      tripleStepTM_reachesIn_init_internal source x hreach, ?_, rfl⟩
    · omega
    · exact (boundaryCfg_halted_iff_internal source cfg).2 hhalt

end NormalizationCompiler

end TimeSpaceSimulation

end Complexity
