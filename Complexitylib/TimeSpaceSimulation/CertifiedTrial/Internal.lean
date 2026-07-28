/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.BlockRespecting
import Complexitylib.TimeSpaceSimulation.CertifiedTrial.Defs
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.DecisionRecovery
import
  Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.EvaluatedProvider
import Complexitylib.TimeSpaceSimulation.NeighborhoodGraph.Guess.Search

/-!
# Correctness internals for one locally certified trial
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace CertifiedTrial

open NeighborhoodGraph
open NeighborhoodGraph.Guess

namespace Internal

theorem decodeVerdict_eq_some_true_iff_internal (symbol : Γ) :
    decodeVerdict symbol = some true ↔ symbol = Γ.one := by
  simp [decodeVerdict]

theorem decodeVerdict_eq_some_false_iff_internal (symbol : Γ) :
    decodeVerdict symbol = some false ↔ symbol = Γ.zero := by
  cases symbol <;> simp [decodeVerdict]

private theorem firstPassing_valid
    (tm : TM workTapeCount) (x : List Bool)
    (blockLength horizon : ℕ) (hpositive : 0 < blockLength)
    (engine : Engine tm blockLength horizon)
    (hexact : engine.IsExact x hpositive)
    {code : Fin (Search.guessCount workTapeCount horizon)}
    (hcode :
      Search.firstPassingCode tm x blockLength
          (EvaluatedProvider.provider engine.node) =
        some code) :
    (Enumeration.candidateGuess
      (Fin.cast (by simp [Search.guessCount]) code :
        Fin (3 ^ Enumeration.movementCount
          workTapeCount horizon))).IsValidFor
      (actualCenterTrajectory tm x blockLength) := by
  apply Search.firstPassingCode_valid
    tm x blockLength horizon hpositive
      (EvaluatedProvider.provider engine.node)
  · exact hexact.1.isExactProvider
  · exact hcode

private theorem halted_frozen_eq_decider
    (tm : TM workTapeCount) (x : List Bool)
    (time : ℕ) (cfg : Cfg workTapeCount tm.Q)
    (haltTime : ℕ)
    (hreach : tm.reachesIn haltTime (tm.initCfg x) cfg)
    (hhalt : tm.halted cfg)
    (hfrozen :
      tm.halted (tm.configurationAt x time)) :
    tm.configurationAt x time = cfg := by
  obtain ⟨frozenTime, hfrozenReach⟩ :=
    tm.reaches_to_reachesIn
      (tm.configurationAt_reaches x time)
  have hfrozen_le :
      frozenTime ≤ haltTime :=
    tm.reachesIn_le_halt hfrozenReach hreach hhalt
  have hhalt_le :
      haltTime ≤ frozenTime :=
    tm.reachesIn_le_halt hreach hfrozenReach hfrozen
  have hfirst :
      tm.configurationAt x frozenTime =
        tm.configurationAt x time :=
    tm.configurationAt_of_reachesIn
      hfrozenReach hfrozen (le_refl frozenTime)
  have hsecond :
      tm.configurationAt x frozenTime = cfg :=
    tm.configurationAt_of_reachesIn
      hreach hhalt (by omega)
  exact hfirst.symm.trans hsecond

theorem run_sound_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (x : List Bool) (blockLength horizon : ℕ)
    (hpositive : 0 < blockLength)
    (engine : Engine tm blockLength horizon)
    (hexact : engine.IsExact x hpositive)
    {answer : Bool}
    (hrun : run tm x blockLength engine = some answer) :
    (answer = true → x ∈ L) ∧
      (answer = false → x ∉ L) := by
  unfold run at hrun
  generalize hsearch :
    Search.firstPassingCode tm x blockLength
      (EvaluatedProvider.provider engine.node) = result at hrun
  cases result with
  | none =>
      simp at hrun
  | some code =>
      let guess :=
        Enumeration.candidateGuess
          (Fin.cast (by simp [Search.guessCount]) code :
            Fin (3 ^ Enumeration.movementCount
              workTapeCount horizon))
      have hvalid :
          guess.IsValidFor
            (actualCenterTrajectory tm x blockLength) := by
        exact firstPassing_valid
          tm x blockLength horizon hpositive
          engine hexact hsearch
      have hsnapshot :=
        hexact.2 guess hvalid
      change
        (match engine.snapshot guess with
        | none => none
        | some snapshot =>
            if snapshot.state = tm.qhalt then
              decodeVerdict snapshot.verdict
            else
              none) = some answer at hrun
      rw [hsnapshot] at hrun
      by_cases hstate :
          (DecisionRecovery.decisionSnapshot
            tm x blockLength hpositive horizon).state =
              tm.qhalt
      · simp only [hstate, if_true] at hrun
        have hfrozen :
            tm.halted
              (tm.configurationAt x
                (timeBlockStart blockLength horizon)) := by
          simpa [TM.halted, Cfg.isHalted,
            DecisionRecovery.decisionSnapshot_state
              tm x blockLength horizon hpositive] using hstate
        obtain ⟨cfg, haltTime, _htime, hreach, hhalt,
            hmember, hnotMember⟩ :=
          hdecides x
        have hcfg :
            tm.configurationAt x
                (timeBlockStart blockLength horizon) =
              cfg :=
          halted_frozen_eq_decider
            tm x (timeBlockStart blockLength horizon)
              cfg haltTime hreach hhalt hfrozen
        have hverdict :
            (DecisionRecovery.decisionSnapshot
              tm x blockLength hpositive horizon).verdict =
                cfg.output.cells 1 := by
          rw [DecisionRecovery.decisionSnapshot_verdict,
            hcfg]
        constructor
        · intro hanswer
          subst answer
          have hone :=
            (decodeVerdict_eq_some_true_iff_internal _).1
              hrun
          by_contra hnot
          have hzero := hnotMember hnot
          rw [hverdict, hzero] at hone
          simp at hone
        · intro hanswer
          subst answer
          have hzero :=
            (decodeVerdict_eq_some_false_iff_internal _).1
              hrun
          intro hmem
          have hone := hmember hmem
          rw [hverdict, hone] at hzero
          simp at hzero
      · simp [hstate] at hrun

theorem run_complete_internal
    (tm : TM workTapeCount) (L : Language)
    (actualTime : ℕ → ℕ)
    (hdecides : tm.DecidesInTime L actualTime)
    (x : List Bool) (blockLength horizon : ℕ)
    (hpositive : 0 < blockLength)
    (hcover :
      actualTime x.length ≤
        timeBlockStart blockLength horizon)
    (engine : Engine tm blockLength horizon)
    (hexact : engine.IsExact x hpositive) :
    (run tm x blockLength engine).isSome := by
  have hprovider :
      Consistency.IsExactProvider
        tm x blockLength hpositive
        (EvaluatedProvider.provider engine.node) :=
    hexact.1.isExactProvider
  have hsearchSome :=
    Search.firstPassingCode_complete
      tm x blockLength horizon hpositive
        (EvaluatedProvider.provider engine.node) hprovider
  obtain ⟨code, hsearch⟩ :=
    Option.isSome_iff_exists.mp hsearchSome
  let guess :=
    Enumeration.candidateGuess
      (Fin.cast (by simp [Search.guessCount]) code :
        Fin (3 ^ Enumeration.movementCount
          workTapeCount horizon))
  have hvalid :
      guess.IsValidFor
        (actualCenterTrajectory tm x blockLength) :=
    firstPassing_valid tm x blockLength horizon hpositive
      engine hexact hsearch
  have hsnapshot := hexact.2 guess hvalid
  obtain ⟨cfg, haltTime, htime, hreach, hhalt,
      hmember, hnotMember⟩ :=
    hdecides x
  have hcovered : haltTime ≤
      timeBlockStart blockLength horizon :=
    htime.trans hcover
  have hsnapshotValue :=
    DecisionRecovery.decisionSnapshot_eq_of_reachesIn
      tm x blockLength horizon haltTime hpositive cfg
        hreach hhalt hcovered
  unfold run
  rw [hsearch]
  change
    (match engine.snapshot guess with
    | none => none
    | some snapshot =>
        if snapshot.state = tm.qhalt then
          decodeVerdict snapshot.verdict
        else
          none).isSome
  rw [hsnapshot, hsnapshotValue]
  have hstate : cfg.state = tm.qhalt := hhalt
  simp only [hstate, if_true]
  by_cases hx : x ∈ L
  · rw [hmember hx]
    simp [decodeVerdict]
  · rw [hnotMember hx]
    simp [decodeVerdict]

end Internal

end CertifiedTrial

end TimeSpaceSimulation

end Complexity
