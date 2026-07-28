/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.TimeSpaceSimulation.CertifiedTrial.Defs
import Complexitylib.TimeSpaceSimulation.CertifiedTrial.Internal

/-!
# One locally certified candidate-time trial

An exact executable engine yields a sound decision whenever a trial returns,
and the trial succeeds once its block horizon covers the source time bound.
-/

namespace Complexity

namespace TimeSpaceSimulation

namespace CertifiedTrial

/-- Decoding returns `true` exactly for the symbol `1`. -/
theorem decodeVerdict_eq_some_true_iff (symbol : Γ) :
    decodeVerdict symbol = some true ↔ symbol = Γ.one :=
  Internal.decodeVerdict_eq_some_true_iff_internal symbol

/-- Decoding returns `false` exactly for the symbol `0`. -/
theorem decodeVerdict_eq_some_false_iff (symbol : Γ) :
    decodeVerdict symbol = some false ↔ symbol = Γ.zero :=
  Internal.decodeVerdict_eq_some_false_iff_internal symbol

/-- Every returned Boolean is the source machine's correct decision. -/
theorem run_sound
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
      (answer = false → x ∉ L) :=
  Internal.run_sound_internal
    tm L actualTime hdecides x blockLength horizon
      hpositive engine hexact hrun

/-- A trial succeeds once its interval horizon covers the supplied source
time bound. -/
theorem run_complete
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
    (run tm x blockLength engine).isSome :=
  Internal.run_complete_internal
    tm L actualTime hdecides x blockLength horizon
      hpositive hcover engine hexact

end CertifiedTrial

end TimeSpaceSimulation

end Complexity
