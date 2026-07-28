/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Hoare.Space.Loop.Defs
import
  Complexitylib.Models.TuringMachine.SpaceTime.Internal.Reachability

/-!
# All-prefix space certificates for `loopTM` — proof internals
-/

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Internal strong-induction proof that certified iteration segments cover
every reachable loop prefix. -/
theorem LoopIterationSpaceSpec.toHoareSpace_internal
    {tmBody tmTest : TM n} {invariant : TapePred n}
    {variant : Tape → (Fin n → Tape) → Tape → ℕ}
    {inputLength spaceBound : ℕ}
    (spec : LoopIterationSpaceSpec tmBody tmTest invariant variant
      inputLength spaceBound) :
    (loopTM tmBody tmTest).HoareSpace
      invariant inputLength spaceBound := by
  intro inp work out hinvariant cfg hreach
  obtain ⟨time, hreachTime⟩ :=
    (loopTM tmBody tmTest).reaches_to_reachesIn hreach
  generalize hvalue : variant inp work out = value
  induction value using Nat.strong_induction_on
      generalizing inp work out time cfg with
  | h value ih =>
      obtain ⟨segmentTime, finish, hsegment, hprefix, houtcome⟩ :=
        spec.iteration inp work out hinvariant
      by_cases htime : time ≤ segmentTime
      · exact hprefix time cfg htime hreachTime
      · rcases houtcome with hhalt | hcontinue
        · have hle :=
            (loopTM tmBody tmTest).reachesIn_le_halt
              hreachTime hsegment hhalt
          omega
        · obtain ⟨inp', work', out', hfinish, hinvariant', hdecrease⟩ :=
            hcontinue
          have hsegmentTime : segmentTime ≤ time := by omega
          let tailTime := time - segmentTime
          have htimeEq : segmentTime + tailTime = time :=
            Nat.add_sub_of_le hsegmentTime
          have hreachSplit :
              (loopTM tmBody tmTest).reachesIn
                (segmentTime + tailTime)
                { state := (loopTM tmBody tmTest).qstart,
                  input := inp, work := work, output := out } cfg := by
            simpa only [htimeEq] using hreachTime
          obtain ⟨boundary, hfirst, htail⟩ :=
            reachesIn_split_internal hreachSplit
          have hboundary : boundary = finish :=
            (loopTM tmBody tmTest).reachesIn_right_unique
              hfirst hsegment
          subst boundary
          rw [hfinish] at htail
          have hdecrease' : variant inp' work' out' < value := by
            omega
          exact ih (variant inp' work' out') hdecrease'
            inp' work' out' hinvariant' cfg
            (TM.reaches_of_reachesIn htail) tailTime htail rfl

end TM

end Complexity
