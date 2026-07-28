/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Structured.Invariant.Defs
import Complexitylib.Models.RandomAccessMachine.Structured.Internal
import Complexitylib.Models.RandomAccessMachine.Structured.Run

/-!
# Proof internals for structured RAM all-program-point invariants
-/

namespace Complexity

namespace RAM

namespace Structured

namespace InvariantRuns

namespace Internal

theorem initial_internal
    {invariant : Store → Prop} {cmd : Cmd}
    {initial final : Store} {steps : ℕ}
    (hrun : InvariantRuns invariant cmd initial final steps) :
    invariant initial := by
  induction hrun <;> assumption

theorem final_internal
    {invariant : Store → Prop} {cmd : Cmd}
    {initial final : Store} {steps : ℕ}
    (hrun : InvariantRuns invariant cmd initial final steps) :
    invariant final := by
  induction hrun <;> assumption

theorem toExecExists_internal
    {invariant : Store → Prop} {cmd : Cmd}
    {initial final : Store} {steps : ℕ}
    (hrun : InvariantRuns invariant cmd initial final steps) :
    ∃ cost space, Exec cmd initial final steps cost space := by
  induction hrun with
  | skip store hstore =>
      exact ⟨0, store.space, Exec.skip store⟩
  | basic op store hstore hnext =>
      exact ⟨op.logCost store,
        max store.space (op.exec store).space,
        Exec.basic op store⟩
  | seq hfirst hsecond ihFirst ihSecond =>
      obtain ⟨firstCost, firstSpace, hfirstExec⟩ := ihFirst
      obtain ⟨secondCost, secondSpace, hsecondExec⟩ := ihSecond
      exact ⟨firstCost + secondCost, max firstSpace secondSpace,
        Exec.seq hfirstExec hsecondExec⟩
  | ifZero htest hbranch ih =>
      obtain ⟨cost, space, hexec⟩ := ih
      exact ⟨bitlen _ + 1 + cost, max _ space,
        Exec.ifZero htest hexec⟩
  | ifNonzero htest hbranch ih =>
      obtain ⟨cost, space, hexec⟩ := ih
      exact ⟨bitlen _ + 1 + cost + 1, max _ space,
        Exec.ifNonzero htest hexec⟩
  | whileZero htest hstore =>
      exact ⟨bitlen _ + 1, _, Exec.whileZero htest⟩
  | whileNonzero htest hbody hloop ihBody ihLoop =>
      obtain ⟨bodyCost, bodySpace, hbodyExec⟩ := ihBody
      obtain ⟨loopCost, loopSpace, hloopExec⟩ := ihLoop
      exact ⟨bitlen _ + 1 + bodyCost + 1 + loopCost,
        max bodySpace loopSpace,
        Exec.whileNonzero htest hbodyExec hloopExec⟩

theorem toRuns_internal
    {invariant : Store → Prop} {cmd : Cmd}
    {initial final : Store} {steps : ℕ}
    (hrun : InvariantRuns invariant cmd initial final steps) :
    Runs cmd initial final := by
  obtain ⟨cost, space, hexec⟩ :=
    toExecExists_internal hrun
  exact ⟨steps, cost, space, hexec⟩

private theorem curInstr_append_head
    (pre suffix : Program) (instruction : Instr) (store : Store) :
    RAM.curInstr (pre ++ instruction :: suffix)
      { pc := pre.length, regs := store } = instruction := by
  simp [RAM.curInstr]

private theorem step_basic
    (pre suffix : Program) (op : Basic) (store : Store) :
    RAM.step (pre ++ op.instr :: suffix)
      { pc := pre.length, regs := store } =
        { pc := pre.length + 1, regs := op.exec store } := by
  unfold RAM.step
  rw [curInstr_append_head]
  cases op <;> simp [Basic.instr, Basic.exec, RAM.stepInstr]

private theorem step_jz_zero
    (pre suffix : Program) (test target : ℕ) (store : Store)
    (htest : store test = 0) :
    RAM.step (pre ++ Instr.jz test target :: suffix)
      { pc := pre.length, regs := store } =
        { pc := target, regs := store } := by
  unfold RAM.step
  rw [curInstr_append_head]
  simp [RAM.stepInstr, htest]

private theorem step_jz_nonzero
    (pre suffix : Program) (test target : ℕ) (store : Store)
    (htest : store test ≠ 0) :
    RAM.step (pre ++ Instr.jz test target :: suffix)
      { pc := pre.length, regs := store } =
        { pc := pre.length + 1, regs := store } := by
  unfold RAM.step
  rw [curInstr_append_head]
  simp [RAM.stepInstr, htest]

private theorem step_jmp
    (pre suffix : Program) (target : ℕ) (store : Store) :
    RAM.step (pre ++ Instr.jmp target :: suffix)
      { pc := pre.length, regs := store } =
        { pc := target, regs := store } := by
  unfold RAM.step
  rw [curInstr_append_head]
  rfl

private theorem compileAt_full
    {invariant : Store → Prop} {cmd : Cmd}
    {initial final : Store} {steps : ℕ}
    (hrun : InvariantRuns invariant cmd initial final steps)
    (pre suffix : Program) :
    RAM.run (pre ++ cmd.compileAt pre.length ++ suffix) steps
      { pc := pre.length, regs := initial } =
        { pc := pre.length + cmd.codeSize, regs := final } := by
  obtain ⟨cost, space, hexec⟩ :=
    toExecExists_internal hrun
  exact (compileAt_correct_internal hexec pre suffix).1

private theorem while_iteration_full
    {invariant : Store → Prop} {test : ℕ} {body : Cmd}
    {initial middle : Store} {bodySteps : ℕ}
    (htest : initial test ≠ 0)
    (hbody :
      InvariantRuns invariant body initial middle bodySteps)
    (pre suffix : Program) :
    RAM.run
      (pre ++ (Cmd.whileNonzero test body).compileAt pre.length ++
        suffix)
      (bodySteps + 2) { pc := pre.length, regs := initial } =
        { pc := pre.length, regs := middle } := by
  rw [show bodySteps + 2 = 1 + (bodySteps + 1) by omega,
    RAM.run_add, RAM.run_one]
  let done :=
    pre.length + (Cmd.whileNonzero test body).codeSize
  simp only [Cmd.compileAt, List.nil_append, List.cons_append,
    List.append_assoc]
  rw [step_jz_nonzero pre _ test done initial htest]
  rw [RAM.run_add]
  let bodyPre := pre ++ [Instr.jz test done]
  have hbodyPre : bodyPre.length = pre.length + 1 := by
    simp [bodyPre]
  have hbodyFull := compileAt_full hbody bodyPre
    (Instr.jmp pre.length :: suffix)
  simp only [bodyPre, hbodyPre, List.singleton_append,
    List.append_assoc] at hbodyFull
  dsimp only [done] at hbodyFull
  rw [show (pre ++ Instr.jz test
          (pre.length + (Cmd.whileNonzero test body).codeSize) ::
            (body.compileAt (pre.length + 1) ++
              Instr.jmp pre.length :: suffix)) =
        pre ++ (Instr.jz test
          (pre.length + (Cmd.whileNonzero test body).codeSize) ::
            body.compileAt (pre.length + 1) ++
              Instr.jmp pre.length :: suffix) by
    simp only [List.cons_append]]
  rw [hbodyFull, RAM.run_one]
  let jmpPre := pre ++ [Instr.jz test
    (pre.length + (Cmd.whileNonzero test body).codeSize)] ++
      body.compileAt (pre.length + 1)
  have hprogram :
      pre ++ (Instr.jz test
        (pre.length + (Cmd.whileNonzero test body).codeSize) ::
          body.compileAt (pre.length + 1) ++
            Instr.jmp pre.length :: suffix) =
        jmpPre ++ Instr.jmp pre.length :: suffix := by
    simp [jmpPre, List.append_assoc]
  rw [hprogram]
  have hpc :
      pre.length + 1 + body.codeSize = jmpPre.length := by
    simp only [jmpPre, List.length_append,
      List.length_singleton, Cmd.length_compileAt]
  rw [hpc]
  exact step_jmp jmpPre suffix pre.length middle

private theorem compileAt_prefix
    {invariant : Store → Prop} {cmd : Cmd}
    {initial final : Store} {steps : ℕ}
    (hrun : InvariantRuns invariant cmd initial final steps)
    (pre suffix : Program)
    {k : ℕ} (hk : k ≤ steps) :
    invariant
      (RAM.run (pre ++ cmd.compileAt pre.length ++ suffix) k
        { pc := pre.length, regs := initial }).regs := by
  induction hrun generalizing pre suffix k with
  | skip store hstore =>
      have hkzero : k = 0 := by omega
      subst k
      simpa using hstore
  | basic op store hstore hnext =>
      cases k with
      | zero =>
          simpa using hstore
      | succ k =>
          have hkzero : k = 0 := by omega
          subst k
          rw [RAM.run_one]
          simp only [Cmd.compileAt, List.singleton_append,
            List.append_assoc]
          rw [step_basic]
          exact hnext
  | seq hfirst hsecond ihFirst ihSecond =>
      rename_i first second startStore middle finalStore
        firstSteps secondSteps
      by_cases hkfirst : k ≤ firstSteps
      · have hprefix := ihFirst pre
          (second.compileAt (pre.length + first.codeSize) ++ suffix)
          hkfirst
        simpa [Cmd.compileAt, List.append_assoc] using hprefix
      · let remaining := k - firstSteps
        have hsplit : firstSteps + remaining = k := by
          simp [remaining]
          omega
        have hremaining : remaining ≤ secondSteps := by omega
        let secondPre := pre ++ first.compileAt pre.length
        have hsecondPre :
            secondPre.length = pre.length + first.codeSize := by
          simp [secondPre, Cmd.length_compileAt]
        have hsecondPrefix :=
          ihSecond secondPre suffix hremaining
        simp only [secondPre, hsecondPre, List.append_assoc]
          at hsecondPrefix
        have hfirstFull := compileAt_full hfirst pre
          (second.compileAt (pre.length + first.codeSize) ++ suffix)
        simp only [List.append_assoc] at hfirstFull
        rw [← hsplit, RAM.run_add]
        simp only [Cmd.compileAt, List.append_assoc]
        rw [hfirstFull]
        exact hsecondPrefix
  | ifZero htest hbranch ih =>
      rename_i test onZero onNonzero store finalStore branchSteps
      cases k with
      | zero =>
          simpa using initial_internal hbranch
      | succ remaining =>
          have hremaining : remaining ≤ branchSteps := by omega
          let zeroStart :=
            pre.length + 1 + onNonzero.codeSize + 1
          let done := pre.length +
            (Cmd.ifZero test onZero onNonzero).codeSize
          let zeroPre := pre ++ [Instr.jz test zeroStart] ++
            onNonzero.compileAt (pre.length + 1) ++
              [Instr.jmp done]
          have hzeroPre : zeroPre.length = zeroStart := by
            simp [zeroPre, zeroStart, Cmd.length_compileAt]
            omega
          have hprefix := ih zeroPre suffix hremaining
          simp only [hzeroPre] at hprefix
          rw [RAM.run_succ]
          simp only [Cmd.compileAt, List.nil_append,
            List.cons_append, List.append_assoc]
          simp [RAM.Halted, RAM.curInstr]
          rw [step_jz_zero pre _ test zeroStart store htest]
          simpa [zeroPre, zeroStart, done, List.append_assoc] using
            hprefix
  | ifNonzero htest hbranch ih =>
      rename_i test onZero onNonzero store finalStore branchSteps
      cases k with
      | zero =>
          simpa using initial_internal hbranch
      | succ remaining =>
          by_cases hbranchPrefix : remaining ≤ branchSteps
          · let zeroStart :=
              pre.length + 1 + onNonzero.codeSize + 1
            let done := pre.length +
              (Cmd.ifZero test onZero onNonzero).codeSize
            let nonzeroPre := pre ++ [Instr.jz test zeroStart]
            have hnonzeroPre :
                nonzeroPre.length = pre.length + 1 := by
              simp [nonzeroPre]
            have hprefix := ih nonzeroPre
              (Instr.jmp done ::
                onZero.compileAt zeroStart ++ suffix)
              hbranchPrefix
            simp only [hnonzeroPre] at hprefix
            rw [RAM.run_succ]
            simp only [Cmd.compileAt, List.nil_append,
              List.cons_append, List.append_assoc]
            simp [RAM.Halted, RAM.curInstr]
            rw [step_jz_nonzero pre _ test zeroStart store htest]
            simpa [nonzeroPre, zeroStart, done, List.append_assoc]
              using hprefix
          · have heq :
                remaining + 1 = branchSteps + 2 := by
              omega
            rw [heq]
            have hfull := compileAt_full
              (InvariantRuns.ifNonzero
                (onZero := onZero) htest hbranch)
              pre suffix
            rw [hfull]
            exact final_internal hbranch
  | whileZero htest hstore =>
      rename_i test body store
      cases k with
      | zero =>
          simpa using hstore
      | succ remaining =>
          have hzero : remaining = 0 := by omega
          subst remaining
          have hfull := compileAt_full
            (InvariantRuns.whileZero
              (body := body) htest hstore)
            pre suffix
          rw [hfull]
          exact hstore
  | whileNonzero htest hbody hloop ihBody ihLoop =>
      rename_i test body startStore middle finalStore
        bodySteps loopSteps
      cases k with
      | zero =>
          simpa using initial_internal hbody
      | succ remaining =>
          by_cases hbodyPrefix : remaining ≤ bodySteps
          · let done := pre.length +
              (Cmd.whileNonzero test body).codeSize
            let bodyPre := pre ++ [Instr.jz test done]
            have hbodyPre :
                bodyPre.length = pre.length + 1 := by
              simp [bodyPre]
            have hprefix := ihBody bodyPre
              (Instr.jmp pre.length :: suffix)
              hbodyPrefix
            simp only [hbodyPre] at hprefix
            rw [RAM.run_succ]
            simp only [Cmd.compileAt, List.nil_append,
              List.cons_append, List.append_assoc]
            simp [RAM.Halted, RAM.curInstr]
            rw [step_jz_nonzero pre _ test done startStore htest]
            simpa [bodyPre, done, List.append_assoc] using hprefix
          · let loopPrefix :=
              remaining - (bodySteps + 1)
            have hsplit :
                bodySteps + 1 + loopPrefix = remaining := by
              simp only [loopPrefix]
              omega
            have hloopPrefix :
                loopPrefix ≤ loopSteps := by
              omega
            have heq :
                remaining + 1 =
                  bodySteps + 2 + loopPrefix := by
              omega
            rw [heq, RAM.run_add]
            have hiteration :=
              while_iteration_full htest hbody pre suffix
            rw [hiteration]
            exact ihLoop pre suffix hloopPrefix

theorem compile_prefix_internal
    {invariant : Store → Prop} {cmd : Cmd}
    {initial final : Store} {steps : ℕ}
    (hrun : InvariantRuns invariant cmd initial final steps)
    {k : ℕ} (hk : k ≤ steps) :
    invariant
      (RAM.run cmd.compile k { pc := 0, regs := initial }).regs := by
  simpa [Cmd.compile] using
    compileAt_prefix hrun ([] : Program) [Instr.halt] hk

end Internal

end InvariantRuns

end Structured

end RAM

end Complexity
