/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.StackDepth.Defs
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.StackDepth.Internal

/-!
# Suspended-stack depth for the neighborhood scheduler

Only suspended parent frames are packed. These theorems prove that every
scheduler prefix contains at most the initial fuel, and therefore at most the
canonical interval horizon, suspended frames.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodScheduler
namespace StackDepth

variable {workTapeCount : ℕ}
variable {tm : TM workTapeCount}
variable {instanceData : NeighborhoodProgram.ResidueInstance tm}

/-- The singleton initial scheduler stack satisfies the exact fuel-chain
capacity invariant. -/
theorem stackInvariant_initial
    (fuel : ℕ)
    (node : NeighborhoodEvaluator.QueryNode
      workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1))
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    StackInvariant fuel
      (State.initial fuel node scalar out registers) :=
  Internal.stackInvariant_initial_internal
    fuel node scalar out registers

/-- One scheduler microstep preserves the fuel-chain capacity invariant. -/
theorem StackInvariant.next
    (initialFuel : ℕ)
    (state : State tm instanceData)
    (hinvariant : StackInvariant initialFuel state) :
    StackInvariant initialFuel state.next :=
  Internal.stackInvariant_next_internal initialFuel state hinvariant

/-- Every prefix of a scheduler execution preserves the fuel-chain capacity
invariant. -/
theorem stackInvariant_iterate
    (fuel steps : ℕ)
    (node : NeighborhoodEvaluator.QueryNode
      workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1))
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    StackInvariant fuel
      (State.next^[steps]
        (State.initial fuel node scalar out registers)) :=
  Internal.stackInvariant_iterate_internal
    fuel steps node scalar out registers

/-- The capacity invariant bounds the packed tail of suspended parents. -/
theorem suspendedDepth_le_of_stackInvariant
    (initialFuel : ℕ)
    (state : State tm instanceData)
    (hinvariant : StackInvariant initialFuel state) :
    suspendedDepth state ≤ initialFuel :=
  Internal.suspendedDepth_le_of_stackInvariant_internal
    initialFuel state hinvariant

/-- At every scheduler prefix, the number of suspended parent frames is at
most the initial recursion fuel. -/
theorem suspendedDepth_iterate_le
    (fuel steps : ℕ)
    (node : NeighborhoodEvaluator.QueryNode
      workTapeCount instanceData.horizon)
    (scalar : ℕ)
    (out : Fin
      (NeighborhoodExecutableEvaluation.graphFanIn workTapeCount + 1))
    (registers :
      NeighborhoodExecutableEvaluation.Residue.Registers
        tm instanceData.blockLength) :
    suspendedDepth
        (State.next^[steps]
          (State.initial fuel node scalar out registers)) ≤
      fuel :=
  Internal.suspendedDepth_iterate_le_internal
    fuel steps node scalar out registers

/-- Packing valid frame digits in stack order uses exactly one radix position
per frame. -/
theorem packFrames_lt_pow
    (base : ℕ)
    (encode : Frame tm instanceData → ℕ)
    (frames : List (Frame tm instanceData))
    (hdigit : ∀ frame ∈ frames, encode frame < base) :
    packFrames base encode frames < base ^ frames.length :=
  Internal.packFrames_lt_pow_internal base encode frames hdigit

/-- Packing only the suspended tail uses exactly its suspended-depth number
of radix positions. -/
theorem packSuspended_lt_pow
    (base : ℕ)
    (encode : Frame tm instanceData → ℕ)
    (state : State tm instanceData)
    (hdigit :
      ∀ frame ∈ state.stack.tail, encode frame < base) :
    packSuspended base encode state <
      base ^ suspendedDepth state :=
  Internal.packSuspended_lt_pow_internal base encode state hdigit

/-- A scheduler fuel invariant upgrades the exact packed-tail bound to the
initial-fuel exponent used by workspace accounting. -/
theorem packSuspended_lt_pow_of_stackInvariant
    (base : ℕ)
    (encode : Frame tm instanceData → ℕ)
    (initialFuel : ℕ)
    (state : State tm instanceData)
    (hbase : 1 ≤ base)
    (hinvariant : StackInvariant initialFuel state)
    (hdigit :
      ∀ frame ∈ state.stack.tail, encode frame < base) :
    packSuspended base encode state < base ^ initialFuel :=
  Internal.packSuspended_lt_pow_of_stackInvariant_internal
    base encode initialFuel state hbase hinvariant hdigit

namespace Decision

/-- The initial two-query decision scheduler satisfies the canonical horizon
stack invariant. -/
theorem stackInvariant_initial :
    Decision.StackInvariant
      (NeighborhoodScheduler.Decision.initial
        (instanceData := instanceData)) :=
  Internal.Decision.stackInvariant_initial_internal

/-- One decision microstep preserves the nested query's horizon stack
invariant. -/
theorem StackInvariant.next
    (state : NeighborhoodScheduler.Decision.State tm instanceData)
    (hinvariant : Decision.StackInvariant state) :
    Decision.StackInvariant
      (NeighborhoodScheduler.Decision.next state) :=
  Internal.Decision.stackInvariant_next_internal state hinvariant

/-- Every prefix of the two-query decision scheduler preserves the canonical
horizon stack invariant. -/
theorem stackInvariant_iterate
    (steps : ℕ) :
    Decision.StackInvariant
      (NeighborhoodScheduler.Decision.next^[steps]
        (NeighborhoodScheduler.Decision.initial
          (instanceData := instanceData))) :=
  Internal.Decision.stackInvariant_iterate_internal steps

/-- At every decision-scheduler prefix, the current query has at most one
packed suspended frame per canonical time-block interval. -/
theorem suspendedDepth_iterate_le
    (steps : ℕ) :
    Decision.suspendedDepth
        (NeighborhoodScheduler.Decision.next^[steps]
          (NeighborhoodScheduler.Decision.initial
            (instanceData := instanceData))) ≤
      instanceData.horizon :=
  Internal.Decision.suspendedDepth_iterate_le_internal steps

/-- Any bounded frame codec packs the suspended decision stack below the
canonical horizon power at every scheduler prefix. -/
theorem packSuspended_iterate_lt_pow
    (base : ℕ)
    (encode : Frame tm instanceData → ℕ)
    (steps : ℕ)
    (hbase : 1 ≤ base)
    (hdigit :
      let state :=
        NeighborhoodScheduler.Decision.next^[steps]
          (NeighborhoodScheduler.Decision.initial
            (instanceData := instanceData))
      ∀ frame ∈ state.query.stack.tail, encode frame < base) :
    Decision.packSuspended base encode
        (NeighborhoodScheduler.Decision.next^[steps]
          (NeighborhoodScheduler.Decision.initial
            (instanceData := instanceData))) <
      base ^ instanceData.horizon :=
  Internal.Decision.packSuspended_iterate_lt_pow_internal
    base encode steps hbase hdigit

end Decision

end StackDepth
end NeighborhoodScheduler
end Runtime
end TimeSpaceSimulation
end Complexity
