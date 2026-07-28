/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.TimeSpaceSimulation.Runtime.NeighborhoodScheduler.Defs
import Complexitylib.TimeSpaceSimulation.Runtime.PackedDigits.Defs

/-!
# Suspended-stack depth for the neighborhood scheduler

The active scheduler frame is represented by fixed scalar registers. Only its
tail of suspended parents is packed. This definitions layer records the exact
fuel-chain invariant used to show that the packed tail has at most the initial
fuel, and hence at most the canonical interval horizon, digits.
-/

namespace Complexity
namespace TimeSpaceSimulation
namespace Runtime
namespace NeighborhoodScheduler
namespace StackDepth

variable {workTapeCount : ℕ}
variable {tm : TM workTapeCount}
variable {instanceData : NeighborhoodProgram.ResidueInstance tm}

namespace Frame

/-- Every non-entry phase belongs to a recursive computation frame and
therefore has positive fuel. -/
def PhaseValid (frame : NeighborhoodScheduler.Frame tm instanceData) : Prop :=
  match frame.phase with
  | .enter => True
  | .prepare _ _ _ => 0 < frame.fuel
  | .combine _ _ => 0 < frame.fuel
  | .cleanupCall _ _ _ => 0 < frame.fuel
  | .cleanupScale _ _ _ _ => 0 < frame.fuel

end Frame

/-- Suspended parents have exactly one more unit of fuel than the child
immediately before them. -/
def FuelChain :
    List (NeighborhoodScheduler.Frame tm instanceData) → Prop
  | [] => True
  | [_] => True
  | child :: parent :: tail =>
      parent.fuel = child.fuel + 1 ∧
        FuelChain (parent :: tail)

/-- Fuel of the active frame, or zero for a terminal empty stack. -/
def headFuel :
    List (NeighborhoodScheduler.Frame tm instanceData) → ℕ
  | [] => 0
  | frame :: _ => frame.fuel

/-- Reachability invariant for a scheduler started with `initialFuel`.

The final inequality is a conserved capacity: pushing a recursive child adds
one frame and subtracts one unit from the active fuel; popping that child does
the reverse. -/
def StackInvariant
    (initialFuel : ℕ)
    (state : NeighborhoodScheduler.State tm instanceData) : Prop :=
  (∀ frame ∈ state.stack, Frame.PhaseValid frame) ∧
    FuelChain state.stack ∧
    state.stack.length + headFuel state.stack ≤ initialFuel + 1

/-- Number of packed suspended parents. The active head frame is excluded. -/
def suspendedDepth
    (state : NeighborhoodScheduler.State tm instanceData) : ℕ :=
  state.stack.length - 1

/-- Pack a list of frame digits in stack order, with the head as the
least-significant radix digit. -/
def packFrames
    (base : ℕ)
    (encode : NeighborhoodScheduler.Frame tm instanceData → ℕ) :
    List (NeighborhoodScheduler.Frame tm instanceData) → ℕ
  | [] => 0
  | frame :: tail =>
      PackedDigits.push base (encode frame)
        (packFrames base encode tail)

/-- Pack only suspended parents, excluding the active head frame. -/
def packSuspended
    (base : ℕ)
    (encode : NeighborhoodScheduler.Frame tm instanceData → ℕ)
    (state : NeighborhoodScheduler.State tm instanceData) : ℕ :=
  packFrames base encode state.stack.tail

namespace Decision

/-- The nested query stack in every decision phase uses the canonical horizon
as its initial fuel capacity. -/
def StackInvariant
    (state : NeighborhoodScheduler.Decision.State tm instanceData) : Prop :=
  StackDepth.StackInvariant instanceData.horizon state.query

/-- Number of suspended parents in the currently active decision query. -/
def suspendedDepth
    (state : NeighborhoodScheduler.Decision.State tm instanceData) : ℕ :=
  StackDepth.suspendedDepth state.query

/-- Packed word of the current decision query's suspended parent frames. -/
def packSuspended
    (base : ℕ)
    (encode : NeighborhoodScheduler.Frame tm instanceData → ℕ)
    (state : NeighborhoodScheduler.Decision.State tm instanceData) : ℕ :=
  StackDepth.packSuspended base encode state.query

end Decision

end StackDepth
end NeighborhoodScheduler
end Runtime
end TimeSpaceSimulation
end Complexity
