/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.PackingInterpolation

/-!
# Interpolating finite integer packing inequalities

Namespace-level entry points for applying the balanced-rounding lift in thermodynamic bounds.
-/

public section

namespace LiebThirring.ThermoBounds

open ThermoLimit

/-- Finset form of `interpolate_fin_packing`, convenient for geometric packings and for adding
one exceptional region carrying a fixed integer budget. -/
theorem interpolate_finset_packing {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F : ℕ → ℝ) (G : ι → ℕ → ℝ) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hpack : ∀ m : ι → ℕ, F (∑ i ∈ s, m i) ≤ ∑ i ∈ s, G i (m i)) :
    interpolate F (∑ i ∈ s, x i) ≤ ∑ i ∈ s, interpolate (G i) (x i) :=
  ThermoLimit.interpolate_finset_packing s F G x hx hpack

end LiebThirring.ThermoBounds

end
