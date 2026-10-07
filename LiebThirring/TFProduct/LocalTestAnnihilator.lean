/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.LocalWeakGraph

/-! # Local compact-smooth tests separate local L² -/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff Topology

namespace LiebThirring.TFProduct

open TFCubes

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasureSpace G] [BorelSpace G]
  [IsLocallyFiniteMeasure (volume : Measure G)]

/-- Compact smooth tests supported in an open region separate its local L² space. -/
theorem localTest_orthogonal_eq_zero {Θ : Set G} (hΘ : IsOpen Θ)
    (p : RegionState G ℂ Θ)
    (hp : ∀ ψ : G → ℂ, ∀ hψc : HasCompactSupport ψ,
      ∀ hψs : ContDiff ℝ ∞ ψ, tsupport ψ ⊆ Θ →
        inner ℂ (localTestFunctionL2 Θ ψ hψc hψs) p = 0) :
    p = 0 := by
  have hzeroP : HasWeakDerivativeOn Θ (0 : G)
      (0 : RegionState G ℂ Θ) p := by
    rw [hasWeakDerivativeOn_iff_inner]
    intro ψ hψc hψs hψΘ
    rw [hp ψ hψc hψs hψΘ]
    simp only [ContinuousLinearMap.map_zero, inner_zero_right, neg_zero]
  exact (hzeroP.unique (HasWeakDerivativeOn.zero Θ (0 : G)) hΘ)

end LiebThirring.TFProduct

end
