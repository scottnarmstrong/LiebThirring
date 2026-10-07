/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.LocalWeakDerivative

/-! # Local weak integration by parts at limits of cube test jets

The physical local weak relation extends to simultaneous L² limits of compact
smooth tests and their directional derivatives. Constructing product test jets
and proving their convergence remain separate analytic obligations.
-/

public section

open MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace

namespace LiebThirring.TFCubes

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Pass the physical weak relation to an actual simultaneous local L² test limit. -/
theorem HasWeakDerivativeOn.test_limit
    {Ω : Set E} {v : E} {u g φ ψ : RegionState E F Ω}
    (h : HasWeakDerivativeOn Ω v u g) (η : ℕ → E → F)
    (hc : ∀ n, HasCompactSupport (η n)) (hs : ∀ n, ContDiff ℝ ∞ (η n))
    (hΩ : ∀ n, tsupport (η n) ⊆ Ω)
    (hφ : Tendsto (fun n => localTestFunctionL2 Ω (η n) (hc n) (hs n))
      atTop (𝓝 φ))
    (hψ : Tendsto (fun n => localTestFunctionL2 Ω
        (fun x => fderiv ℝ (η n) x v) ((hc n).fderiv_apply ℝ v)
        (((hs n).fderiv_right (by simp)).clm_apply contDiff_const))
      atTop (𝓝 ψ)) :
    ⟪φ, g⟫_ℂ = -⟪ψ, u⟫_ℂ := by
  have heq := hasWeakDerivativeOn_iff_inner.mp h
  exact tendsto_nhds_unique
    ((hφ.inner tendsto_const_nhds).congr'
      (Eventually.of_forall fun n => heq (η n) (hc n) (hs n) (hΩ n)))
    ((hψ.inner tendsto_const_nhds).neg)

end LiebThirring.TFCubes

end
