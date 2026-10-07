/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeSpin
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Spin projections preserve the physical weak derivative

Testing with the adjoint of a bounded spin map transports the literal
integration-by-parts relation, without imposing a boundary condition.
-/

public section

open MeasureTheory
open scoped ContDiff InnerProductSpace

namespace LiebThirring.TFCubes

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Bounded linear spin maps commute with genuine local weak differentiation. -/
theorem HasWeakDerivativeOn.compLpL {Ω : Set E} {v : E}
    {u g : RegionState E F Ω} (h : HasWeakDerivativeOn Ω v u g)
    (L : F →L[ℂ] G) :
    HasWeakDerivativeOn Ω v (L.compLpL 2 (volume.restrict Ω) u)
      (L.compLpL 2 (volume.restrict Ω) g) := by
  intro η hc hs hΩ
  let A : G →L[ℝ] F := L.adjoint.restrictScalars ℝ
  have hcs : HasCompactSupport (A ∘ η) := hc.comp_left A.map_zero
  have hss : ContDiff ℝ ∞ (A ∘ η) := A.contDiff.comp hs
  have hsu : tsupport (A ∘ η) ⊆ Ω := (tsupport_comp_subset A.map_zero η).trans hΩ
  have hd (x : E) : fderiv ℝ (A ∘ η) x v = A (fderiv ℝ η x v) := by
    have hd := (A.hasFDerivAt.comp x
      ((hs.differentiable (by simp)).differentiableAt.hasFDerivAt)).fderiv
    rw [hd]
    rfl
  have hw := h (A ∘ η) hcs hss hsu
  calc
    _ = ∫ x in Ω, inner ℂ (A (η x)) (g x) := by
      apply integral_congr_ae
      filter_upwards [L.coeFn_compLpL g] with x hx
      rw [hx]
      exact (L.adjoint_inner_left (g x) (η x)).symm
    _ = -(∫ x in Ω, inner ℂ (A (fderiv ℝ η x v)) (u x)) := by
      simpa only [Function.comp_apply, hd] using hw
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [L.coeFn_compLpL u] with x hx
      rw [hx]
      exact L.adjoint_inner_left (u x) (fderiv ℝ η x v)

end LiebThirring.TFCubes

end
