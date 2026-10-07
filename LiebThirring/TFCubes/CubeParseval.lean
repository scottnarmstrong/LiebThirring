/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeSpin

/-! # Parseval and finite-coordinate energy assembly

These helpers assemble the physical derivative norms after the mixed-mode
coefficient identities have been established.
-/

public section

open scoped InnerProductSpace ENNReal

namespace LiebThirring.TFCubes

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Unconditional squared-norm Parseval for any genuine Hilbert basis. -/
theorem hasSum_norm_sq_hilbertBasis (B : HilbertBasis ι ℂ E) (u : E) :
    HasSum (fun k => ‖⟪B k, u⟫_ℂ‖ ^ 2) (‖u‖ ^ 2) := by
  have hs := lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (B.repr u)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, B.repr_apply_apply,
    LinearIsometryEquiv.norm_map] using hs

omit [InnerProductSpace ℂ E] in
/-- Sum the finitely many derivative Parseval identities before taking an infinite sum. -/
theorem hasSum_cubeCoordinateEnergy {A : Type*} [Fintype A]
    (w : A → ι → ℝ) (g : A → E)
    (h : ∀ a, HasSum (w a) (‖g a‖ ^ 2)) :
    HasSum (fun k => ∑ a : A, w a k) (∑ a : A, ‖g a‖ ^ 2) := by
  exact hasSum_sum (fun a _ => h a)

end LiebThirring.TFCubes

end
