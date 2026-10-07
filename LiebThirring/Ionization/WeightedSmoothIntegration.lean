/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.WeightedLocal

/-!
# Integration by parts for the full compact smooth core

Local Coulomb integrability and a.e. coordinate lines remove the
avoiding-zero restriction. These are analytic helpers for weighted positivity.
-/

public section
open MeasureTheory
open scoped RealInnerProductSpace
namespace LiebThirring
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A locally integrable weight times a compact smooth norm-square is integrable. -/
theorem integrable_smooth_weight_norm_sq {f : Position → F} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {a : Position → ℝ} (ha : LocallyIntegrable a) :
    Integrable (fun x => a x * ‖f x‖ ^ 2) :=
  ha.integrable_smul_right_of_hasCompactSupport (hf.continuous.norm.pow 2)
    (hfc.comp_left (g := fun u : F => ‖u‖ ^ 2) (by simp))

/-- A locally integrable weight times a compact smooth derivative norm-square
is integrable. -/
theorem integrable_smooth_weight_deriv_sq {f : Position → F} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {a : Position → ℝ} (ha : LocallyIntegrable a) (v : Position) :
    Integrable (fun x => a x * ‖fderiv ℝ f x v‖ ^ 2) :=
  ha.integrable_smul_right_of_hasCompactSupport
    (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).norm.pow 2)
    ((hfc.fderiv_apply ℝ v).comp_left (g := fun u : F => ‖u‖ ^ 2) (by simp))

/-- A locally integrable weight times a compact smooth derivative pairing is integrable. -/
theorem integrable_smooth_weight_inner {f : Position → F} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {a : Position → ℝ} (ha : LocallyIntegrable a) (v : Position) :
    Integrable (fun x => a x * inner ℝ (f x) (fderiv ℝ f x v)) := by
  apply ha.integrable_smul_right_of_hasCompactSupport
  · exact hf.continuous.inner ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  · apply hfc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_mono
    intro x hx
    contrapose! hx
    simp only [Function.mem_support, not_not] at hx ⊢
    rw [hx, inner_zero_left]

/-- Integration by parts against the norm-square, allowing nonzero values at the origin. -/
theorem integral_smooth_field_norm_sq {a : Position → ℝ}
    (ha : ∀ x : Position, x ≠ 0 → DifferentiableAt ℝ a x)
    (hal : LocallyIntegrable a) (i : Fin 3)
    (hadl : LocallyIntegrable (fun x => fderiv ℝ a x (EuclideanSpace.basisFun (Fin 3) ℝ i)))
    {f : Position → F} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x, fderiv ℝ a x (EuclideanSpace.basisFun (Fin 3) ℝ i) * ‖f x‖ ^ 2) =
      -2 * ∫ x, a x * inner ℝ (f x) (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i)) := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ i
  have hg := (hf.norm_sq ℝ).differentiable (by norm_num)
  have hgc := hfc.comp_left (g := fun u : F => ‖u‖ ^ 2) (by simp)
  have h₁ := integrable_smooth_weight_norm_sq hf hfc hadl
  have h₂ : Integrable (fun x => a x * fderiv ℝ (fun y => ‖f y‖ ^ 2) x e) :=
    hal.integrable_smul_right_of_hasCompactSupport
      ((hf.norm_sq ℝ).continuous_fderiv (by norm_num) |>.clm_apply continuous_const)
      (hgc.fderiv_apply ℝ e)
  have h₀ := integrable_smooth_weight_norm_sq hf hfc hal
  have hh := integral_punctured_mul_fderiv_of_integrable ha hg i h₁ h₂ h₀
  have hd (x : Position) : fderiv ℝ (fun y => ‖f y‖ ^ 2) x e =
      2 * inner ℝ (f x) (fderiv ℝ f x e) := by
    rw [((hf.differentiable (by norm_num) x).hasFDerivAt.norm_sq).fderiv]
    simp only [two_smul, add_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    ring
  change (∫ x, a x * fderiv ℝ (fun y => ‖f y‖ ^ 2) x e) = _ at hh
  simp_rw [hd] at hh
  have he : (fun x => a x * (2 * inner ℝ (f x) (fderiv ℝ f x e))) =
      (fun x => 2 * (a x * inner ℝ (f x) (fderiv ℝ f x e))) := by funext x; ring
  rw [he, integral_const_mul] at hh
  linarith only [hh]

/-- The full-core divergence identity; the local integrability premises describe
an arbitrary field and are proved for the two concrete fields in `WeightedLocal`. -/
theorem integral_smooth_divergence_norm_sq {f : Position → F}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (a : Fin 3 → Position → ℝ)
    (ha : ∀ i (x : Position), x ≠ 0 → DifferentiableAt ℝ (a i) x)
    (hal : ∀ i, LocallyIntegrable (a i))
    (hadl : ∀ i, LocallyIntegrable (fun x => fderiv ℝ (a i) x (EuclideanSpace.basisFun (Fin 3) ℝ i))) :
    (∫ x, (∑ i : Fin 3, fderiv ℝ (a i) x (EuclideanSpace.basisFun (Fin 3) ℝ i)) * ‖f x‖ ^ 2) =
      -2 * ∑ i : Fin 3, ∫ x, a i x * inner ℝ (f x)
        (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i)) := by
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => integrable_smooth_weight_norm_sq hf hfc (hadl i))]
  simp_rw [integral_smooth_field_norm_sq (ha _) (hal _) _ (hadl _) hf hfc]
  exact (Finset.mul_sum _ _ _).symm

end LiebThirring
end
