/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.WeightedCore

/-!
# The kinetic cross-form identity and positivity

Argument weighted positivity for every compact `C²` function, including those nonzero at the origin.
The real Hilbert-space formulation also covers the real part of complex
Hilbert inner products by restriction of scalars.
-/

public section
open MeasureTheory
open scoped RealInnerProductSpace
namespace LiebThirring
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Product rule for the bounded radial multiplier away from zero. -/
theorem fderiv_ionizationWeight_smul {ε : ℝ} (hε : 0 ≤ ε) {f : Position → F}
    (hf : Differentiable ℝ f) {x : Position} (hx : x ≠ 0) (v : Position) :
    fderiv ℝ (fun y => ionizationWeight ε ‖y‖ • f y) x v =
      ionizationWeight ε ‖x‖ • fderiv ℝ f x v +
      (ionizationGradCoeff ε ‖x‖ * inner ℝ x v) • f x := by
  have hd : 0 < 1 + ε * ‖x‖ :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hε (norm_nonneg x))
  have hw := (hasDerivAt_ionizationWeight hd.ne').comp_hasFDerivAt x
    (hasFDerivAt_position_norm hx)
  change HasFDerivAt (fun y : Position => ionizationWeight ε ‖y‖) _ x at hw
  have hh := hw.smul (hf x).hasFDerivAt
  change HasFDerivAt (fun y => ionizationWeight ε ‖y‖ • f y) _ x at hh
  rw [hh.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  congr 1
  dsimp [ionizationGradCoeff]
  field_simp [norm_ne_zero_iff.mpr hx, hd.ne']

/-- The cross-form integrand has the expected product-rule expansion. -/
theorem ionization_cross_pointwise {ε : ℝ} (hε : 0 ≤ ε) {f : Position → F}
    (hf : Differentiable ℝ f) {x : Position} (hx : x ≠ 0) (v : Position) :
    inner ℝ (fderiv ℝ (fun y => ionizationWeight ε ‖y‖ • f y) x v)
      (fderiv ℝ f x v) =
      ionizationWeight ε ‖x‖ * ‖fderiv ℝ f x v‖ ^ 2 +
      (ionizationGradCoeff ε ‖x‖ * inner ℝ x v) *
        inner ℝ (f x) (fderiv ℝ f x v) := by
  rw [fderiv_ionizationWeight_smul hε hf hx, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- The singular mass kernel in the kinetic cross-form is integrable on the core. -/
theorem integrable_ionization_kernel_core {ε : ℝ} (hε : 0 ≤ ε) {f : Position → F}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Integrable (fun x => (1 / (‖x‖ * (1 + ε * ‖x‖) ^ 3)) * ‖f x‖ ^ 2) := by
  exact integrable_smooth_weight_norm_sq hf hfc (locallyIntegrable_ionization_kernel hε 3)

/-- The exact kinetic identity in weighted positivity, with no integrability assumptions added. -/
theorem integral_ionization_cross_eq {ε : ℝ} (hε : 0 ≤ ε) {f : Position → F}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∑ i : Fin 3, ∫ x, inner ℝ
      (fderiv ℝ (fun y => ionizationWeight ε ‖y‖ • f y) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i))) =
      (∫ x, ionizationWeight ε ‖x‖ * ∑ i : Fin 3,
        ‖fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i)‖ ^ 2) -
      ∫ x, (1 / (‖x‖ * (1 + ε * ‖x‖) ^ 3)) * ‖f x‖ ^ 2 := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  let c := fun i (x : Position) => ionizationGradCoeff ε ‖x‖ * inner ℝ x (e i)
  have hc := fun (i : Fin 3) (x : Position) (hx : x ≠ 0) => contDiffAt_ionizationGrad hε hx (e i)
  have hlc := fun i => locallyIntegrable_ionizationGrad hε i
  have hw : LocallyIntegrable (fun x : Position => ionizationWeight ε ‖x‖) :=
    (lipschitzWith_ionizationWeight hε).continuous.locallyIntegrable
  have hg (i : Fin 3) := integrable_smooth_weight_deriv_sq hf hfc hw (e i)
  have hi (i : Fin 3) := integrable_smooth_weight_inner hf hfc (hlc i) (e i)
  have hdiv := integral_smooth_divergence_norm_sq hf hfc c
    (fun i x hx => (hc i x hx).differentiableAt one_ne_zero) hlc
    (fun i => locallyIntegrable_fderiv_ionizationGrad hε i)
  have hdiv' : 2 * (∫ x, (1 / (‖x‖ * (1 + ε * ‖x‖) ^ 3)) * ‖f x‖ ^ 2) =
      -2 * ∑ i : Fin 3, ∫ x, c i x * inner ℝ (f x) (fderiv ℝ f x (e i)) := by
    rw [← integral_const_mul, ← hdiv]
    apply integral_congr_ae
    filter_upwards [show ∀ᵐ x : Position, x ≠ 0 by rw [ae_iff]; simp] with x hx
    rw [show (∑ i, fderiv ℝ (c i) x (e i)) =
      2 / (‖x‖ * (1 + ε * ‖x‖) ^ 3) from sum_fderiv_ionizationGrad hε hx]
    ring
  have he (i : Fin 3) : (∫ x, inner ℝ
      (fderiv ℝ (fun y => ionizationWeight ε ‖y‖ • f y) x (e i))
      (fderiv ℝ f x (e i))) =
      (∫ x, ionizationWeight ε ‖x‖ * ‖fderiv ℝ f x (e i)‖ ^ 2) +
      ∫ x, c i x * inner ℝ (f x) (fderiv ℝ f x (e i)) := by
    rw [← integral_add (hg i) (hi i)]
    apply integral_congr_ae
    filter_upwards [show ∀ᵐ x : Position, x ≠ 0 by rw [ae_iff]; simp] with x hx
    exact ionization_cross_pointwise hε (hf.differentiable (by norm_num)) hx (e i)
  change (∑ i : Fin 3, ∫ x, inner ℝ
    (fderiv ℝ (fun y => ionizationWeight ε ‖y‖ • f y) x (e i))
    (fderiv ℝ f x (e i))) = _
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  have hgs : (∑ i : Fin 3, ∫ x, ionizationWeight ε ‖x‖ * ‖fderiv ℝ f x (e i)‖ ^ 2) =
      ∫ x, ionizationWeight ε ‖x‖ * ∑ i : Fin 3, ‖fderiv ℝ f x (e i)‖ ^ 2 := by
    simp_rw [Finset.mul_sum]
    exact (integral_finsetSum _ (fun i _ => hg i)).symm
  change _ + _ = _ - _
  rw [hgs]
  linarith only [hdiv']

/-- Weighted kinetic positivity on the full compact smooth core of weighted positivity. -/
theorem integral_ionization_cross_nonneg {ε : ℝ} (hε : 0 ≤ ε) {f : Position → F}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    0 ≤ ∑ i : Fin 3, ∫ x, inner ℝ
      (fderiv ℝ (fun y => ionizationWeight ε ‖y‖ • f y) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ i)) := by
  rw [integral_ionization_cross_eq hε hf hfc]
  apply sub_nonneg.mpr
  apply le_trans _ (integral_ionization_hardy_le hε hf hfc)
  have hm := integrable_ionization_kernel_core hε hf hfc
  have hn : Integrable (fun x => ionizationGradCoeff ε ‖x‖ * ‖f x‖ ^ 2) := by
    exact integrable_smooth_weight_norm_sq hf hfc (locallyIntegrable_ionization_kernel hε 2)

  apply integral_mono_ae hm hn
  filter_upwards [show ∀ᵐ x : Position, x ≠ 0 by rw [ae_iff]; simp] with x hx
  exact mul_le_mul_of_nonneg_right
    (ionization_kernel_le hε (norm_pos_iff.mpr hx)) (sq_nonneg _)

end LiebThirring
end
