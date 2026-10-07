/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Configuration

/-!
# The bounded radial ionization weight

Scalar calculus and the radial vector field used for weighted kinetic positivity.
The weight is the reciprocal of Lieb's
regularized potential (Lieb, 1984, Appendix A §2), journal p. 3027.
-/

public section

open scoped RealInnerProductSpace
namespace LiebThirring

/-- Lieb's bounded reciprocal-potential weight. -/
@[expose] noncomputable def ionizationWeight (ε r : ℝ) : ℝ := r / (1 + ε * r)

@[simp] theorem ionizationWeight_zero (ε : ℝ) : ionizationWeight ε 0 = 0 := by
  simp only [ionizationWeight, mul_zero, add_zero, zero_div]

theorem ionizationWeight_nonneg {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) :
    0 ≤ ionizationWeight ε r :=
  div_nonneg hr (add_nonneg zero_le_one (mul_nonneg hε hr))

theorem ionizationWeight_le_inv {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    ionizationWeight ε r ≤ ε⁻¹ := by
  have hd : 0 < 1 + ε * r := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hε.le hr)
  apply (div_le_iff₀ hd).mpr
  rw [mul_add, mul_one, inv_mul_cancel_left₀ hε.ne']
  exact le_add_of_nonneg_left (inv_nonneg.mpr hε.le)

theorem hasDerivAt_ionizationWeight {ε r : ℝ} (hd : 1 + ε * r ≠ 0) :
    HasDerivAt (ionizationWeight ε) (1 / (1 + ε * r) ^ 2) r := by
  convert (hasDerivAt_id r).div
    ((hasDerivAt_const r 1).add ((hasDerivAt_id r).const_mul ε)) hd using 1
  · rfl
  · dsimp
    ring

/-- The exact nonnegative difference between the two singular kernels. -/
theorem ionization_kernel_sub {ε r : ℝ} (hr : r ≠ 0) :
    1 / (r * (1 + ε * r) ^ 2) - 1 / (r * (1 + ε * r) ^ 3) =
      ε / (1 + ε * r) ^ 3 := by
  field_simp [hr]
  ring

theorem ionization_kernel_le {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 < r) :
    1 / (r * (1 + ε * r) ^ 3) ≤ 1 / (r * (1 + ε * r) ^ 2) := by
  have hd : 0 < 1 + ε * r := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hε hr.le)
  have hh := ionization_kernel_sub (ε := ε) hr.ne'
  have hp := div_nonneg hε (pow_nonneg hd.le 3)
  linarith only [hh, hp]

/-- The weight is 1-Lipschitz on the nonnegative radius half-line. -/
theorem abs_ionizationWeight_sub_le {ε r s : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |ionizationWeight ε r - ionizationWeight ε s| ≤ |r - s| := by
  have hdr : 0 < 1 + ε * r := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hε hr)
  have hds : 0 < 1 + ε * s := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hε hs)
  have he : ionizationWeight ε r - ionizationWeight ε s =
      (r - s) / ((1 + ε * r) * (1 + ε * s)) := by
    dsimp [ionizationWeight]
    field_simp
    ring
  rw [he, abs_div, abs_of_pos (mul_pos hdr hds)]
  apply div_le_self (abs_nonneg _)
  exact one_le_mul_of_one_le_of_one_le
    (le_add_of_nonneg_right (mul_nonneg hε hr))
    (le_add_of_nonneg_right (mul_nonneg hε hs))

/-- The spatial weight has Lipschitz constant one in the Euclidean norm. -/
theorem lipschitzWith_ionizationWeight {ε : ℝ} (hε : 0 ≤ ε) :
    LipschitzWith 1 (fun x : Position => ionizationWeight ε ‖x‖) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  exact (abs_ionizationWeight_sub_le hε (norm_nonneg x) (norm_nonneg y)).trans
    (abs_norm_sub_norm_le x y)

/-- The derivative of the radius on punctured three-dimensional space. -/
theorem hasFDerivAt_position_norm {x : Position} (hx : x ≠ 0) :
    HasFDerivAt (fun y : Position => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hh := (hasFDerivAt_id (𝕜 := ℝ) x).norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  simp only [id_eq, Real.sqrt_sq (norm_nonneg _), ContinuousLinearMap.comp_id] at hh
  convert hh using 1
  ext v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  ring

/-- A scalar radial derivative evaluated in a direction. -/
theorem fderiv_radial_apply {a : ℝ → ℝ} {a' : ℝ} {x : Position}
    (hx : x ≠ 0) (ha : HasDerivAt a a' ‖x‖) (v : Position) :
    fderiv ℝ (fun y : Position => a ‖y‖) x v = a' * inner ℝ x v / ‖x‖ := by
  have hh := ha.comp_hasFDerivAt x (hasFDerivAt_position_norm hx)
  change HasFDerivAt (fun y : Position => a ‖y‖) _ x at hh
  rw [hh.fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

/-- Derivative of a radial field component. -/
theorem fderiv_radial_component {a : ℝ → ℝ} {a' : ℝ} {x : Position}
    (hx : x ≠ 0) (ha : HasDerivAt a a' ‖x‖) (v z : Position) :
    fderiv ℝ (fun y : Position => a ‖y‖ * inner ℝ y v) x z =
      a ‖x‖ * inner ℝ z v + a' * inner ℝ x z / ‖x‖ * inner ℝ x v := by
  have hi : HasFDerivAt (fun y : Position => inner ℝ y v) (innerSL ℝ v) x := by
    simpa only [coe_innerSL_apply, real_inner_comm] using (innerSL ℝ v).hasFDerivAt (x := x)
  have hh := (ha.comp_hasFDerivAt x (hasFDerivAt_position_norm hx)).mul hi
  change HasFDerivAt (fun y : Position => a ‖y‖ * inner ℝ y v) _ x at hh
  rw [hh.fderiv]
  simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, Function.comp_apply]
  rw [real_inner_comm v z]
  ring

/-- Trace of a radial field derivative in dimension three. -/
theorem sum_fderiv_radial_component {a : ℝ → ℝ} {a' : ℝ} {x : Position}
    (hx : x ≠ 0) (ha : HasDerivAt a a' ‖x‖) :
    (∑ i : Fin 3, fderiv ℝ
      (fun y : Position => a ‖y‖ * inner ℝ y (EuclideanSpace.basisFun (Fin 3) ℝ i))
      x (EuclideanSpace.basisFun (Fin 3) ℝ i)) = 3 * a ‖x‖ + a' * ‖x‖ := by
  simp_rw [fderiv_radial_component hx ha, EuclideanSpace.inner_basisFun_real,
    EuclideanSpace.basisFun_apply, PiLp.single_apply, ite_true]
  simp only [mul_one, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  simp_rw [show ∀ i : Fin 3, a' * x i / ‖x‖ * x i = (a' / ‖x‖) * (x i) ^ 2
    from fun i => by ring]
  rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
  have hn := norm_ne_zero_iff.mpr hx
  field_simp [hn]
  ring

/-- Radial coefficient of `w A`, where `A(x) = x / |x|²`. -/
@[expose] noncomputable def ionizationFieldCoeff (ε r : ℝ) : ℝ :=
  1 / (r * (1 + ε * r))

/-- Radial coefficient of the gradient of the weight. -/
@[expose] noncomputable def ionizationGradCoeff (ε r : ℝ) : ℝ :=
  1 / (r * (1 + ε * r) ^ 2)

theorem hasDerivAt_ionizationFieldCoeff {ε r : ℝ} (hr : r ≠ 0)
    (hd : 1 + ε * r ≠ 0) :
    HasDerivAt (ionizationFieldCoeff ε)
      (-(1 + 2 * ε * r) / (r ^ 2 * (1 + ε * r) ^ 2)) r := by
  convert (hasDerivAt_const r 1).div
    ((hasDerivAt_id r).mul ((hasDerivAt_const r 1).add
      ((hasDerivAt_id r).const_mul ε))) (mul_ne_zero hr hd) using 1
  · rfl
  · dsimp
    field_simp
    ring

theorem hasDerivAt_ionizationGradCoeff {ε r : ℝ} (hr : r ≠ 0)
    (hd : 1 + ε * r ≠ 0) :
    HasDerivAt (ionizationGradCoeff ε)
      (-(1 + 3 * ε * r) / (r ^ 2 * (1 + ε * r) ^ 3)) r := by
  convert (hasDerivAt_const r 1).div
    ((hasDerivAt_id r).mul (((hasDerivAt_const r 1).add
      ((hasDerivAt_id r).const_mul ε)).pow 2))
    (mul_ne_zero hr (pow_ne_zero 2 hd)) using 1
  · rfl
  · dsimp
    field_simp [hr, hd]
    ring

theorem fderiv_ionizationWeight {ε : ℝ} (hε : 0 ≤ ε) {x : Position}
    (hx : x ≠ 0) (v : Position) :
    fderiv ℝ (fun y : Position => ionizationWeight ε ‖y‖) x v =
      ionizationGradCoeff ε ‖x‖ * inner ℝ x v := by
  have hd : 0 < 1 + ε * ‖x‖ :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hε (norm_nonneg x))
  rw [fderiv_radial_apply hx (hasDerivAt_ionizationWeight hd.ne')]
  dsimp [ionizationGradCoeff]
  field_simp [norm_ne_zero_iff.mpr hx, hd.ne']

/-- The divergence formula for `w A` on punctured space. -/
theorem sum_fderiv_ionizationField {ε : ℝ} (hε : 0 ≤ ε) {x : Position}
    (hx : x ≠ 0) :
    (∑ i : Fin 3, fderiv ℝ
      (fun y : Position => ionizationFieldCoeff ε ‖y‖ *
        inner ℝ y (EuclideanSpace.basisFun (Fin 3) ℝ i))
      x (EuclideanSpace.basisFun (Fin 3) ℝ i)) =
      ionizationGradCoeff ε ‖x‖ + ionizationFieldCoeff ε ‖x‖ := by
  have hn := norm_ne_zero_iff.mpr hx
  have hd : 0 < 1 + ε * ‖x‖ :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hε (norm_nonneg x))
  rw [sum_fderiv_radial_component hx (hasDerivAt_ionizationFieldCoeff hn hd.ne')]
  dsimp [ionizationFieldCoeff, ionizationGradCoeff]
  field_simp
  ring

/-- The trace of the derivative of the weight's gradient is its Laplacian. -/
theorem sum_fderiv_ionizationGrad {ε : ℝ} (hε : 0 ≤ ε) {x : Position}
    (hx : x ≠ 0) :
    (∑ i : Fin 3, fderiv ℝ
      (fun y : Position => ionizationGradCoeff ε ‖y‖ *
        inner ℝ y (EuclideanSpace.basisFun (Fin 3) ℝ i))
      x (EuclideanSpace.basisFun (Fin 3) ℝ i)) =
      2 / (‖x‖ * (1 + ε * ‖x‖) ^ 3) := by
  have hn := norm_ne_zero_iff.mpr hx
  have hd : 0 < 1 + ε * ‖x‖ :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hε (norm_nonneg x))
  rw [sum_fderiv_radial_component hx (hasDerivAt_ionizationGradCoeff hn hd.ne')]
  dsimp [ionizationGradCoeff]
  field_simp [hn, hd.ne']
  ring

end LiebThirring
end
