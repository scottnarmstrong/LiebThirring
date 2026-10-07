/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.WeightedPuncture
public import LiebThirring.Analysis.FundamentalSolutionIntegrability

/-!
# Local integrability of the ionization fields

The kernels and the derivatives of both radial fields are dominated by a
constant times the locally integrable three-dimensional Coulomb kernel.
-/

public section
open MeasureTheory
open scoped RealInnerProductSpace
namespace LiebThirring

/-- Every denominator power in weighted positivity only decreases the Coulomb singularity. -/
theorem locallyIntegrable_ionization_kernel {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) :
    LocallyIntegrable (fun x : Position => 1 / (‖x‖ * (1 + ε * ‖x‖) ^ k)) := by
  have hi : LocallyIntegrable (fun x : Position => ‖x‖⁻¹) := by
    simpa only [sub_zero] using locallyIntegrable_inv_norm_sub (0 : Position)
  apply hi.mono
  · have hm : Measurable (fun x : Position => 1 / (‖x‖ * (1 + ε * ‖x‖) ^ k)) := by
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [show ∀ᵐ x : Position, x ≠ 0 by rw [ae_iff]; simp] with x hx
    have hr := norm_pos_iff.mpr hx
    have hd : 1 ≤ 1 + ε * ‖x‖ := le_add_of_nonneg_right (mul_nonneg hε hr.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hr.le), ← one_div]
    exact one_div_le_one_div_of_le hr (le_mul_of_one_le_right hr.le (one_le_pow₀ hd))

/-- A pure scalar bound for the two coordinate derivatives. -/
theorem ionization_diagonal_abs_le {r t z : ℝ} (hr : 0 < r) (ht : 0 ≤ t)
    (hz : z ^ 2 ≤ r ^ 2) (k n : ℕ) :
    |1 / (r * (1 + t) ^ k) - (1 + n * t) * z ^ 2 / (r ^ 3 * (1 + t) ^ n)| ≤ 2 / r := by
  have hd : 1 ≤ 1 + t := le_add_of_nonneg_right ht
  have hp := lt_of_lt_of_le zero_lt_one hd
  have hb : 1 + n * t ≤ (1 + t) ^ n := one_add_mul_le_pow (by linarith only [ht]) n
  have hn : 0 ≤ 1 + (n : ℝ) * t := by positivity
  have h₁ : 1 / (r * (1 + t) ^ k) ≤ 1 / r :=
    one_div_le_one_div_of_le hr (le_mul_of_one_le_right hr.le (one_le_pow₀ hd))
  have h₂ : (1 + n * t) * z ^ 2 / (r ^ 3 * (1 + t) ^ n) ≤ 1 / r := by
    apply (div_le_iff₀ (mul_pos (pow_pos hr 3) (pow_pos hp n))).mpr
    have he : 1 / r * (r ^ 3 * (1 + t) ^ n) = r ^ 2 * (1 + t) ^ n := by
      field_simp

    rw [he, mul_comm (r ^ 2)]
    exact mul_le_mul hb hz (sq_nonneg z) (pow_nonneg hp.le n)
  calc
    _ ≤ |1 / (r * (1 + t) ^ k)| + |(1 + n * t) * z ^ 2 / (r ^ 3 * (1 + t) ^ n)| :=
      abs_sub _ _
    _ = 1 / (r * (1 + t) ^ k) + (1 + n * t) * z ^ 2 / (r ^ 3 * (1 + t) ^ n) := by
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    _ ≤ 1 / r + 1 / r := add_le_add h₁ h₂
    _ = 2 / r := by ring

/-- Local integrability of a coordinate derivative of the weighted Hardy field. -/
theorem locallyIntegrable_fderiv_ionizationField {ε : ℝ} (hε : 0 ≤ ε) (i : Fin 3) :
    LocallyIntegrable (fun x : Position => fderiv ℝ
      (fun y : Position => ionizationFieldCoeff ε ‖y‖ *
        inner ℝ y (EuclideanSpace.basisFun (Fin 3) ℝ i))
      x (EuclideanSpace.basisFun (Fin 3) ℝ i)) := by
  have hi : LocallyIntegrable (fun x : Position => 2 * ‖x‖⁻¹) := by
    have hh := (locallyIntegrable_inv_norm_sub (0 : Position)).smul (2 : ℝ)
    change LocallyIntegrable (fun x : Position => (2 : ℝ) • ‖x - 0‖⁻¹) at hh
    simpa only [sub_zero, smul_eq_mul] using hh
  apply hi.mono
  · exact (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable
  · filter_upwards [show ∀ᵐ x : Position, x ≠ 0 by rw [ae_iff]; simp] with x hx
    have hr := norm_pos_iff.mpr hx
    have hd : 0 < 1 + ε * ‖x‖ := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hε hr.le)
    rw [fderiv_radial_component hx (hasDerivAt_ionizationFieldCoeff hr.ne' hd.ne')]
    simp_rw [EuclideanSpace.inner_basisFun_real, EuclideanSpace.basisFun_apply,
      PiLp.single_apply, ite_true, mul_one, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hr.le))]
    have hz : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
      have hh : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x i)) hh 2
    have he : ionizationFieldCoeff ε ‖x‖ +
        (-(1 + 2 * ε * ‖x‖) / (‖x‖ ^ 2 * (1 + ε * ‖x‖) ^ 2)) * x i / ‖x‖ * x i =
        1 / (‖x‖ * (1 + ε * ‖x‖) ^ 1) -
          (1 + (2 : ℕ) * (ε * ‖x‖)) * (x i) ^ 2 / (‖x‖ ^ 3 * (1 + ε * ‖x‖) ^ 2) := by
      dsimp [ionizationFieldCoeff]
      field_simp
      ring
    rw [he]
    simpa only [div_eq_mul_inv, Nat.cast_ofNat] using
      ionization_diagonal_abs_le hr (mul_nonneg hε hr.le) hz 1 2

/-- Local integrability of a coordinate derivative of the weight gradient. -/
theorem locallyIntegrable_fderiv_ionizationGrad {ε : ℝ} (hε : 0 ≤ ε) (i : Fin 3) :
    LocallyIntegrable (fun x : Position => fderiv ℝ
      (fun y : Position => ionizationGradCoeff ε ‖y‖ *
        inner ℝ y (EuclideanSpace.basisFun (Fin 3) ℝ i))
      x (EuclideanSpace.basisFun (Fin 3) ℝ i)) := by
  have hi : LocallyIntegrable (fun x : Position => 2 * ‖x‖⁻¹) := by
    have hh := (locallyIntegrable_inv_norm_sub (0 : Position)).smul (2 : ℝ)
    change LocallyIntegrable (fun x : Position => (2 : ℝ) • ‖x - 0‖⁻¹) at hh
    simpa only [sub_zero, smul_eq_mul] using hh
  apply hi.mono
  · exact (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable
  · filter_upwards [show ∀ᵐ x : Position, x ≠ 0 by rw [ae_iff]; simp] with x hx
    have hr := norm_pos_iff.mpr hx
    have hd : 0 < 1 + ε * ‖x‖ := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hε hr.le)
    rw [fderiv_radial_component hx (hasDerivAt_ionizationGradCoeff hr.ne' hd.ne')]
    simp_rw [EuclideanSpace.inner_basisFun_real, EuclideanSpace.basisFun_apply,
      PiLp.single_apply, ite_true, mul_one, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hr.le))]
    have hz : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
      have hh : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x i)) hh 2
    have he : ionizationGradCoeff ε ‖x‖ +
        (-(1 + 3 * ε * ‖x‖) / (‖x‖ ^ 2 * (1 + ε * ‖x‖) ^ 3)) * x i / ‖x‖ * x i =
        1 / (‖x‖ * (1 + ε * ‖x‖) ^ 2) -
          (1 + (3 : ℕ) * (ε * ‖x‖)) * (x i) ^ 2 / (‖x‖ ^ 3 * (1 + ε * ‖x‖) ^ 3) := by
      dsimp [ionizationGradCoeff]
      field_simp
      ring
    rw [he]
    simpa only [div_eq_mul_inv, Nat.cast_ofNat] using
      ionization_diagonal_abs_le hr (mul_nonneg hε hr.le) hz 2 3

/-- Local integrability of a component of the weighted Hardy field. -/
theorem locallyIntegrable_ionizationField {ε : ℝ} (hε : 0 ≤ ε) (i : Fin 3) :
    LocallyIntegrable (fun x : Position => ionizationFieldCoeff ε ‖x‖ *
      inner ℝ x (EuclideanSpace.basisFun (Fin 3) ℝ i)) := by
  simpa only [ionizationFieldCoeff, pow_one, id_eq] using
    (locallyIntegrable_ionization_kernel hε 1).mul_continuous
      (continuous_id.inner (continuous_const (y := EuclideanSpace.basisFun (Fin 3) ℝ i)))

/-- Local integrability of a component of the weight gradient. -/
theorem locallyIntegrable_ionizationGrad {ε : ℝ} (hε : 0 ≤ ε) (i : Fin 3) :
    LocallyIntegrable (fun x : Position => ionizationGradCoeff ε ‖x‖ *
      inner ℝ x (EuclideanSpace.basisFun (Fin 3) ℝ i)) :=
  (locallyIntegrable_ionization_kernel hε 2).mul_continuous
    ((continuous_id.inner continuous_const))

end LiebThirring
end
