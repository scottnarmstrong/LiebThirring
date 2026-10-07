/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormContinuity

/-! # Normalization estimates in the literal Fourier form graph norm -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

theorem escape_formGraphNorm_smul {N q : ℕ} (c : ℂ) (u : FormDomain N q) :
    formGraphNorm (c • u) = ‖c‖ * formGraphNorm u := by
  apply (sq_eq_sq₀ (formGraphNorm_nonneg _) (mul_nonneg (norm_nonneg _) (formGraphNorm_nonneg _))).mp
  rw [formGraphNorm_sq, formDomain_coe_smul, norm_smul, kineticEnergy_smul,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal]
  simp only [mul_pow, coe_nnnorm]
  rw [formGraphNorm_sq]
  ring

theorem escape_formGraphNorm_sub_comm {N q : ℕ} (u v : FormDomain N q) :
    formGraphNorm (u - v) = formGraphNorm (v - u) := by
  have he : u - v = (-1 : ℂ) • (v - u) := by rw [neg_one_smul, neg_sub]
  rw [he, escape_formGraphNorm_smul, norm_neg, norm_one, one_mul]

/-- Normalization is quantitatively continuous at a unit state in the graph norm. -/
theorem escape_formGraphNorm_normalize_le {N q : ℕ} (u v : FormDomain N q)
    (hu : ‖(u : State N q)‖ = 1)
    (hd : formGraphNorm (v - u) ≤ 1 / 2) :
    formGraphNorm (((‖(v : State N q)‖⁻¹ : ℝ) : ℂ) • v - u) ≤
      4 * formGraphNorm (v - u) * (1 + formGraphNorm u) := by
  let d := formGraphNorm (v - u)
  let a := ‖(v : State N q)‖
  have hd0 : 0 ≤ d := formGraphNorm_nonneg _
  have hna : |a - 1| ≤ d := by
    rw [← hu]
    exact (abs_norm_sub_norm_le (v : State N q) (u : State N q)).trans
      (norm_state_le_formGraphNorm (v - u))
  have ha : 1 / 2 ≤ a := by
    have h := (abs_le.mp hna).1
    linarith only [h, hd]
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hai : 0 ≤ a⁻¹ := inv_nonneg.mpr ha0.le
  have hai2 : a⁻¹ ≤ 2 := by
    simpa only [one_div, inv_inv] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) ha
  have hci : |a⁻¹ - 1| ≤ 2 * d := by
    have he : a⁻¹ - 1 = (1 - a) * a⁻¹ := by
      rw [sub_mul, one_mul, mul_inv_cancel₀ ha0.ne']
    rw [he, abs_mul, abs_of_nonneg hai, abs_sub_comm]
    exact (mul_le_mul_of_nonneg_right hna hai).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hai2 hd0)
  have he : (((a⁻¹ : ℝ) : ℂ) • v - u) =
      (((a⁻¹ : ℝ) : ℂ) • (v - u)) + ((((a⁻¹ - 1 : ℝ) : ℂ)) • u) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_one, smul_sub, sub_smul, one_smul]
    abel
  change formGraphNorm (((a⁻¹ : ℝ) : ℂ) • v - u) ≤ 4 * d * (1 + formGraphNorm u)
  rw [he]
  apply (formGraphNorm_add_le _ _).trans
  rw [escape_formGraphNorm_smul, escape_formGraphNorm_smul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hai]
  have h1 := mul_le_mul_of_nonneg_right hai2 hd0
  have h2 := mul_le_mul_of_nonneg_right hci (formGraphNorm_nonneg u)
  change 2 * (a⁻¹ * d + |a⁻¹ - 1| * formGraphNorm u) ≤ _
  nlinarith only [h1, h2]

end LiebThirring

end
