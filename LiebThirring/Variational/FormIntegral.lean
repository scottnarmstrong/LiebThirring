/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Function.L2Space

/-! # Weighted integrals for finite quadratic forms

Elementary Cauchy–Schwarz and extended-to-real facts used in Hardy estimates and form continuity.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E]

/-- Weighted Cauchy–Schwarz bounds a first moment by mass and a second moment. -/
theorem lintegral_weight_first_le {p : α → ℝ≥0∞} (hp : AEMeasurable p μ)
    {f : α → E} (hf : AEStronglyMeasurable f μ)
    (hm : (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤)
    (hs : (∫⁻ x, p x ^ 2 * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤) :
    (∫⁻ x, p x * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤ ∧
    (∫⁻ x, p x * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal ≤
      Real.sqrt (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal *
        Real.sqrt (∫⁻ x, p x ^ 2 * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal := by
  have hn := hf.nnnorm.aemeasurable.coe_nnreal_ennreal
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (hp.mul hn) hn
  simp only [Pi.mul_apply, ENNReal.rpow_two, mul_pow, mul_assoc, ← pow_two] at h
  have hfin :
      (∫⁻ x, p x ^ 2 * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) ^ (1 / (2 : ℝ)) *
        (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) ^ (1 / (2 : ℝ)) < ⊤ :=
    ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hs.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hm.ne)
  refine ⟨h.trans_lt hfin, ?_⟩
  have ht := ENNReal.toReal_mono hfin.ne h
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, mul_comm] at ht
  exact ht

/-- A finite extended weighted quadratic integral is its literal real integral. -/
theorem integral_weight_norm_sq {p : α → ℝ≥0∞} (hp : AEMeasurable p μ)
    {f : α → E} (hf : AEStronglyMeasurable f μ)
    (hfin : (∫⁻ x, p x * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤) :
    (∫ x, (p x).toReal * ‖f x‖ ^ 2 ∂μ) =
      (∫⁻ x, p x * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal := by
  have hm : AEMeasurable (fun x => p x * (‖f x‖₊ : ℝ≥0∞) ^ 2) μ :=
    hp.mul (hf.nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2)
  have ht := ae_lt_top' hm hfin.ne
  have he (x : α) : (p x * (‖f x‖₊ : ℝ≥0∞) ^ 2).toReal =
      (p x).toReal * ‖f x‖ ^ 2 := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm]
  simpa only [he] using integral_toReal hm ht

/-- Finiteness gives absolute integrability of the literal real quadratic integrand. -/
theorem integrable_weight_norm_sq {p : α → ℝ≥0∞} (hp : AEMeasurable p μ)
    {f : α → E} (hf : AEStronglyMeasurable f μ)
    (hfin : (∫⁻ x, p x * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤) :
    Integrable (fun x => (p x).toReal * ‖f x‖ ^ 2) μ := by
  have hm : AEMeasurable (fun x => p x * (‖f x‖₊ : ℝ≥0∞) ^ 2) μ :=
    hp.mul (hf.nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm]
    using integrable_toReal_of_lintegral_ne_top hm hfin.ne

variable [InnerProductSpace ℂ E]

/-- Finite quadratic expectations make the literal weighted inner product integrable. -/
theorem integrable_weight_inner {p : α → ℝ≥0∞} (hp : AEMeasurable p μ)
    {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfint : (∫⁻ x, p x * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤)
    (hgint : (∫⁻ x, p x * (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤) :
    Integrable (fun x => ((p x).toReal : ℂ) * inner ℂ (f x) (g x)) μ := by
  have hi := (integrable_weight_norm_sq hp hf hfint).add
    (integrable_weight_norm_sq hp hg hgint)
  apply hi.mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable hp.ennreal_toReal.aestronglyMeasurable).mul (hf.inner hg))
  apply Filter.Eventually.of_forall
  intro x
  simp only [Pi.mul_apply, Pi.add_apply]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  calc
    _ ≤ (p x).toReal * (‖f x‖ * ‖g x‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) ENNReal.toReal_nonneg
    _ ≤ (p x).toReal * (‖f x‖ ^ 2 + ‖g x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [sq_nonneg (‖f x‖ - ‖g x‖),
        (mul_nonneg (norm_nonneg (f x)) (norm_nonneg (g x)))]) ENNReal.toReal_nonneg
    _ = _ := mul_add _ _ _

/-- The diagonal weighted inner-product integral is the finite extended expectation. -/
theorem integral_weight_inner_self {p : α → ℝ≥0∞} (hp : AEMeasurable p μ)
    {f : α → E} (hf : AEStronglyMeasurable f μ)
    (hfin : (∫⁻ x, p x * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤) :
    (∫ x, ((p x).toReal : ℂ) * inner ℂ (f x) (f x) ∂μ) =
      ((∫⁻ x, p x * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal : ℂ) := by
  calc
    _ = ∫ x, (((p x).toReal * ‖f x‖ ^ 2 : ℝ) : ℂ) ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    _ = _ := by
      rw [integral_complex_ofReal, integral_weight_norm_sq hp hf hfin]

end LiebThirring
end
