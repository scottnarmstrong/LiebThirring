/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormIntegral

/-! # Weighted Cauchy–Schwarz for the literal complex form -/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

omit [InnerProductSpace ℂ E] in
/-- Weighted amplitudes belong to scalar L² when the quadratic expectation is finite. -/
theorem memLp_sqrt_weight_norm {p : α → ℝ≥0∞} (hp : AEMeasurable p μ)
    {f : α → E} (hf : AEStronglyMeasurable f μ)
    (hfin : (∫⁻ x, p x * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤) :
    MemLp (fun x => Real.sqrt (p x).toReal * ‖f x‖) 2 μ := by
  have hm : AEStronglyMeasurable (fun x => Real.sqrt (p x).toReal * ‖f x‖) μ :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable
      hp.ennreal_toReal.aestronglyMeasurable).mul hf.norm
  apply (memLp_two_iff_integrable_sq hm).mpr
  have he (x : α) : (Real.sqrt (p x).toReal * ‖f x‖) ^ 2 =
      (p x).toReal * ‖f x‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  simpa only [he] using integrable_weight_norm_sq hp hf hfin

/-- Absolute value of the weighted pairing is bounded by its two quadratic expectations. -/
theorem norm_integral_weight_inner_le {p : α → ℝ≥0∞} (hp : AEMeasurable p μ)
    {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfint : (∫⁻ x, p x * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤)
    (hgint : (∫⁻ x, p x * (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤) :
    ‖∫ x, ((p x).toReal : ℂ) * inner ℂ (f x) (g x) ∂μ‖ ≤
      Real.sqrt (∫⁻ x, p x * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal *
        Real.sqrt (∫⁻ x, p x * (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal := by
  let a : α → ℝ := fun x => Real.sqrt (p x).toReal * ‖f x‖
  let b : α → ℝ := fun x => Real.sqrt (p x).toReal * ‖g x‖
  have ha := memLp_sqrt_weight_norm hp hf hfint
  have hb := memLp_sqrt_weight_norm hp hg hgint
  have ha0 (x : α) : 0 ≤ a x := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hb0 (x : α) : 0 ≤ b x := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have he (x : α) : a x * b x = (p x).toReal * (‖f x‖ * ‖g x‖) := by
    dsimp only [a, b]
    rw [mul_mul_mul_comm, ← pow_two, Real.sq_sqrt ENNReal.toReal_nonneg]
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp a (ENNReal.ofReal 2) μ by simpa only [ENNReal.ofReal_ofNat] using ha)
    (show MemLp b (ENNReal.ofReal 2) μ by simpa only [ENNReal.ofReal_ofNat] using hb)
  simp only [Real.norm_eq_abs, abs_of_nonneg (ha0 _), abs_of_nonneg (hb0 _)] at hcs
  have hcs' : (∫ x, a x * b x ∂μ) ≤
      Real.sqrt (∫ x, (p x).toReal * ‖f x‖ ^ 2 ∂μ) *
        Real.sqrt (∫ x, (p x).toReal * ‖g x‖ ^ 2 ∂μ) := by
    simpa only [← Real.sqrt_eq_rpow, Real.rpow_two, a, b, mul_pow,
      Real.sq_sqrt ENNReal.toReal_nonneg] using hcs
  rw [integral_weight_norm_sq hp hf hfint, integral_weight_norm_sq hp hg hgint] at hcs'
  apply (norm_integral_le_integral_norm _).trans
  refine (integral_mono_ae (integrable_weight_inner hp hf hg hfint hgint).norm
    (ha.integrable_mul hb) ?_).trans hcs'
  apply Filter.Eventually.of_forall
  intro x
  change ‖((p x).toReal : ℂ) * inner ℂ (f x) (g x)‖ ≤ a x * b x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, he]
  exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) ENNReal.toReal_nonneg

end LiebThirring
end
