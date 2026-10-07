/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.CompactApproximationBounded

/-! # An L1-to-L5/3 bound for uniformly bounded errors -/

public section

open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.TFFunctional

/-- Interpolation between L1 and a pointwise bound, specialized to exponent `5/3`. -/
theorem eLpNorm_five_thirds_le_of_ae_norm_le (e : Position → ℝ)
    (he : AEStronglyMeasurable e volume) (C : ℝ≥0)
    (hC : ∀ᵐ x ∂volume, ‖e x‖ ≤ (C : ℝ)) :
    eLpNorm e ((5 : ℝ≥0∞) / 3) volume ≤
      (((C : ℝ≥0∞) ^ ((2 : ℝ) / 3) * eLpNorm e 1 volume) ^ ((3 : ℝ) / 5)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num)
    (ENNReal.div_ne_top (by norm_num) (by norm_num)) he]
  have hp : (((5 : ℝ≥0∞) / 3).toReal) = (5 : ℝ) / 3 := by
    norm_num [ENNReal.toReal_div]
  rw [hp]
  rw [show (1 / ((5 : ℝ) / 3)) = (3 : ℝ) / 5 by norm_num]
  apply ENNReal.rpow_le_rpow
  calc
    (∫⁻ x, ‖e x‖ₑ ^ ((5 : ℝ) / 3) ∂volume) ≤
        ∫⁻ x, (C : ℝ≥0∞) ^ ((2 : ℝ) / 3) * ‖e x‖ₑ ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [hC] with x hx
      rw [show (5 : ℝ) / 3 = (2 : ℝ) / 3 + 1 by ring,
        ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
        ENNReal.rpow_one]
      apply mul_le_mul_left
      apply ENNReal.rpow_le_rpow
      · exact_mod_cast hx
      · norm_num
    _ = (C : ℝ≥0∞) ^ ((2 : ℝ) / 3) * eLpNorm e 1 volume := by
      rw [lintegral_const_mul'' _ he.enorm,
        eLpNorm_one_eq_lintegral_enorm he]
  norm_num

/-- A bounded nonnegative integrable function admits one compact continuous
nonnegative approximation simultaneously in L1 and L5/3. -/
theorem exists_compact_nonneg_joint_approximation_of_bounded
    (u : Position → ℝ) (hu : Integrable u volume) (C : ℝ≥0)
    (hu0 : ∀ᵐ x ∂volume, 0 ≤ u x) (huC : ∀ᵐ x ∂volume, u x ≤ (C : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : Position → ℝ, (∀ x, 0 ≤ f x) ∧ Continuous f ∧ HasCompactSupport f ∧
      eLpNorm (f - u) ((5 : ℝ≥0∞) / 3) volume ≤ ENNReal.ofReal ε ∧
      eLpNorm (f - u) 1 volume ≤ ENNReal.ofReal ε := by
  let E : ℝ≥0∞ := ENNReal.ofReal ε
  let X : ℝ≥0∞ := (C : ℝ≥0∞) ^ ((2 : ℝ) / 3)
  let δ : ℝ≥0∞ := min E (E ^ ((5 : ℝ) / 3) / (X + 1))
  have hE : E ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  have hXtop : X ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.coe_ne_top
  have hδ : δ ≠ 0 := by
    dsimp [δ]
    simp only [min_eq_zero, hE, false_or]
    exact (ENNReal.div_ne_zero).2
      ⟨(ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hE) (by simp [E])).ne', by simp [hXtop]⟩
  obtain ⟨f, hf0, hfcont, hfcomp, hf1, hfC⟩ :=
    exists_compact_nonneg_eLpNorm_one_approximation u hu C C.property hu0 huC δ hδ
  refine ⟨f, hf0, hfcont, hfcomp, ?_, hf1.trans (min_le_left _ _)⟩
  have hbound : ∀ᵐ x ∂volume, ‖(f - u) x‖ ≤ (C : ℝ) := by
    filter_upwards [hu0, huC] with x hx0 hxC
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hf0 x, hfC x], by linarith [hf0 x, hfC x]⟩
  calc
    eLpNorm (f - u) ((5 : ℝ≥0∞) / 3) volume ≤
        (X * eLpNorm (f - u) 1 volume) ^ ((3 : ℝ) / 5) := by
      simpa only [X] using eLpNorm_five_thirds_le_of_ae_norm_le
        (f - u) (hfcont.aestronglyMeasurable.sub hu.aestronglyMeasurable) C hbound
    _ ≤ (X * δ) ^ ((3 : ℝ) / 5) := ENNReal.rpow_le_rpow
      (by gcongr) (by norm_num)
    _ ≤ (E ^ ((5 : ℝ) / 3)) ^ ((3 : ℝ) / 5) := by
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      calc
        X * δ ≤ X * (E ^ ((5 : ℝ) / 3) / (X + 1)) := by
          gcongr
          exact min_le_right _ _
        _ = E ^ ((5 : ℝ) / 3) * (X / (X + 1)) := by
          simp only [div_eq_mul_inv]
          ac_rfl
        _ ≤ E ^ ((5 : ℝ) / 3) := by
          nth_rewrite 2 [← mul_one (E ^ ((5 : ℝ) / 3))]
          gcongr
          apply (ENNReal.div_le_iff_le_mul (Or.inl (by simp))
            (Or.inl (by simpa using ENNReal.add_ne_top.mpr ⟨hXtop, ENNReal.one_ne_top⟩))).2
          simp
    _ = E := by
      rw [← ENNReal.rpow_mul]
      norm_num

end LiebThirring.TFFunctional

end
