/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.Mass
public import LiebThirring.ThomasFermi.DensityMeasure

/-! # Elementary properties of Thomas--Fermi densities -/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace LiebThirring.TFFunctional

theorem tfDensity_ae_nonneg (ρ : TFDensity) :
    ∀ᵐ x ∂(volume : Measure Position), 0 ≤ ρ.val x :=
  ρ.property.1

theorem integrable_tfDensity (ρ : TFDensity) :
    Integrable (fun x : Position => ρ.val x) volume :=
  ρ.property.2

theorem tfMass_nonneg (ρ : TFDensity) : 0 ≤ tfMass ρ := by
  unfold tfMass
  exact integral_nonneg_of_ae (tfDensity_ae_nonneg ρ)

theorem lintegral_ofReal_tfDensity_lt_top (ρ : TFDensity) :
    (∫⁻ x : Position, ENNReal.ofReal (ρ.val x) ∂volume) < ⊤ := by
  have hi : (∫⁻ x : Position, ‖ρ.val x‖ₑ ∂volume) < ⊤ :=
    (integrable_tfDensity ρ).hasFiniteIntegral
  apply lt_of_le_of_lt ?_ hi
  apply lintegral_mono_ae
  filter_upwards with x
  exact Real.ofReal_le_enorm _

noncomputable instance instIsFiniteMeasureTfDensityMeasure (ρ : TFDensity) :
    IsFiniteMeasure (tfDensityMeasure ρ) := by
  unfold tfDensityMeasure
  exact MeasureTheory.isFiniteMeasure_withDensity (lintegral_ofReal_tfDensity_lt_top ρ).ne

theorem tfDensityMeasure_univ (ρ : TFDensity) :
    tfDensityMeasure ρ univ = ENNReal.ofReal (tfMass ρ) := by
  unfold tfDensityMeasure tfMass
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_tfDensity ρ)
    (tfDensity_ae_nonneg ρ)]

theorem integrable_tfDensity_rpow_five_thirds (ρ : TFDensity) :
    Integrable (fun x : Position => (ρ.val x) ^ ((5 : ℝ) / 3)) volume := by
  have hp0 : (5 : ℝ≥0∞) / 3 ≠ 0 := by norm_num
  have hpt : (5 : ℝ≥0∞) / 3 ≠ ∞ := ENNReal.div_ne_top (by norm_num) (by norm_num)
  have h := (Lp.memLp ρ.val).integrable_norm_rpow hp0 hpt
  apply h.congr
  filter_upwards [tfDensity_ae_nonneg ρ] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx, ENNReal.toReal_div]
  norm_num

theorem integral_tfDensity_rpow_five_thirds_nonneg (ρ : TFDensity) :
    0 ≤ ∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3) := by
  apply integral_nonneg_of_ae
  filter_upwards [tfDensity_ae_nonneg ρ] with x hx
  exact Real.rpow_nonneg hx _

theorem integral_tfDensity_rpow_eq_norm (ρ : TFDensity) :
    (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) =
      ‖ρ.val‖ ^ ((5 : ℝ) / 3) := by
  have hp0 : (5 : ℝ≥0∞) / 3 ≠ 0 := by norm_num
  have hpt : (5 : ℝ≥0∞) / 3 ≠ ∞ := ENNReal.div_ne_top (by norm_num) (by norm_num)
  have he := (Lp.memLp ρ.val).eLpNorm_eq_integral_rpow_norm hp0 hpt
  have hi : 0 ≤ ∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3) :=
    integral_tfDensity_rpow_five_thirds_nonneg ρ
  have hint : (∫ x : Position, ‖ρ.val x‖ ^ (((5 : ℝ≥0∞) / 3).toReal)) =
      ∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3) := by
    apply integral_congr_ae
    filter_upwards [tfDensity_ae_nonneg ρ] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx, ENNReal.toReal_div]
    norm_num
  have hexp : (((5 : ℝ≥0∞) / 3).toReal)⁻¹ = (3 : ℝ) / 5 := by
    rw [ENNReal.toReal_div]
    norm_num
  have hn : ‖ρ.val‖ =
      (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) ^ ((3 : ℝ) / 5) := by
    rw [Lp.norm_def, he, hint, hexp, ENNReal.toReal_ofReal (Real.rpow_nonneg hi _)]
  rw [hn, ← Real.rpow_mul hi]
  norm_num

end LiebThirring.TFFunctional

end
