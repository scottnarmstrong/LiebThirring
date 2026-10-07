/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.TrialDensities
public import LiebThirring.TFFunctional.CoulombBounds
public import LiebThirring.Screening.Newton
import all LiebThirring.Electrostatics.Basic

/-! # A proportional-thickness radial annulus trial

The literal indicator of `L ≤ |x| < 2L` is a TF density. Newton
makes its potential constant in the cavity and maximal there. Its mass is
`7 |B₁| L³`.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LiebThirring.TFMinimizer

open TFFunctional

@[expose] def tfAnnulus (L : ℝ) : Set Position := ball 0 (2 * L) \ ball 0 L

theorem measurableSet_tfAnnulus (L : ℝ) : MeasurableSet (tfAnnulus L) :=
  MeasurableSet.diff measurableSet_ball measurableSet_ball

theorem volume_tfAnnulus_ne_top (L : ℝ) : volume (tfAnnulus L) ≠ ⊤ :=
  (lt_of_le_of_lt (measure_mono sdiff_subset) (by rw [volume_ball_position]; finiteness)).ne

@[expose] noncomputable def tfAnnulusDensity (L : ℝ) : TFDensity :=
  tfIndicatorDensity (tfAnnulus L) (measurableSet_tfAnnulus L) (volume_tfAnnulus_ne_top L) 1

theorem tfAnnulusDensity_apply_ae (L : ℝ) :
    (tfAnnulusDensity L).val =ᵐ[volume] (tfAnnulus L).indicator (fun _ => (1 : ℝ)) :=
  tfIndicatorDensity_coeFn _ _ _ _

theorem tfDensityMeasure_tfAnnulusDensity (L : ℝ) :
    tfDensityMeasure (tfAnnulusDensity L) = volume.restrict (tfAnnulus L) := by
  change volume.withDensity (fun x : Position => ENNReal.ofReal ((tfAnnulusDensity L).val x)) = _
  calc
    _ = volume.withDensity ((tfAnnulus L).indicator (fun _ => (1 : ℝ≥0∞))) := by
      apply withDensity_congr_ae
      filter_upwards [tfAnnulusDensity_apply_ae L] with x hx
      rw [hx]
      by_cases hxs : x ∈ tfAnnulus L <;> simp [hxs]
    _ = _ := withDensity_indicator_one (measurableSet_tfAnnulus L)

theorem volume_real_tfAnnulus (L : ℝ) (hL : 0 < L) :
    volume.real (tfAnnulus L) = 7 * ballVolumeConstant * L ^ 3 := by
  rw [tfAnnulus, measureReal_sdiff (ball_subset_ball (by linarith : L ≤ 2 * L))
    measurableSet_ball (by rw [volume_ball_position]; finiteness),
    volume_real_ball_position _ (by positivity : 0 ≤ 2 * L),
    volume_real_ball_position _ hL.le]
  ring

theorem tfMass_tfAnnulusDensity (L : ℝ) (hL : 0 < L) :
    tfMass (tfAnnulusDensity L) = 7 * ballVolumeConstant * L ^ 3 := by
  rw [tfAnnulusDensity, tfMass_tfIndicatorDensity, volume_real_tfAnnulus L hL]
  simp only [NNReal.coe_one, mul_one]

theorem isRadial_tfAnnulusDensity (L : ℝ) : IsRadial 0 (tfDensityMeasure (tfAnnulusDensity L)) := by
  rw [tfDensityMeasure_tfAnnulusDensity]
  intro Q _
  have hpre : Q ⁻¹' tfAnnulus L = tfAnnulus L := by
    ext x
    simp only [tfAnnulus, mem_preimage, mem_sdiff, mem_ball, dist_zero_right, Q.norm_map]
  change (volume.restrict (tfAnnulus L)).map (fun x : Position => 0 + Q (x - 0)) = _
  simp only [zero_add, sub_zero]
  calc
    _ = ((volume : Measure Position).map Q).restrict (tfAnnulus L) := by
      rw [Measure.restrict_map Q.continuous.measurable (measurableSet_tfAnnulus L), hpre]
    _ = _ := by rw [Q.measurePreserving.map_eq]

theorem tfAnnulusDensity_radius_ae (L : ℝ) :
    ∀ᵐ x ∂tfDensityMeasure (tfAnnulusDensity L), L ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * L := by
  rw [tfDensityMeasure_tfAnnulusDensity]
  filter_upwards [ae_restrict_mem (measurableSet_tfAnnulus L)] with x hx
  have hn : ‖x‖ < 2 * L ∧ L ≤ ‖x‖ := by
    simpa only [tfAnnulus, mem_sdiff, mem_ball, dist_zero_right, not_lt] using hx
  exact ⟨hn.2, hn.1.le⟩

theorem potential_tfAnnulusDensity_cavity (L : ℝ) (x : Position) (hx : ‖x‖ ≤ L) :
    coulombPotential (tfDensityMeasure (tfAnnulusDensity L)) x =
      coulombPotential (tfDensityMeasure (tfAnnulusDensity L)) 0 := by
  rw [coulombPotential_radial 0 x _ (isRadial_tfAnnulusDensity L),
    coulombPotential_radial 0 0 _ (isRadial_tfAnnulusDensity L)]
  apply lintegral_congr_ae
  filter_upwards [tfAnnulusDensity_radius_ae L] with y hy
  simp only [sub_zero, norm_zero, max_eq_right (hx.trans hy.1),
    max_eq_right (norm_nonneg y)]

theorem potential_tfAnnulusDensity_le_center (L : ℝ) (x : Position) :
    coulombPotential (tfDensityMeasure (tfAnnulusDensity L)) x ≤
      coulombPotential (tfDensityMeasure (tfAnnulusDensity L)) 0 := by
  rw [coulombPotential_radial 0 x _ (isRadial_tfAnnulusDensity L),
    coulombPotential_radial 0 0 _ (isRadial_tfAnnulusDensity L)]
  apply lintegral_mono
  intro y
  simp only [sub_zero, norm_zero, max_eq_right (norm_nonneg y)]
  exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (le_max_right _ _))

theorem mass_div_le_potential_tfAnnulusDensity_center (L : ℝ) (hL : 0 < L) :
    tfMass (tfAnnulusDensity L) / (2 * L) ≤
      (coulombPotential (tfDensityMeasure (tfAnnulusDensity L)) 0).toReal := by
  have hp : (ENNReal.ofReal (2 * L))⁻¹ * tfDensityMeasure (tfAnnulusDensity L) univ ≤
      coulombPotential (tfDensityMeasure (tfAnnulusDensity L)) 0 := by
    rw [coulombPotential_radial 0 0 _ (isRadial_tfAnnulusDensity L)]
    calc
      _ = ∫⁻ _y : Position, (ENNReal.ofReal (2 * L))⁻¹
          ∂tfDensityMeasure (tfAnnulusDensity L) := (lintegral_const _).symm
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [tfAnnulusDensity_radius_ae L] with y hy
        simp only [sub_zero, norm_zero, max_eq_right (norm_nonneg y)]
        exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hy.2)
  have h := ENNReal.toReal_mono
    (coulombPotential_tfDensityMeasure_lt_top (tfAnnulusDensity L) 0).ne hp
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, tfDensityMeasure_univ,
    ENNReal.toReal_ofReal (tfMass_nonneg _), ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * L)] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

end LiebThirring.TFMinimizer

end
