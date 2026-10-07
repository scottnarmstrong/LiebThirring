/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Screening.Rotations
public import LiebThirring.Screening.Signed
public import LiebThirring.Screening.Integrability
public import LiebThirring.Electrostatics.Gaussian
import LiebThirring.ThermoNeutral.PositiveInteraction

/-!
# Real integrals against a rotation-averaged measure

Fubini's theorem identifies averaging a separated Coulomb interaction over
spatial rotations with integration against the rotation-averaged measure.
-/

public section

open MeasureTheory Set Filter

namespace LiebThirring.ThermoNeutral

private theorem separation_le_rotated_distance
    (c d x y : Position) (Q : SpatialRotation) (r s : ℝ)
    (hx : ‖x - c‖ ≤ r) (hy : ‖y - d‖ ≤ s) :
    ‖d - c‖ - s - r ≤ ‖y - rotateAbout Q c x‖ := by
  have ht := norm_add_le (d - y) (y - rotateAbout Q c x)
  have hu := norm_add_le (d - rotateAbout Q c x) (rotateAbout Q c x - c)
  have heq : (d - y) + (y - rotateAbout Q c x) = d - rotateAbout Q c x := by
    abel
  rw [heq] at ht
  have heq' : (d - rotateAbout Q c x) + (rotateAbout Q c x - c) = d - c := by
    abel
  rw [heq'] at hu
  rw [norm_rotateAbout_sub Q c x] at hu
  have hdy : ‖d - y‖ ≤ s := by rwa [norm_sub_rev]
  linarith

private theorem integrable_rotated_kernel_at_outer
    (c d y : Position) (μ : Measure Position) [IsFiniteMeasure μ]
    {r s : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x - c‖ ≤ r) (hy : ‖y - d‖ ≤ s)
    (hsep : r + s < ‖d - c‖) :
    Integrable (fun p : SpatialRotation × Position =>
      ‖y - rotateAbout p.1 c p.2‖⁻¹) (spatialRotationMeasure.prod μ) := by
  have hδ : 0 < ‖d-c‖-s-r := by linarith
  have hQ : Measurable (fun p : SpatialRotation × Position => p.1) := measurable_fst
  have hx : Measurable (fun p : SpatialRotation × Position => p.2) := measurable_snd
  have hm : Measurable (fun p : SpatialRotation × Position =>
      ‖y - rotateAbout p.1 c p.2‖⁻¹) :=
    (measurable_const.sub ((continuous_rotateAbout c).measurable.comp (hQ.prodMk hx))).norm.inv
  apply Integrable.mono' (integrable_const ((‖d-c‖-s-r)⁻¹ : ℝ)) hm.aestronglyMeasurable
  have hμ' : ∀ᵐ p ∂spatialRotationMeasure.prod μ, ‖p.2-c‖ ≤ r :=
    (measurePreserving_snd (μ := spatialRotationMeasure) (ν := μ)).quasiMeasurePreserving.ae hμ
  filter_upwards [hμ'] with p hp
  have hd := separation_le_rotated_distance c d p.2 y p.1 r s hp hy
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact (inv_le_inv₀ (hδ.trans_le hd) hδ).2 hd

/-- Averaging the real mutual inverse-distance integral over rotations is the
same as integrating against the rotation-averaged inner measure. -/
theorem integral_rotated_eq_rotationAveragedMeasure
    (c d : Position) (μ ν : Measure Position)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {r s : ℝ}
    (hμ : ∀ᵐ x ∂μ, ‖x - c‖ ≤ r) (hν : ∀ᵐ y ∂ν, ‖y - d‖ ≤ s)
    (hsep : r + s < ‖d - c‖) :
    (∫ Q, (∫ y, ∫ x, ‖y - x‖⁻¹ ∂(μ.map (rotateAbout Q c)) ∂ν)
      ∂spatialRotationMeasure) =
      ∫ y, ∫ x, ‖y - x‖⁻¹ ∂rotationAveragedMeasure c μ ∂ν := by
  have hH : Integrable
      (fun p : SpatialRotation × Position =>
        ∫ x, ‖p.2 - rotateAbout p.1 c x‖⁻¹ ∂μ)
      (spatialRotationMeasure.prod ν) := by
    have hδ : 0 < ‖d-c‖-s-r := by linarith
    have hQ : Measurable
        (fun p : (SpatialRotation × Position) × Position => p.1.1) :=
      measurable_fst.comp measurable_fst
    have hy : Measurable
        (fun p : (SpatialRotation × Position) × Position => p.1.2) :=
      measurable_snd.comp measurable_fst
    have hx : Measurable
        (fun p : (SpatialRotation × Position) × Position => p.2) := measurable_snd
    have hrot := (continuous_rotateAbout c).measurable.comp (hQ.prodMk hx)
    have hk : Measurable (fun p : (SpatialRotation × Position) × Position =>
        ‖p.1.2 - rotateAbout p.1.1 c p.2‖⁻¹) := (hy.sub hrot).norm.inv
    apply Integrable.mono'
      (integrable_const ((‖d-c‖-s-r)⁻¹ * μ.real univ))
      (hk.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    have hν' : ∀ᵐ p ∂spatialRotationMeasure.prod ν, ‖p.2-d‖ ≤ s :=
      (measurePreserving_snd (μ := spatialRotationMeasure) (ν := ν)).quasiMeasurePreserving.ae hν
    filter_upwards [hν'] with qy hqy
    apply norm_integral_le_of_norm_le_const
    filter_upwards [hμ] with x hx'
    have hd := separation_le_rotated_distance c d x qy.2 qy.1 r s hx' hqy
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact (inv_le_inv₀ (hδ.trans_le hd) hδ).2 hd
  calc
    (∫ Q, (∫ y, ∫ x, ‖y - x‖⁻¹ ∂(μ.map (rotateAbout Q c)) ∂ν)
        ∂spatialRotationMeasure) =
        ∫ Q, ∫ y, ∫ x, ‖y - rotateAbout Q c x‖⁻¹ ∂μ ∂ν
          ∂spatialRotationMeasure := by
      apply integral_congr_ae
      filter_upwards [] with Q
      apply integral_congr_ae
      filter_upwards [] with y
      exact integral_map (measurable_rotateAbout Q c).aemeasurable
        ((measurable_const.sub measurable_id).norm.inv.aestronglyMeasurable)
    _ = ∫ y, ∫ Q, ∫ x, ‖y - rotateAbout Q c x‖⁻¹ ∂μ
          ∂spatialRotationMeasure ∂ν :=
      integral_integral_swap hH
    _ = ∫ y, ∫ p : SpatialRotation × Position,
          ‖y - rotateAbout p.1 c p.2‖⁻¹ ∂(spatialRotationMeasure.prod μ) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hν] with y hy
      exact (integral_prod _
        (integrable_rotated_kernel_at_outer c d y μ hμ hy hsep)).symm
    _ = ∫ y, ∫ x, ‖y - x‖⁻¹ ∂rotationAveragedMeasure c μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with y
      unfold rotationAveragedMeasure
      exact (integral_map (continuous_rotateAbout c).measurable.aemeasurable
        ((measurable_const.sub measurable_id).norm.inv.aestronglyMeasurable)).symm

end LiebThirring.ThermoNeutral

end
