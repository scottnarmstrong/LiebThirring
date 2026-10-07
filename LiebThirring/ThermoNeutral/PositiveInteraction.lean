/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Screening.Rotations
public import LiebThirring.Screening.Integrability

/-!
# Positive Coulomb interactions of independently rotated measures

The literal pushforward interaction used by the neutral variational packing.
Inner closed-ball support and a strict centre gap give a bound uniform in
both rotations. No regularity of the charge measures beyond finiteness is needed.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace LiebThirring.ThermoNeutral

/-- Mutual Coulomb interaction, with the first measure integrated inside. -/
noncomputable def mutualInteraction (μ ν : Measure Position) : ℝ :=
  ∫ y, ∫ x, ‖y - x‖⁻¹ ∂μ ∂ν

/-- The interaction after independently rotating each measure about its centre. -/
noncomputable def rotatedMutualInteraction (c d : Position) (μ ν : Measure Position)
    (Q R : SpatialRotation) : ℝ :=
  ∫ y, ∫ x, ‖rotateAbout R d y - rotateAbout Q c x‖⁻¹ ∂μ ∂ν

theorem measurable_rotateAbout (Q : SpatialRotation) (c : Position) :
    Measurable (rotateAbout Q c) :=
  ((continuous_rotateAbout c).comp (continuous_const.prodMk continuous_id)).measurable

theorem rotatedMutualInteraction_eq_map (c d : Position) (μ ν : Measure Position)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (Q R : SpatialRotation) :
    rotatedMutualInteraction c d μ ν Q R =
      mutualInteraction (μ.map (rotateAbout Q c)) (ν.map (rotateAbout R d)) := by
  unfold rotatedMutualInteraction mutualInteraction
  rw [integral_map (measurable_rotateAbout R d).aemeasurable]
  · apply integral_congr_ae
    filter_upwards [] with y
    exact (integral_map (measurable_rotateAbout Q c).aemeasurable
      ((measurable_const.sub measurable_id).norm.inv.aestronglyMeasurable)).symm
  · exact (((measurable_fst.sub measurable_snd).norm.inv.stronglyMeasurable).integral_prod_right').aestronglyMeasurable

/-- A quantitative gap for all rotated points in the two inner balls. -/
theorem rotated_distance_ge_gap (c d x y : Position) (Q R : SpatialRotation)
    {r s : ℝ} (hx : ‖x-c‖ ≤ r) (hy : ‖y-d‖ ≤ s) :
    ‖d-c‖ - r - s ≤ ‖rotateAbout R d y - rotateAbout Q c x‖ := by
  have htri : ‖d-c‖ ≤ ‖rotateAbout R d y - d‖ +
      ‖rotateAbout R d y - rotateAbout Q c x‖ + ‖rotateAbout Q c x - c‖ := by
    calc
      _ ≤ ‖d - rotateAbout R d y‖ + ‖rotateAbout R d y - c‖ := by
        simpa only [sub_add_sub_cancel] using
          norm_add_le (d - rotateAbout R d y) (rotateAbout R d y - c)
      _ ≤ _ := by
        have hh := norm_add_le (rotateAbout R d y - rotateAbout Q c x)
          (rotateAbout Q c x - c)
        rw [sub_add_sub_cancel] at hh
        rw [norm_sub_rev d (rotateAbout R d y)]
        linarith only [hh]
  rw [norm_rotateAbout_sub, norm_rotateAbout_sub] at htri
  linarith only [hx, hy, htri]

theorem measurable_rotatedMutualInteraction (c d : Position) (μ ν : Measure Position)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Measurable (fun p : SpatialRotation × SpatialRotation =>
      rotatedMutualInteraction c d μ ν p.1 p.2) := by
  have hQ : Measurable (fun p : ((SpatialRotation × SpatialRotation) × Position) × Position =>
      p.1.1.2) := measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hy : Measurable (fun p : ((SpatialRotation × SpatialRotation) × Position) × Position =>
      p.1.2) := measurable_snd.comp measurable_fst
  have hR : Measurable (fun p : ((SpatialRotation × SpatialRotation) × Position) × Position =>
      p.1.1.1) := measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hx : Measurable (fun p : ((SpatialRotation × SpatialRotation) × Position) × Position =>
      p.2) := measurable_snd
  have h1 := (continuous_rotateAbout d).measurable.comp (hQ.prodMk hy)
  have h2 := (continuous_rotateAbout c).measurable.comp (hR.prodMk hx)
  exact ((((h1.sub h2).norm.inv.stronglyMeasurable).integral_prod_right').integral_prod_right').measurable

theorem integrable_rotated_kernel (c d : Position) (μ ν : Measure Position)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {r s : ℝ} (hcent : r+s < ‖d-c‖)
    (hμ : ∀ᵐ x ∂μ, ‖x-c‖ ≤ r) (hν : ∀ᵐ y ∂ν, ‖y-d‖ ≤ s)
    (Q R : SpatialRotation) :
    Integrable (fun p : Position × Position =>
      ‖rotateAbout R d p.1 - rotateAbout Q c p.2‖⁻¹) (ν.prod μ) := by
  have hδ : 0 < ‖d-c‖ - r - s := by linarith only [hcent]
  have hm : Measurable (fun p : Position × Position =>
      ‖rotateAbout R d p.1 - rotateAbout Q c p.2‖⁻¹) :=
    (((measurable_rotateAbout R d).comp measurable_fst).sub
      ((measurable_rotateAbout Q c).comp measurable_snd)).norm.inv
  apply Integrable.mono' (integrable_const ((‖d-c‖-r-s)⁻¹ : ℝ)) hm.aestronglyMeasurable
  have hae : ∀ᵐ p ∂ν.prod μ, ‖d-c‖-r-s ≤
      ‖rotateAbout R d p.1 - rotateAbout Q c p.2‖ := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le measurable_const
        ((((measurable_rotateAbout R d).comp measurable_fst).sub
          ((measurable_rotateAbout Q c).comp measurable_snd)).norm))).2
    filter_upwards [hν] with y hy
    filter_upwards [hμ] with x hx
    exact rotated_distance_ge_gap c d x y Q R hx hy
  filter_upwards [hae] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact (inv_le_inv₀ (hδ.trans_le hp) hδ).2 hp

/-- Every positive pair interaction has a bound independent of the rotations. -/
theorem norm_rotatedMutualInteraction_le (c d : Position) (μ ν : Measure Position)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {r s : ℝ} (hcent : r+s < ‖d-c‖)
    (hμ : ∀ᵐ x ∂μ, ‖x-c‖ ≤ r) (hν : ∀ᵐ y ∂ν, ‖y-d‖ ≤ s)
    (Q R : SpatialRotation) :
    ‖rotatedMutualInteraction c d μ ν Q R‖ ≤
      (‖d-c‖-r-s)⁻¹ * (ν.prod μ).real univ := by
  have hδ : 0 < ‖d-c‖ - r - s := by linarith only [hcent]
  rw [rotatedMutualInteraction,
    ← integral_prod _ (integrable_rotated_kernel c d μ ν hcent hμ hν Q R)]
  apply norm_integral_le_of_norm_le_const
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
    (((((measurable_rotateAbout R d).comp measurable_fst).sub
      ((measurable_rotateAbout Q c).comp measurable_snd)).norm.inv).norm)
    measurable_const)).2
  filter_upwards [hν] with y hy
  filter_upwards [hμ] with x hx
  have hp := rotated_distance_ge_gap c d x y Q R hx hy
  change ‖(‖rotateAbout R d y - rotateAbout Q c x‖⁻¹ : ℝ)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact (inv_le_inv₀ (hδ.trans_le hp) hδ).2 hp

/-- The positive pair interaction is integrable over independent Haar rotations. -/
theorem integrable_rotatedMutualInteraction (c d : Position) (μ ν : Measure Position)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {r s : ℝ} (hcent : r+s < ‖d-c‖)
    (hμ : ∀ᵐ x ∂μ, ‖x-c‖ ≤ r) (hν : ∀ᵐ y ∂ν, ‖y-d‖ ≤ s) :
    Integrable (fun p : SpatialRotation × SpatialRotation =>
      rotatedMutualInteraction c d μ ν p.1 p.2)
      (spatialRotationMeasure.prod spatialRotationMeasure) := by
  apply Integrable.mono'
    (integrable_const ((‖d-c‖-r-s)⁻¹ * (ν.prod μ).real univ))
    (measurable_rotatedMutualInteraction c d μ ν).aestronglyMeasurable
  exact Eventually.of_forall fun p => norm_rotatedMutualInteraction_le c d μ ν hcent hμ hν p.1 p.2

theorem integrable_rotatedMutualInteraction_left (c d : Position) (μ ν : Measure Position)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {r s : ℝ} (hcent : r+s < ‖d-c‖)
    (hμ : ∀ᵐ x ∂μ, ‖x-c‖ ≤ r) (hν : ∀ᵐ y ∂ν, ‖y-d‖ ≤ s)
    (R : SpatialRotation) :
    Integrable (fun Q : SpatialRotation => rotatedMutualInteraction c d μ ν Q R) spatialRotationMeasure := by
  have hm : Measurable (fun Q : SpatialRotation => rotatedMutualInteraction c d μ ν Q R) :=
    (measurable_rotatedMutualInteraction c d μ ν).of_uncurry_right
  apply Integrable.mono'
    (integrable_const ((‖d-c‖-r-s)⁻¹ * (ν.prod μ).real univ)) hm.aestronglyMeasurable
  exact Eventually.of_forall fun Q => norm_rotatedMutualInteraction_le c d μ ν hcent hμ hν Q R

end LiebThirring.ThermoNeutral

end
