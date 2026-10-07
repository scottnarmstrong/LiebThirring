/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoNeutral.SignedInteraction
public import LiebThirring.ThermoNeutral.Separation
public import LiebThirring.ThermoNeutral.AverageIntegral

/-! # Zero average of a separated neutral signed interaction

Neutrality is required for the total charge, after summing all clusters.
Only the first cluster has to be neutral. The second may be an exceptional,
unrotated cluster whenever its charge supports satisfy the displayed separation.
-/

public section

open MeasureTheory Set

namespace LiebThirring.ThermoNeutral

section Pair

variable (c d : Position) (μp μm νp νm : Measure Position)
  [IsFiniteMeasure μp] [IsFiniteMeasure μm] [IsFiniteMeasure νp] [IsFiniteMeasure νm]
  {r s : ℝ} (hr : 0 ≤ r) (hcent : r+s < ‖d-c‖)
  (hμp : ∀ᵐ x ∂μp, ‖x-c‖ ≤ r) (hμm : ∀ᵐ x ∂μm, ‖x-c‖ ≤ r)
  (hνp : ∀ᵐ y ∂νp, ‖y-d‖ ≤ s) (hνm : ∀ᵐ y ∂νm, ‖y-d‖ ≤ s)
  (hneutral : μp univ = μm univ)

include hr hcent hμp hμm hνp hνm hneutral

/-- Integrating the first rotation screens the signed interaction for every second rotation. -/
theorem integral_rotatedSignedInteraction_left_eq_zero (R : SpatialRotation) :
    (∫ Q, rotatedSignedInteraction c d μp μm νp νm Q R ∂spatialRotationMeasure) = 0 := by
  have hνp' := ae_norm_le_map_rotateAbout R d νp hνp
  have hνm' := ae_norm_le_map_rotateAbout R d νm hνm
  have hpp := integrable_rotatedMutualInteraction_left c d μp νp hcent hμp hνp R
  have hmp := integrable_rotatedMutualInteraction_left c d μm νp hcent hμm hνp R
  have hpm := integrable_rotatedMutualInteraction_left c d μp νm hcent hμp hνm R
  have hmm := integrable_rotatedMutualInteraction_left c d μm νm hcent hμm hνm R
  unfold rotatedSignedInteraction
  rw [integral_add
    (f := fun Q => rotatedMutualInteraction c d μp νp Q R -
      rotatedMutualInteraction c d μm νp Q R - rotatedMutualInteraction c d μp νm Q R)
    ((hpp.sub hmp).sub hpm) hmm,
    integral_sub
      (f := fun Q => rotatedMutualInteraction c d μp νp Q R -
        rotatedMutualInteraction c d μm νp Q R) (hpp.sub hmp) hpm,
    integral_sub hpp hmp]
  simp_rw [rotatedMutualInteraction_eq_map, mutualInteraction]
  rw [integral_rotated_eq_rotationAveragedMeasure c d μp _ hμp hνp' hcent,
    integral_rotated_eq_rotationAveragedMeasure c d μm _ hμm hνp' hcent,
    integral_rotated_eq_rotationAveragedMeasure c d μp _ hμp hνm' hcent,
    integral_rotated_eq_rotationAveragedMeasure c d μm _ hμm hνm' hcent]
  exact neutral_radial_mutual_energy_zero_of_ball_separation c d
    (rotationAveragedMeasure c μp) (rotationAveragedMeasure c μm)
    (νp.map (rotateAbout R d)) (νm.map (rotateAbout R d))
    (isRadial_rotationAveragedMeasure c μp) (isRadial_rotationAveragedMeasure c μm)
    (by rw [rotationAveragedMeasure_mass, rotationAveragedMeasure_mass, hneutral]) hr hcent
    (ae_norm_le_rotationAveragedMeasure c μp hμp)
    (ae_norm_le_rotationAveragedMeasure c μm hμm) hνp' hνm'

/-- Independent Haar rotations have zero mean signed cross energy. -/
theorem integral_rotatedSignedInteraction_eq_zero :
    (∫ Q, ∫ R, rotatedSignedInteraction c d μp μm νp νm Q R
      ∂spatialRotationMeasure ∂spatialRotationMeasure) = 0 := by
  rw [integral_integral_swap
    (integrable_rotatedSignedInteraction c d μp μm νp νm hcent hμp hμm hνp hνm)]
  have heq : (fun R => ∫ Q, rotatedSignedInteraction c d μp μm νp νm Q R
      ∂spatialRotationMeasure) = fun _ => (0 : ℝ) := by
    funext R
    exact integral_rotatedSignedInteraction_left_eq_zero c d μp μm νp νm
      hr hcent hμp hμm hνp hνm hneutral R
  rw [heq, integral_zero]

end Pair

end LiebThirring.ThermoNeutral

end
