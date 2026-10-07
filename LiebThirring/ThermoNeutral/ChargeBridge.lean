/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoNeutral.Separation
public import LiebThirring.ThermoNeutral.FamilyInteraction
public import LiebThirring.ThermoClusters.ChargeEnergy
public import LiebThirring.ThermoClusters.SupportSeparation

/-!
# Bridge from rotated signed interactions to cluster charge interactions

This identifies the rotation-side four-species expression of thermodynamic
the neutral variational packing with the cluster-energy expression used by cluster assembly.
-/

public section

open MeasureTheory

namespace LiebThirring.ThermoNeutral

private theorem mutualInteraction_smul (a b : NNReal) (μ ν : Measure Position) :
    mutualInteraction (a • μ) (b • ν) =
      (b : ℝ) * (a : ℝ) * mutualInteraction μ ν := by
  unfold mutualInteraction
  simp only [ENNReal.smul_def]
  rw [integral_smul_measure]
  simp_rw [integral_smul_measure]
  simp only [smul_eq_mul, ENNReal.coe_toReal]
  rw [integral_const_mul]
  ring

private theorem mutualInteraction_smul_left (a : NNReal) (μ ν : Measure Position) :
    mutualInteraction (a • μ) ν = (a : ℝ) * mutualInteraction μ ν := by
  unfold mutualInteraction
  simp only [ENNReal.smul_def]
  simp_rw [integral_smul_measure]
  rw [integral_smul]
  simp only [smul_eq_mul, ENNReal.coe_toReal]

private theorem mutualInteraction_smul_right (b : NNReal) (μ ν : Measure Position) :
    mutualInteraction μ (b • ν) = (b : ℝ) * mutualInteraction μ ν := by
  unfold mutualInteraction
  simp only [ENNReal.smul_def]
  rw [integral_smul_measure]
  simp only [smul_eq_mul, ENNReal.coe_toReal]

private theorem mutualInteraction_eq_clusterIntegral
    (μ ν : Measure Position) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hi : Integrable (fun p : Position × Position => ‖p.1 - p.2‖⁻¹) (ν.prod μ)) :
    mutualInteraction μ ν = ∫ x, ∫ y, ‖x - y‖⁻¹ ∂ν ∂μ := by
  unfold mutualInteraction
  simpa only [norm_sub_rev] using
    (integral_integral_swap (f := fun y x : Position => ‖y - x‖⁻¹) hi)

/-- The rotated four-species charge interaction is exactly the cluster charge
interaction of the four pushed-forward measures. -/
theorem rotatedChargeInteraction_eq_clusterChargeInteraction
    (z : ℕ) (c d : Position) (μe μn νe νn : Measure Position)
    [IsFiniteMeasure μe] [IsFiniteMeasure μn]
    [IsFiniteMeasure νe] [IsFiniteMeasure νn]
    (Q R : SpatialRotation) {r s : ℝ} (hcent : r + s < ‖d - c‖)
    (hμe : ∀ᵐ x ∂μe, ‖x - c‖ ≤ r) (hμn : ∀ᵐ x ∂μn, ‖x - c‖ ≤ r)
    (hνe : ∀ᵐ y ∂νe, ‖y - d‖ ≤ s) (hνn : ∀ᵐ y ∂νn, ‖y - d‖ ≤ s) :
    rotatedChargeInteraction z c d μe μn νe νn Q R =
      clusterChargeInteraction z
        (μe.map (rotateAbout Q c)) (μn.map (rotateAbout Q c))
        (νe.map (rotateAbout R d)) (νn.map (rotateAbout R d)) := by
  let μe' := μe.map (rotateAbout Q c)
  let μn' := μn.map (rotateAbout Q c)
  let νe' := νe.map (rotateAbout R d)
  let νn' := νn.map (rotateAbout R d)
  obtain ⟨heeI, hneI, henI, hnnI⟩ :=
    four_integrable_inverse_norm_map_rotateAbout Q R μe μn νe νn hcent hμe hμn hνe hνn
  have hμe' := ae_norm_le_map_rotateAbout Q c μe hμe
  have hμn' := ae_norm_le_map_rotateAbout Q c μn hμn
  have hνe' := ae_norm_le_map_rotateAbout R d νe hνe
  have hνn' := ae_norm_le_map_rotateAbout R d νn hνn
  have hdisj : Disjoint (Metric.closedBall c r) (Metric.closedBall d s) := by
    apply Metric.closedBall_disjoint_closedBall
    simpa only [dist_eq_norm, norm_sub_rev] using hcent
  have hee' : clusterCoulombInteraction μe' νe' < ⊤ := by
    exact clusterCoulombInteraction_lt_top_of_compact_disjoint μe' νe'
      (isCompact_closedBall c r) (isCompact_closedBall d s) hdisj hμe' hνe'
  have hnn' : clusterCoulombInteraction μn' νn' < ⊤ := by
    exact clusterCoulombInteraction_lt_top_of_compact_disjoint μn' νn'
      (isCompact_closedBall c r) (isCompact_closedBall d s) hdisj hμn' hνn'
  have hen' : clusterCoulombInteraction μe' νn' < ⊤ := by
    exact clusterCoulombInteraction_lt_top_of_compact_disjoint μe' νn'
      (isCompact_closedBall c r) (isCompact_closedBall d s) hdisj hμe' hνn'
  have hne' : clusterCoulombInteraction μn' νe' < ⊤ := by
    exact clusterCoulombInteraction_lt_top_of_compact_disjoint μn' νe'
      (isCompact_closedBall c r) (isCompact_closedBall d s) hdisj hμn' hνe'
  rw [clusterChargeInteraction_eq_four_integrals z μe' μn' νe' νn'
    hee' hnn' hen' hne']
  unfold rotatedChargeInteraction rotatedSignedInteraction
  rw [rotatedMutualInteraction_eq_map, rotatedMutualInteraction_eq_map,
    rotatedMutualInteraction_eq_map, rotatedMutualInteraction_eq_map]
  rw [Measure.map_smul _ (measurable_rotateAbout Q c).aemeasurable,
    Measure.map_smul _ (measurable_rotateAbout R d).aemeasurable]
  rw [mutualInteraction_smul, mutualInteraction_smul_right,
    mutualInteraction_smul_left,
    mutualInteraction_eq_clusterIntegral μe' νe' heeI,
    mutualInteraction_eq_clusterIntegral μe' νn' henI,
    mutualInteraction_eq_clusterIntegral μn' νe' hneI,
    mutualInteraction_eq_clusterIntegral μn' νn' hnnI]
  push_cast
  ring

/-- The total rotated charge interaction is the sum of the corresponding
cluster charge interactions of the pushed-forward measures. -/
theorem totalRotatedChargeInteraction_eq_sum_clusterChargeInteraction
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (z : ℕ) (c : ι → Position) (μe μn : ι → Measure Position)
    [∀ i, IsFiniteMeasure (μe i)] [∀ i, IsFiniteMeasure (μn i)]
    (Q : ι → SpatialRotation) {r : ι → ℝ}
    (hcent : ∀ i j, i ≠ j → r i + r j < ‖c j - c i‖)
    (hμe : ∀ i, ∀ᵐ x ∂μe i, ‖x - c i‖ ≤ r i)
    (hμn : ∀ i, ∀ᵐ x ∂μn i, ‖x - c i‖ ≤ r i) :
    totalRotatedChargeInteraction z c μe μn Q =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        clusterChargeInteraction z
          ((μe i).map (rotateAbout (Q i) (c i)))
          ((μn i).map (rotateAbout (Q i) (c i)))
          ((μe j).map (rotateAbout (Q j) (c j)))
          ((μn j).map (rotateAbout (Q j) (c j))) := by
  unfold totalRotatedChargeInteraction totalRotatedSignedInteraction
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j hj
  change rotatedChargeInteraction z (c i) (c j) (μe i) (μn i) (μe j) (μn j)
      (Q i) (Q j) = _
  apply rotatedChargeInteraction_eq_clusterChargeInteraction
    z (c i) (c j) (μe i) (μn i) (μe j) (μn j) (Q i) (Q j)
  · exact hcent i j (ne_of_lt (Finset.mem_filter.mp hj).2)
  · exact hμe i
  · exact hμn i
  · exact hμe j
  · exact hμn j

end LiebThirring.ThermoNeutral

end
