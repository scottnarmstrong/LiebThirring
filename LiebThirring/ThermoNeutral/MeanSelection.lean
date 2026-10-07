/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoNeutral.FamilyInteraction
public import LiebThirring.ThermoNeutral.SignedAverage
public import LiebThirring.ThermoNeutral.Selection

/-! # Zero Haar mean and rotation selection for finite neutral clusters

The positive/negative charge measures have equal total masses. No open-ball
mass equality is substituted for this condition. This uses neutrality of the total charge.
-/

public section

open MeasureTheory Set Filter Finset Metric
open scoped NNReal ENNReal

namespace LiebThirring.ThermoNeutral

section SignedFamily

variable {ι : Type*} [Fintype ι] [LinearOrder ι]
  (c : ι → Position) (μp μm : ι → Measure Position)
  [∀ i, IsFiniteMeasure (μp i)] [∀ i, IsFiniteMeasure (μm i)]
  {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i)
  (hcent : ∀ i j, i ≠ j → r i+r j < ‖c j-c i‖)
  (hμp : ∀ i, ∀ᵐ x ∂μp i, ‖x-c i‖ ≤ r i)
  (hμm : ∀ i, ∀ᵐ x ∂μm i, ‖x-c i‖ ≤ r i)
  (hneutral : ∀ i, μp i univ = μm i univ)

include hr hcent hμp hμm hneutral

/-- The actual total signed cross energy has mean zero under independent Haar rotations. -/
theorem integral_totalRotatedSignedInteraction_eq_zero :
    (∫ Q, totalRotatedSignedInteraction c μp μm Q ∂productRotationMeasure ι) = 0 := by
  have hpair (i j : ι) (hij : i ≠ j) :
      Integrable (fun p : SpatialRotation × SpatialRotation =>
        rotatedSignedInteraction (c i) (c j) (μp i) (μm i) (μp j) (μm j) p.1 p.2)
        (spatialRotationMeasure.prod spatialRotationMeasure) :=
    integrable_rotatedSignedInteraction (c i) (c j) (μp i) (μm i) (μp j) (μm j)
      (hcent i j hij) (hμp i) (hμm i) (hμp j) (hμm j)
  have hprod (i j : ι) (hij : i ≠ j) :
      Integrable (fun Q : ι → SpatialRotation =>
        rotatedSignedInteraction (c i) (c j) (μp i) (μm i) (μp j) (μm j) (Q i) (Q j))
        (productRotationMeasure ι) :=
    integrable_productRotationMeasure_comp_pair hij (hpair i j hij)
  unfold totalRotatedSignedInteraction
  rw [integral_finsetSum univ (fun i _ => integrable_finsetSum _
    (fun j hj => hprod i j (ne_of_lt (mem_filter.mp hj).2)))]
  apply sum_eq_zero
  intro i _
  rw [integral_finsetSum _ (fun j hj => hprod i j (ne_of_lt (mem_filter.mp hj).2))]
  apply sum_eq_zero
  intro j hj
  have hij : i ≠ j := ne_of_lt (mem_filter.mp hj).2
  rw [integral_productRotationMeasure_comp_pair hij (hpair i j hij)]
  exact integral_rotatedSignedInteraction_eq_zero (c i) (c j) (μp i) (μm i) (μp j) (μm j)
    (hr i) (hcent i j hij) (hμp i) (hμm i) (hμp j) (hμm j) (hneutral i)

end SignedFamily

section ChargedFamily

variable {ι : Type*} [Fintype ι] [LinearOrder ι]
  (z : ℕ) (c : ι → Position) (r R : ι → ℝ)
  (μe μn : ι → Measure Position)
  [∀ i, IsFiniteMeasure (μe i)] [∀ i, IsFiniteMeasure (μn i)]
  (hr : ∀ i, 0 < r i) (hsmall : ∀ i, r i < R i)
  (hdisj : Pairwise (fun i j => Disjoint (ball (c i) (R i)) (ball (c j) (R j))))
  (hμe : ∀ i, ∀ᵐ x ∂μe i, ‖x-c i‖ ≤ r i)
  (hμn : ∀ i, ∀ᵐ x ∂μn i, ‖x-c i‖ ≤ r i)
  (hneutral : ∀ i, (z : ℝ≥0∞) * μn i univ = μe i univ)

include hr hsmall hdisj hμe hμn hneutral

/-- The physical four-species sum has zero product-Haar average. -/
theorem integral_totalRotatedChargeInteraction_eq_zero :
    (∫ Q, totalRotatedChargeInteraction z c μe μn Q ∂productRotationMeasure ι) = 0 := by
  have hcent : ∀ i j, i ≠ j → r i+r j < ‖c j-c i‖ := by
    intro i j hij
    exact inner_radii_lt_center_distance_of_disjoint_balls
      ((hr i).trans (hsmall i)) ((hr j).trans (hsmall j)) (hsmall i) (hsmall j) (hdisj hij)
  apply integral_totalRotatedSignedInteraction_eq_zero c (fun i => (z : ℝ≥0) • μn i) μe
    (fun i => (hr i).le) hcent
    (fun i => Measure.ae_smul_measure (hμn i) (z : ℝ≥0)) hμe
  intro i
  simpa only [Measure.coe_nnreal_smul_apply, ENNReal.coe_natCast] using
    hneutral i

/-- Independent rotations select a nonpositive physical cross energy, even when outer balls touch. -/
theorem exists_nonpos_totalRotatedChargeInteraction :
    ∃ Q, totalRotatedChargeInteraction z c μe μn Q ≤ 0 := by
  have hcent : ∀ i j, i ≠ j → r i+r j < ‖c j-c i‖ := by
    intro i j hij
    exact inner_radii_lt_center_distance_of_disjoint_balls
      ((hr i).trans (hsmall i)) ((hr j).trans (hsmall j)) (hsmall i) (hsmall j) (hdisj hij)
  apply exists_nonpos_of_integral_eq_zero (productRotationMeasure ι)
    (integrable_totalRotatedSignedInteraction c (fun i => (z : ℝ≥0) • μn i) μe hcent
      (fun i => Measure.ae_smul_measure (hμn i) (z : ℝ≥0)) hμe)
    (integral_totalRotatedChargeInteraction_eq_zero z c r R μe μn hr hsmall hdisj hμe hμn hneutral)

end ChargedFamily

end LiebThirring.ThermoNeutral

end
