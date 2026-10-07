/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoNeutral.SignedInteraction
public import LiebThirring.ThermoNeutral.FiniteProduct

/-!
# Total rotated interaction of a finite family

The sum is over each unordered pair exactly once, using a linear order on
the finite label type. Proof: neutral variational packing.
-/

@[expose] public section

open MeasureTheory Set Filter Finset
open scoped NNReal

namespace LiebThirring.ThermoNeutral

/-- Total cross interaction of independently rotated positive/negative charge pairs. -/
noncomputable def totalRotatedSignedInteraction {ι : Type*} [Fintype ι] [LinearOrder ι]
    (c : ι → Position) (μp μm : ι → Measure Position) (Q : ι → SpatialRotation) : ℝ :=
  ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
    rotatedSignedInteraction (c i) (c j) (μp i) (μm i) (μp j) (μm j) (Q i) (Q j)

/-- Total cross energy for electron/nucleus measures and nuclear charge `z`. -/
noncomputable def totalRotatedChargeInteraction {ι : Type*} [Fintype ι] [LinearOrder ι]
    (z : ℕ) (c : ι → Position) (μe μn : ι → Measure Position)
    (Q : ι → SpatialRotation) : ℝ :=
  totalRotatedSignedInteraction c (fun i => (z : ℝ≥0) • μn i) μe Q

section Family

variable {ι : Type*} [Fintype ι] [LinearOrder ι]
  (c : ι → Position) (μp μm : ι → Measure Position)
  [∀ i, IsFiniteMeasure (μp i)] [∀ i, IsFiniteMeasure (μm i)]

variable {r : ι → ℝ} (hcent : ∀ i j, i ≠ j → r i+r j < ‖c j-c i‖)
  (hμp : ∀ i, ∀ᵐ x ∂μp i, ‖x-c i‖ ≤ r i)
  (hμm : ∀ i, ∀ᵐ x ∂μm i, ‖x-c i‖ ≤ r i)

include hcent hμp hμm

theorem integrable_totalRotatedSignedInteraction :
    Integrable (totalRotatedSignedInteraction c μp μm) (productRotationMeasure ι) := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j hj
  have hij : i ≠ j := ne_of_lt (mem_filter.mp hj).2
  exact integrable_productRotationMeasure_comp_pair hij
    (integrable_rotatedSignedInteraction (c i) (c j) (μp i) (μm i) (μp j) (μm j)
      (hcent i j hij) (hμp i) (hμm i) (hμp j) (hμm j))

end Family

end LiebThirring.ThermoNeutral

end
