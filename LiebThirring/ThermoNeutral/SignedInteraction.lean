/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoNeutral.PositiveInteraction

/-!
# Four-species signed interactions under rotation

The signed measure is represented by its actual positive and negative charges.
For nuclei of charge `z`, these are `z • μn` and `μe`, respectively.
with neutrality imposed on the total charge.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal

namespace LiebThirring.ThermoNeutral

/-- Four species in the interaction of the charges `μp-μm` and `νp-νm`. -/
noncomputable def rotatedSignedInteraction (c d : Position)
    (μp μm νp νm : Measure Position) (Q R : SpatialRotation) : ℝ :=
  rotatedMutualInteraction c d μp νp Q R -
    rotatedMutualInteraction c d μm νp Q R -
    rotatedMutualInteraction c d μp νm Q R +
    rotatedMutualInteraction c d μm νm Q R

/-- Electron/nucleus interaction, using the physical positive charge measure. -/
noncomputable def rotatedChargeInteraction (z : ℕ) (c d : Position)
    (μe μn νe νn : Measure Position) (Q R : SpatialRotation) : ℝ :=
  rotatedSignedInteraction c d ((z : ℝ≥0) • μn) μe ((z : ℝ≥0) • νn) νe Q R

section Support

variable (c d : Position) (μp μm νp νm : Measure Position)
  [IsFiniteMeasure μp] [IsFiniteMeasure μm] [IsFiniteMeasure νp] [IsFiniteMeasure νm]
  {r s : ℝ} (hcent : r+s < ‖d-c‖)
  (hμp : ∀ᵐ x ∂μp, ‖x-c‖ ≤ r) (hμm : ∀ᵐ x ∂μm, ‖x-c‖ ≤ r)
  (hνp : ∀ᵐ y ∂νp, ‖y-d‖ ≤ s) (hνm : ∀ᵐ y ∂νm, ‖y-d‖ ≤ s)

include hcent hμp hμm hνp hνm

theorem integrable_rotatedSignedInteraction :
    Integrable (fun p : SpatialRotation × SpatialRotation =>
      rotatedSignedInteraction c d μp μm νp νm p.1 p.2)
      (spatialRotationMeasure.prod spatialRotationMeasure) :=
  (((integrable_rotatedMutualInteraction c d μp νp hcent hμp hνp).sub
    (integrable_rotatedMutualInteraction c d μm νp hcent hμm hνp)).sub
    (integrable_rotatedMutualInteraction c d μp νm hcent hμp hνm)).add
    (integrable_rotatedMutualInteraction c d μm νm hcent hμm hνm)

end Support

end LiebThirring.ThermoNeutral

end
