/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoHeadline.PhysicalEnergy
public import LiebThirring.ThermoClusters.RegionMotion
public import LiebThirring.ThermoForm.EnergyApproximation

/-!
# Smooth near-minimizers in positive-radius balls

The literal finite physical neutral energy is approximated by the actual
normalized joint smooth trial carrier. Source: thermodynamic argument
confined form estimates and neutral variational packing, the finite-family near-minimizer step.
-/

public section

open MeasureTheory Metric Set
open scoped NNReal

namespace LiebThirring.ThermoNeutral

open ThermoHeadline

/-- A smooth trial in any positive-radius ball lies arbitrarily close to its real neutral infimum. -/
theorem exists_smoothRegionTrial_energy_lt_physical_add
    (q : ℕ) (hq : 1 ≤ q) (z : ℕ) (hz : 1 ≤ z)
    (mass : {m : ℝ≥0 // 0 < m}) (c : Position) {R : ℝ} (hR : 0 < R)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : SmoothRegionTrial (z*n) n q (ball c R),
      quantumEnergy z mass f.formDomain < physicalNeutralEnergy q z mass (ball c R) n + ε := by
  let L : {L : ℝ // 0 < L} := ⟨R, hR⟩
  have hcenter := dirichletRegionGroundStateEnergy_ball_center (z*n) n q z c mass L
  have hphysical := coe_physicalNeutralEnergy q hq z hz mass (ball c R) n
    isOpen_ball (nonempty_ball.mpr hR)
  have hlt : smoothConfinedGroundStateEnergy (z*n) n q z mass L <
      (physicalNeutralEnergy q z mass (ball c R) n + ε : EReal) := by
    rw [← confinedGroundStateEnergy_eq_smoothConfinedGroundStateEnergy,
      ← hcenter, ← hphysical]
    exact EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right _ hε)
  unfold smoothConfinedGroundStateEnergy at hlt
  obtain ⟨f, hf⟩ := iInf_lt_iff.mp hlt
  let g : SmoothRegionTrial (z*n) n q (ball (0 : Position) R) := f
  have hg : quantumEnergy z mass g.formDomain <
      physicalNeutralEnergy q z mass (ball c R) n + ε :=
    EReal.coe_lt_coe_iff.mp hf
  let Q := LinearIsometryEquiv.refl ℝ Position
  have hsub : spatialRigidMotion Q c '' ball (0 : Position) R ⊆ ball c R :=
    (image_spatialRigidMotion_ball_zero Q c R).le
  refine ⟨(g.motion Q c).enlarge hsub, ?_⟩
  change quantumEnergy z mass (g.motion Q c).formDomain < _
  rw [SmoothRegionTrial.energy_motion]
  exact hg

end LiebThirring.ThermoNeutral

end
