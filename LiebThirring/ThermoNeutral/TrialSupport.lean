/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.Trials
public import LiebThirring.ThermoClusters.SupportSeparation

/-!
# Inner support radii for smooth region trials

A compact smooth trial confined to an open ball is carried by a strictly
smaller concentric closed ball. This is the support input used by the neutral
cluster rotation argument of the neutral variational packing.
-/

public section

open MeasureTheory Set

namespace LiebThirring.ThermoNeutral

/-- The electron and nuclear one-body measures of a smooth trial in an open
ball are both carried by one strictly smaller concentric closed ball. -/
theorem exists_inner_radius_of_smoothRegionTrial_ball
    {N M q : ℕ} {c : Position} {R : ℝ}
    (f : SmoothRegionTrial N M q (Metric.ball c R)) (hR : 0 < R) :
    ∃ r, 0 < r ∧ r < R ∧
      (∀ᵐ x ∂quantumElectronMeasure f.formDomain.val, ‖x - c‖ ≤ r) ∧
      (∀ᵐ x ∂quantumNuclearMeasure f.formDomain.val, ‖x - c‖ ≤ r) := by
  let K := clusterSpatialSupport f.val
  have hK : IsCompact K := isCompact_clusterSpatialSupport f.val f.property.1
  have hsub : K ⊆ Metric.ball c R :=
    clusterSpatialSupport_subset f.val (Metric.ball c R) f.property.2.1
  have hae : ∀ᵐ x ∂quantumElectronMeasure f.formDomain.val, x ∈ K := by
    simpa only [SmoothRegionTrial.formDomain] using
      ae_quantumElectronMeasure_mem_clusterSpatialSupport f.val f.property.1
  have han : ∀ᵐ x ∂quantumNuclearMeasure f.formDomain.val, x ∈ K := by
    simpa only [SmoothRegionTrial.formDomain] using
      ae_quantumNuclearMeasure_mem_clusterSpatialSupport f.val f.property.1
  by_cases hne : K.Nonempty
  · obtain ⟨x, hxK, hxmax⟩ := hK.exists_isMaxOn hne
      ((continuous_id.sub continuous_const).norm.continuousOn)
    have hxR : ‖x - c‖ < R := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hsub hxK
    refine ⟨(‖x - c‖ + R) / 2, ?_, ?_, ?_, ?_⟩
    · positivity
    · linarith
    · filter_upwards [hae] with y hy
      have hyle : ‖y - c‖ ≤ ‖x - c‖ := hxmax hy
      linarith
    · filter_upwards [han] with y hy
      have hyle : ‖y - c‖ ≤ ‖x - c‖ := hxmax hy
      linarith
  · have hKempty : K = ∅ := not_nonempty_iff_eq_empty.mp hne
    refine ⟨R / 2, by linarith, by linarith, ?_, ?_⟩
    · filter_upwards [hae] with x hx
      rw [hKempty] at hx
      exact hx.elim
    · filter_upwards [han] with x hx
      rw [hKempty] at hx
      exact hx.elim

end LiebThirring.ThermoNeutral

end
