/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Screening.Rotations
public import LiebThirring.Screening.Integrability

/-!
# Separation of independently rotated neutral clusters

Geometric and measure-theoretic separation facts used in the neutral-cluster
rotation argument of the neutral variational packing.
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal

namespace LiebThirring.ThermoNeutral

/-- Inner radii leave a strict gap when the corresponding larger open balls
are disjoint. -/
theorem inner_radii_lt_center_distance_of_disjoint_balls
    {c d : Position} {R S r s : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hr : r < R) (hs : s < S)
    (hdisj : Disjoint (ball c R) (ball d S)) :
    r + s < ‖d - c‖ := by
  have hRS : R + S ≤ dist c d :=
    (disjoint_ball_ball_iff hR hS).mp hdisj
  rw [dist_eq_norm, norm_sub_rev] at hRS
  linarith

/-- The width left between two inner balls is positive. -/
theorem separationGap_pos {c d : Position} {r s : ℝ}
    (hcent : r + s < ‖d - c‖) :
    0 < ‖d - c‖ - r - s := by
  linarith

/-- A fixed rotation about `c` is continuous. -/
theorem continuous_rotateAbout_fixed (Q : SpatialRotation) (c : Position) :
    Continuous (rotateAbout Q c) := by
  unfold rotateAbout
  exact continuous_const.add
    ((spatialRotationIsometry Q).continuous.comp (continuous_id.sub continuous_const))

/-- A measure carried by a concentric closed ball keeps that support after a
fixed rotation. -/
theorem ae_norm_le_map_rotateAbout (Q : SpatialRotation) (c : Position)
    (μ : Measure Position) {r : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x - c‖ ≤ r) :
    ∀ᵐ x ∂μ.map (rotateAbout Q c), ‖x - c‖ ≤ r := by
  apply (ae_map_iff (continuous_rotateAbout_fixed Q c).measurable.aemeasurable
    (measurableSet_le (continuous_id.sub continuous_const).norm.measurable measurable_const)).2
  filter_upwards [hμ] with x hx
  change ‖rotateAbout Q c x - c‖ ≤ r
  simpa only [norm_rotateAbout_sub] using hx

/-- Support in the second inner ball gives the exterior support condition used
by the screening integrability API, viewed from the first centre. -/
theorem ae_outer_of_ae_inner {c d : Position} (ν : Measure Position)
    {r s : ℝ} (hν : ∀ᵐ y ∂ν, ‖y - d‖ ≤ s) :
    ∀ᵐ y ∂ν, r + (‖d - c‖ - r - s) ≤ ‖y - c‖ := by
  filter_upwards [hν] with y hy
  have htriangle : ‖d - c‖ ≤ ‖d - y‖ + ‖y - c‖ := by
    calc
      ‖d - c‖ = ‖(d - y) + (y - c)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  rw [norm_sub_rev d y] at htriangle
  linarith

/-- All four real inverse-distance kernels between two independently rotated
finite two-species clusters are integrable. -/
theorem four_integrable_inverse_norm_map_rotateAbout
    (Q P : SpatialRotation) {c d : Position} {r s : ℝ}
    (μp μn νp νn : Measure Position)
    [IsFiniteMeasure μp] [IsFiniteMeasure μn]
    [IsFiniteMeasure νp] [IsFiniteMeasure νn]
    (hcent : r + s < ‖d - c‖)
    (hμp : ∀ᵐ x ∂μp, ‖x - c‖ ≤ r) (hμn : ∀ᵐ x ∂μn, ‖x - c‖ ≤ r)
    (hνp : ∀ᵐ y ∂νp, ‖y - d‖ ≤ s) (hνn : ∀ᵐ y ∂νn, ‖y - d‖ ≤ s) :
    Integrable (fun z : Position × Position => ‖z.1 - z.2‖⁻¹)
        ((νp.map (rotateAbout P d)).prod (μp.map (rotateAbout Q c))) ∧
    Integrable (fun z : Position × Position => ‖z.1 - z.2‖⁻¹)
        ((νp.map (rotateAbout P d)).prod (μn.map (rotateAbout Q c))) ∧
    Integrable (fun z : Position × Position => ‖z.1 - z.2‖⁻¹)
        ((νn.map (rotateAbout P d)).prod (μp.map (rotateAbout Q c))) ∧
    Integrable (fun z : Position × Position => ‖z.1 - z.2‖⁻¹)
        ((νn.map (rotateAbout P d)).prod (μn.map (rotateAbout Q c))) := by
  let ε := ‖d - c‖ - r - s
  have hε : 0 < ε := separationGap_pos hcent
  have hμp' := ae_norm_le_map_rotateAbout Q c μp hμp
  have hμn' := ae_norm_le_map_rotateAbout Q c μn hμn
  have hνp' := ae_norm_le_map_rotateAbout P d νp hνp
  have hνn' := ae_norm_le_map_rotateAbout P d νn hνn
  have hop : ∀ᵐ y ∂νp.map (rotateAbout P d), r + ε ≤ ‖y - c‖ :=
    ae_outer_of_ae_inner (νp.map (rotateAbout P d)) hνp'
  have hon : ∀ᵐ y ∂νn.map (rotateAbout P d), r + ε ≤ ‖y - c‖ :=
    ae_outer_of_ae_inner (νn.map (rotateAbout P d)) hνn'
  exact ⟨integrable_inverse_norm_prod_of_ball_separation c _ _ hε hμp' hop,
    integrable_inverse_norm_prod_of_ball_separation c _ _ hε hμn' hop,
    integrable_inverse_norm_prod_of_ball_separation c _ _ hε hμp' hon,
    integrable_inverse_norm_prod_of_ball_separation c _ _ hε hμn' hon⟩

end LiebThirring.ThermoNeutral

end
