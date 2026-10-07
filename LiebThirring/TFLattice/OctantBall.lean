/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.OctantMeasure
public import LiebThirring.Packing.BallShells

/-!
# Exact octant ball volume

The radius is Euclidean, even though the coordinates are presented as a plain
finite function. The sharp volume is `π r³ / 6`. Source: Lieb–Simon (1977) III.13,
pp. 67–69 (sharp eigenvalue sums), unit-cell comparison.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LiebThirring.TFLattice

noncomputable def coordinateBall (r : ℝ) : Set (Fin 3 → ℝ) :=
  (WithLp.toLp 2) ⁻¹' closedBall (0 : Position) r

noncomputable def coordinateOctantBall (r : ℝ) : Set (Fin 3 → ℝ) :=
  coordinateBall r ∩ coordinateOctant

theorem measurableSet_coordinateBall (r : ℝ) : MeasurableSet (coordinateBall r) :=
  measurableSet_closedBall.preimage (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable

theorem measurableSet_coordinateOctant : MeasurableSet coordinateOctant :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ici

theorem measurableSet_coordinateOctantBall (r : ℝ) :
    MeasurableSet (coordinateOctantBall r) :=
  (measurableSet_coordinateBall r).inter measurableSet_coordinateOctant

theorem norm_absoluteCoordinates (x : Fin 3 → ℝ) :
    ‖(WithLp.toLp 2 (absoluteCoordinates x) : Position)‖ = ‖(WithLp.toLp 2 x : Position)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [absoluteCoordinates]

theorem preimage_absoluteCoordinates_ball (r : ℝ) :
    absoluteCoordinates ⁻¹' coordinateBall r = coordinateBall r := by
  ext x
  simp only [coordinateBall, mem_preimage, mem_closedBall, dist_zero_right,
    norm_absoluteCoordinates]

theorem volume_coordinateBall (r : ℝ) :
    volume (coordinateBall r) = volume (closedBall (0 : Position) r) := by
  exact (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    measurableSet_closedBall.nullMeasurableSet

theorem volume_coordinateBall_eq_eight_mul_octant (r : ℝ) :
    volume (coordinateBall r) = (8 : ℝ≥0∞) * volume (coordinateOctantBall r) := by
  have he := congrArg (fun μ : Measure (Fin 3 → ℝ) => μ (coordinateBall r))
    map_absoluteCoordinates_volume
  rw [Measure.map_apply measurable_absoluteCoordinates
    (measurableSet_coordinateBall r), preimage_absoluteCoordinates_ball,
    Measure.smul_apply, Measure.restrict_apply (measurableSet_coordinateBall r)] at he
  exact he

/-- The sharp octant volume, including radius zero. -/
theorem volume_real_coordinateOctantBall {r : ℝ} (hr : 0 ≤ r) :
    volume.real (coordinateOctantBall r) = Real.pi / 6 * r ^ 3 := by
  have he := congrArg ENNReal.toReal (volume_coordinateBall_eq_eight_mul_octant r)
  rw [volume_coordinateBall, ENNReal.toReal_mul] at he
  norm_num only [ENNReal.toReal_ofNat] at he
  have hfull := volume_real_closedBall_position (0 : Position) hr
  change (volume (closedBall (0 : Position) r)).toReal = _ at hfull
  rw [hfull] at he
  unfold ballVolumeConstant at he
  change (volume (coordinateOctantBall r)).toReal = _
  linarith

/-- The same sharp volume on the physical Euclidean carrier. -/
theorem volume_real_octant_norm_le {r : ℝ} (hr : 0 ≤ r) :
    volume.real {x : Position | (∀ i, 0 ≤ x i) ∧ ‖x‖ ≤ r} = Real.pi / 6 * r ^ 3 := by
  have hset : (WithLp.ofLp : Position → Fin 3 → ℝ) ⁻¹' coordinateOctantBall r =
      {x : Position | (∀ i, 0 ≤ x i) ∧ ‖x‖ ≤ r} := by
    ext x
    simp [coordinateOctantBall, coordinateBall, coordinateOctant, and_comm, Pi.le_def]
  have he := (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (measurableSet_coordinateOctantBall r).nullMeasurableSet
  rw [hset] at he
  rw [Measure.real, he]
  exact volume_real_coordinateOctantBall hr

end LiebThirring.TFLattice

end
