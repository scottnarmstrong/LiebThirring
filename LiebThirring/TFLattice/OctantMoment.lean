/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.RadialMoment

/-!
# Physical octant ball integrals

Both the volume and squared moment are finite, so their real integrals retain
the sharp constants. Source: Lieb–Simon (1977) III.13, pp. 67–69 (sharp eigenvalue sums).
-/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace LiebThirring.TFLattice

def octantBall (r : ℝ) : Set Position := {x | (∀ i, 0 ≤ x i) ∧ ‖x‖ ≤ r}

theorem octantBall_eq_preimage (r : ℝ) : octantBall r =
    (WithLp.ofLp : Position → Fin 3 → ℝ) ⁻¹' coordinateOctantBall r := by
  ext x
  simp [octantBall, coordinateOctantBall, coordinateBall, coordinateOctant, Pi.le_def,
    and_comm]

theorem measurableSet_octantBall (r : ℝ) : MeasurableSet (octantBall r) := by
  rw [octantBall_eq_preimage]
  exact (measurableSet_coordinateOctantBall r).preimage (WithLp.measurable_ofLp 2 _)

theorem volume_octantBall_ne_top (r : ℝ) : volume (octantBall r) ≠ ∞ := by
  apply ne_of_lt
  apply lt_of_le_of_lt (measure_mono (show octantBall r ⊆ closedBall 0 r from
    fun x hx => by simpa only [mem_closedBall, dist_zero_right] using hx.2))
  exact (isCompact_closedBall (0 : Position) r).measure_lt_top

theorem volume_real_octantBall {r : ℝ} (hr : 0 ≤ r) :
    volume.real (octantBall r) = Real.pi / 6 * r ^ 3 := volume_real_octant_norm_le hr

theorem integrableOn_octantBall_norm_sq (r : ℝ) :
    IntegrableOn (fun x : Position => ‖x‖ ^ 2) (octantBall r) :=
  ((continuous_norm.pow 2).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Position) r)).mono_set
      (fun x hx => by simpa only [mem_closedBall, dist_zero_right] using hx.2)

theorem integral_octantBall_norm_sq {r : ℝ} (hr : 0 ≤ r) :
    (∫ x in octantBall r, ‖x‖ ^ 2) = Real.pi / 10 * r ^ 5 := by
  have hmp := (PiLp.volume_preserving_ofLp (Fin 3)).restrict_preimage
    (measurableSet_coordinateOctantBall r)
  rw [← octantBall_eq_preimage] at hmp
  have he := hmp.lintegral_comp (f := fun x : Fin 3 → ℝ =>
    ENNReal.ofReal (‖(WithLp.toLp 2 x : Position)‖ ^ 2)) (by fun_prop)
  simp only [WithLp.toLp_ofLp] at he
  rw [lintegral_coordinateOctantBall_norm_sq hr] at he
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg ‖x‖)
    (integrableOn_octantBall_norm_sq r).aestronglyMeasurable, he,
    ENNReal.toReal_ofReal (by positivity)]

end LiebThirring.TFLattice

end
