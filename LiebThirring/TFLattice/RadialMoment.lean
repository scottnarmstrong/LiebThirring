/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.OctantBall
import LiebThirring.Electrostatics.SphereRadial

/-!
# Exact radial squared moment

The full three-dimensional ball moment is `4πr⁵/5`, hence the octant moment
is `πr⁵/10`. Source: Lieb–Simon (1977) III.13, pp. 67–69 (sharp eigenvalue sums).
This module establishes the full-ball identity for transport by octant folding.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LiebThirring.TFLattice

theorem lintegral_radial_norm_sq {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ x : Position, if ‖x‖ ≤ r then ENNReal.ofReal (‖x‖ ^ 2) else 0) =
      ENNReal.ofReal (4 * Real.pi / 5 * r ^ 5) := by
  have hm : Measurable (fun t : ℝ => if t ≤ r then ENNReal.ofReal (t ^ 2) else 0) :=
    Measurable.ite (measurableSet_le measurable_id measurable_const)
      (measurable_id.pow_const 2).ennreal_ofReal measurable_const
  rw [LiebThirring.lintegral_norm _ hm]
  have hcore : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ 2) *
      (if t ≤ r then ENNReal.ofReal (t ^ 2) else 0)) =
      ∫⁻ t in Ioc (0 : ℝ) r, ENNReal.ofReal (t ^ 4) := by
    calc
      _ = ∫⁻ t in Ioi (0 : ℝ), (Iic r).indicator (fun t => ENNReal.ofReal (t ^ 4)) t := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        by_cases htr : t ≤ r
        · simp only [htr, ite_true, indicator_of_mem (show t ∈ Iic r from htr)]
          rw [← ENNReal.ofReal_mul (sq_nonneg t)]
          congr 1
          ring
        · simp only [htr, ite_false, mul_zero, indicator_of_notMem (show t ∉ Iic r from htr)]
      _ = _ := by
        rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
        rw [show Iic r ∩ Ioi (0 : ℝ) = Ioc 0 r by
          ext t
          exact and_comm]
  have hi : IntegrableOn (fun t : ℝ => t ^ 4) (Ioc 0 r) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mp
      ((continuous_id.pow 4).intervalIntegrable 0 r)
  have hscalar : (∫⁻ t in Ioc (0 : ℝ) r, ENNReal.ofReal (t ^ 4)) =
      ENNReal.ofReal (r ^ 5 / 5) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun t => by positivity)),
      ← intervalIntegral.integral_of_le hr, integral_pow]
    norm_num
  rw [hcore, hscalar, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The sharp octant square moment, with no default `toReal` at infinity. -/
theorem lintegral_coordinateOctantBall_norm_sq {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ x in coordinateOctantBall r,
      ENNReal.ofReal (‖(WithLp.toLp 2 x : Position)‖ ^ 2)) =
      ENNReal.ofReal (Real.pi / 10 * r ^ 5) := by
  let f : (Fin 3 → ℝ) → ℝ≥0∞ := fun x =>
    if ‖(WithLp.toLp 2 x : Position)‖ ≤ r then
      ENNReal.ofReal (‖(WithLp.toLp 2 x : Position)‖ ^ 2) else 0
  have hm : Measurable f := by
    apply Measurable.ite
    · exact measurableSet_le ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable.norm)
        measurable_const
    · fun_prop
    · exact measurable_const
  have hf : f = (coordinateBall r).indicator
      (fun x => ENNReal.ofReal (‖(WithLp.toLp 2 x : Position)‖ ^ 2)) := by
    ext x
    by_cases hx : x ∈ coordinateBall r
    · have hn : ‖(WithLp.toLp 2 x : Position)‖ ≤ r := by
        simpa only [coordinateBall, mem_preimage, Metric.mem_closedBall, dist_zero_right] using hx
      rw [indicator_of_mem hx]
      exact ite_eq_left hn
    · have hn : ¬‖(WithLp.toLp 2 x : Position)‖ ≤ r := by
        simpa only [coordinateBall, mem_preimage, Metric.mem_closedBall, dist_zero_right] using hx
      rw [indicator_of_notMem hx]
      exact ite_eq_right hn
  have hfull : (∫⁻ x, f x) = ENNReal.ofReal (4 * Real.pi / 5 * r ^ 5) := by
    have he := (PiLp.volume_preserving_toLp (Fin 3)).lintegral_comp
      (f := fun x : Position => if ‖x‖ ≤ r then ENNReal.ofReal (‖x‖ ^ 2) else 0)
      (by
        apply Measurable.ite
        · exact measurableSet_le measurable_norm measurable_const
        · fun_prop
        · exact measurable_const)
    exact he.trans (lintegral_radial_norm_sq hr)
  have hfold : (∫⁻ x, f x) = (8 : ℝ≥0∞) *
      ∫⁻ x in coordinateOctantBall r, ENNReal.ofReal (‖(WithLp.toLp 2 x : Position)‖ ^ 2) := by
    calc
      _ = ∫⁻ x, f (absoluteCoordinates x) := by
        apply lintegral_congr
        intro x
        simp only [f, norm_absoluteCoordinates]
      _ = ∫⁻ x, f x ∂Measure.map absoluteCoordinates volume :=
        (lintegral_map hm measurable_absoluteCoordinates).symm
      _ = (8 : ℝ≥0∞) * ∫⁻ x in coordinateOctant, f x := by
        rw [map_absoluteCoordinates_volume, lintegral_smul_measure, smul_eq_mul]
      _ = _ := by
        rw [hf, lintegral_indicator (measurableSet_coordinateBall r),
          Measure.restrict_restrict (measurableSet_coordinateBall r)]
        rfl
  apply (ENNReal.mul_left_inj (by norm_num : (8 : ℝ≥0∞) ≠ 0)
    (by norm_num : (8 : ℝ≥0∞) ≠ ∞)).mp
  rw [mul_comm _ (8 : ℝ≥0∞), mul_comm _ (8 : ℝ≥0∞), ← hfold, hfull, show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
  congr 1
  ring

end LiebThirring.TFLattice

end
