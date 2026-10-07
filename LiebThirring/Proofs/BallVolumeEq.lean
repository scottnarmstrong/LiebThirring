/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.BallVolume
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Volume of a three-dimensional ball

The Euclidean volume of a ball is four thirds of π times the cube of its radius.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace LiebThirring.Proofs

theorem ballVolume_eq_volume (L : {L : ℝ // 0 < L}) :
    ENNReal.ofReal (ballVolume L) = volume (Metric.ball (0 : Position) L.val) ∧
      0 < ballVolume L := by
  constructor
  · rw [EuclideanSpace.volume_ball_fin_three]
    rw [ballVolume, ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.pi / 3),
      ENNReal.ofReal_pow L.property.le, mul_comm]
    congr 2
    ring
  · exact mul_pos (div_pos (mul_pos (by norm_num) Real.pi_pos) (by norm_num))
      (pow_pos L.property 3)
end LiebThirring.Proofs

end
