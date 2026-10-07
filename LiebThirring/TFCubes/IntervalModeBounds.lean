/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.IntervalModesL2

/-!
# Endpoint and derivative bounds for interval sine modes

Argument cube spectral theory test-density inputs. The sine vanishes linearly at each endpoint,
with its physical frequency, and its actual derivative is bounded uniformly.
-/

public section

namespace LiebThirring.TFCubes

theorem abs_dirichletIntervalMode_le (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) (x : ℝ) :
    |dirichletIntervalMode ℓ n x| ≤ Real.sqrt (2 / ℓ.val) := by
  rw [dirichletIntervalMode, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (Real.sqrt_nonneg _)).trans_eq
    (mul_one _)

theorem abs_dirichletIntervalMode_le_left (ℓ : {ℓ : ℝ // 0 < ℓ})
    (n : ℕ+) {x : ℝ} (hx : 0 ≤ x) :
    |dirichletIntervalMode ℓ n x| ≤
      Real.sqrt (2 / ℓ.val) * intervalFrequency ℓ n * x := by
  rw [dirichletIntervalMode, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt (2 / ℓ.val) * |intervalFrequency ℓ n * x| :=
      mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (Real.sqrt_nonneg _)
    _ = _ := by
      rw [abs_of_nonneg (mul_nonneg (intervalFrequency_nonneg ℓ n) hx), mul_assoc]

theorem abs_dirichletIntervalMode_le_right (ℓ : {ℓ : ℝ // 0 < ℓ})
    (n : ℕ+) {x : ℝ} (hx : x ≤ ℓ.val) :
    |dirichletIntervalMode ℓ n x| ≤
      Real.sqrt (2 / ℓ.val) * intervalFrequency ℓ n * (ℓ.val - x) := by
  have hs : |Real.sin (intervalFrequency ℓ n * x)| ≤
      |intervalFrequency ℓ n * x - intervalFrequency ℓ n * ℓ.val| := by
    simpa only [intervalFrequency_mul_length, Real.sin_nat_mul_pi, sub_zero] using
      Real.abs_sin_sub_sin_le (intervalFrequency ℓ n * x) (intervalFrequency ℓ n * ℓ.val)
  rw [dirichletIntervalMode, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt (2 / ℓ.val) *
        |intervalFrequency ℓ n * x - intervalFrequency ℓ n * ℓ.val| :=
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    _ = _ := by
      rw [abs_of_nonpos (sub_nonpos.mpr
        (mul_le_mul_of_nonneg_left hx (intervalFrequency_nonneg ℓ n)))]
      ring

theorem abs_deriv_dirichletIntervalMode_le (ℓ : {ℓ : ℝ // 0 < ℓ})
    (n : ℕ+) (x : ℝ) :
    |deriv (dirichletIntervalMode ℓ n) x| ≤
      Real.sqrt (2 / ℓ.val) * intervalFrequency ℓ n := by
  rw [deriv_dirichletIntervalMode, abs_mul, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (intervalFrequency_nonneg ℓ n)]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.sqrt_nonneg _))
      (intervalFrequency_nonneg ℓ n)).trans_eq (by rw [mul_one])

end LiebThirring.TFCubes

end
