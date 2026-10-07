/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.IntervalTransitionBounds
public import LiebThirring.TFCubes.IntervalModeBounds
public import LiebThirring.TFCubes.IntervalCutoffDerivative
import Mathlib.Tactic

/-! # Scalar estimates for differentiated interval cutoffs -/

public section

open Set

namespace LiebThirring.TFCubes

theorem intervalInteriorCutoff_nonneg (ℓ : {ℓ : ℝ // 0 < ℓ}) (k : ℕ) (x : ℝ) :
    0 ≤ intervalInteriorCutoff ℓ k x := by
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem intervalInteriorCutoff_le_one (ℓ : {ℓ : ℝ // 0 < ℓ}) (k : ℕ) (x : ℝ) :
    intervalInteriorCutoff ℓ k x ≤ 1 := by
  unfold intervalInteriorCutoff
  calc
    _ ≤ 1 * Real.smoothTransition
        ((ℓ.val - intervalCutoffWidth ℓ k - x) / intervalCutoffWidth ℓ k) :=
      mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
        (Real.smoothTransition.nonneg _)
    _ ≤ 1 := by rw [one_mul]; exact Real.smoothTransition.le_one _

/-- A transition derivative multiplied by a function vanishing linearly at the corresponding
endpoint is uniformly bounded, independently of the transition width. -/
theorem abs_transition_mul_le {ε M C d y m : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (hC : 0 ≤ C) (hderiv : ∀ z, |deriv Real.smoothTransition z| ≤ M)
    (hm : |m| ≤ C * d) :
    |deriv Real.smoothTransition ((d - ε) / ε) / ε *
        Real.smoothTransition y * m| ≤ 2 * M * C := by
  by_cases hzero : deriv Real.smoothTransition ((d - ε) / ε) = 0
  · simp only [hzero, zero_div, zero_mul, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM) hC
  have hsupp : (d - ε) / ε ∈ Icc (0 : ℝ) 1 :=
    tsupport_deriv_smoothTransition_subset (subset_tsupport _ hzero)
  have hdupper : d ≤ 2 * ε := by
    have h := (div_le_iff₀ hε).mp hsupp.2
    linarith
  have hdle : |deriv Real.smoothTransition ((d - ε) / ε)| / ε ≤ M / ε :=
    div_le_div_of_nonneg_right (hderiv _) hε.le
  have hst : |Real.smoothTransition y| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hm2 : |m| ≤ C * (2 * ε) := hm.trans (mul_le_mul_of_nonneg_left hdupper hC)
  rw [abs_mul, abs_mul, abs_div, abs_of_pos hε]
  calc
    |deriv Real.smoothTransition ((d - ε) / ε)| / ε *
          |Real.smoothTransition y| * |m| ≤
        (M / ε) * 1 * (C * (2 * ε)) := by
      exact mul_le_mul (mul_le_mul hdle hst (abs_nonneg _) (div_nonneg hM hε.le))
        hm2 (abs_nonneg _) (mul_nonneg (div_nonneg hM hε.le) zero_le_one)
    _ = 2 * M * C := by field_simp

/-- The actual derivative of every compact sine test has one pointwise bound independent of the
cutoff index. -/
theorem norm_fderiv_compactDirichletMode_le
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ z, |deriv Real.smoothTransition z| ≤ M) (k : ℕ)
    {x : ℝ} (hx : x ∈ Ioo 0 ℓ.val) :
    ‖fderiv ℝ (compactDirichletMode ℓ n k) x 1‖ ≤
      Real.sqrt (2 / ℓ.val) * intervalFrequency ℓ n +
        4 * M * (Real.sqrt (2 / ℓ.val) * intervalFrequency ℓ n) := by
  let ε := intervalCutoffWidth ℓ k
  let C := Real.sqrt (2 / ℓ.val) * intervalFrequency ℓ n
  have hε : 0 < ε := intervalCutoffWidth_pos ℓ k
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) (intervalFrequency_nonneg ℓ n)
  have hleft :
      |deriv Real.smoothTransition ((x - ε) / ε) / ε *
        Real.smoothTransition ((ℓ.val - ε - x) / ε) * dirichletIntervalMode ℓ n x| ≤
          2 * M * C :=
    abs_transition_mul_le hε hM hC hderiv
      (abs_dirichletIntervalMode_le_left ℓ n hx.1.le)
  have hright :
      |deriv Real.smoothTransition (((ℓ.val - x) - ε) / ε) / ε *
        Real.smoothTransition ((x - ε) / ε) * dirichletIntervalMode ℓ n x| ≤
          2 * M * C :=
    abs_transition_mul_le hε hM hC hderiv
      (abs_dirichletIntervalMode_le_right ℓ n hx.2.le)
  have hbase : |intervalInteriorCutoff ℓ k x * deriv (dirichletIntervalMode ℓ n) x| ≤ C := by
    rw [abs_mul, abs_of_nonneg (intervalInteriorCutoff_nonneg ℓ k x)]
    calc
      intervalInteriorCutoff ℓ k x * |deriv (dirichletIntervalMode ℓ n) x| ≤
          1 * C := mul_le_mul (intervalInteriorCutoff_le_one ℓ k x)
            (abs_deriv_dirichletIntervalMode_le ℓ n x) (abs_nonneg _) (by positivity)
      _ = C := one_mul C
  have hright' :
      |Real.smoothTransition ((x - ε) / ε) *
        (deriv Real.smoothTransition ((ℓ.val - ε - x) / ε) / ε) *
        dirichletIntervalMode ℓ n x| ≤ 2 * M * C := by
    rw [show ℓ.val - ε - x = (ℓ.val - x) - ε by ring]
    have heq :
        Real.smoothTransition ((x - ε) / ε) *
            (deriv Real.smoothTransition (((ℓ.val - x) - ε) / ε) / ε) *
            dirichletIntervalMode ℓ n x =
          deriv Real.smoothTransition (((ℓ.val - x) - ε) / ε) / ε *
            Real.smoothTransition ((x - ε) / ε) * dirichletIntervalMode ℓ n x := by
      ring
    rw [heq]
    exact hright
  rw [fderiv_compactDirichletMode_apply_one, Complex.norm_real, Real.norm_eq_abs,
    deriv_intervalInteriorCutoff, sub_mul]
  calc
    _ ≤ |deriv Real.smoothTransition ((x - ε) / ε) / ε *
          Real.smoothTransition ((ℓ.val - ε - x) / ε) * dirichletIntervalMode ℓ n x -
        Real.smoothTransition ((x - ε) / ε) *
          (deriv Real.smoothTransition ((ℓ.val - ε - x) / ε) / ε) *
          dirichletIntervalMode ℓ n x| +
        |intervalInteriorCutoff ℓ k x * deriv (dirichletIntervalMode ℓ n) x| := abs_add_le _ _
    _ ≤ (2 * M * C + 2 * M * C) + C :=
      add_le_add ((abs_sub _ _).trans (add_le_add hleft hright')) hbase
    _ = _ := by dsimp only [C]; ring

end LiebThirring.TFCubes

end
