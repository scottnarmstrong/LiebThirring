/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # One-dimensional integration by parts for a Lipschitz factor -/

public section

open MeasureTheory Set Function
open scoped ContDiff NNReal Interval

namespace LiebThirring.Sobolev

/-- A Lipschitz function can be integrated by parts against a compactly supported smooth test. -/
theorem integral_mul_deriv_eq_neg_deriv_mul_of_lipschitz {b φ : ℝ → ℝ} {C : ℝ≥0}
    (hb : LipschitzWith C b) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ t, b t * deriv φ t) = -(∫ t, deriv b t * φ t) := by
  obtain ⟨r, hr⟩ := hφc.isCompact.isBounded.subset_ball (0 : ℝ)
  let A : ℝ := -(r + 1)
  let B : ℝ := r + 1
  have hsupportOpen : tsupport φ ⊆ Ioo A B := by
    intro x hx
    have hxball := hr hx
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hxball
    dsimp [A, B]
    constructor <;> linarith [abs_nonneg x, le_abs_self x, neg_le_abs x]
  have hsupport : tsupport φ ⊆ Ioc A B := hsupportOpen.trans Ioo_subset_Ioc_self
  have hA : φ A = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact (lt_irrefl A) (hsupportOpen h).1
  have hB : φ B = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact (lt_irrefl B) (hsupportOpen h).2
  have hbAC : AbsolutelyContinuousOnInterval b A B :=
    hb.lipschitzOnWith.absolutelyContinuousOnInterval
  have hφAC : AbsolutelyContinuousOnInterval φ A B :=
    (hφ.contDiffOn.of_le (by simp)).absolutelyContinuousOnInterval
  have hinterval := hbAC.integral_mul_deriv_eq_deriv_mul hφAC
  simp only [hA, hB, mul_zero, neg_zero, zero_sub] at hinterval
  have hsleft : support (fun t => b t * deriv φ t) ⊆ Ioc A B :=
    (support_mul_subset_right b (deriv φ)).trans (support_deriv_subset.trans hsupport)
  have hsright : support (fun t => deriv b t * φ t) ⊆ Ioc A B :=
    (support_mul_subset_right (deriv b) φ).trans (subset_tsupport _ |>.trans hsupport)
  rw [intervalIntegral.integral_eq_integral_of_support_subset hsleft,
    intervalIntegral.integral_eq_integral_of_support_subset hsright] at hinterval
  exact hinterval

end LiebThirring.Sobolev

end
