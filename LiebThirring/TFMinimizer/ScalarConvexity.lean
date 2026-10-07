/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Quantitative convexity of the TF kinetic power

The elementary curvature estimate in the quantitative convexity (direct proof).
The endpoint zero is included by continuity; derivatives are used only in
the interior of the interval.
-/

public section

open Set

namespace LiebThirring.TFMinimizer

/-- Subtracting the lower curvature bound leaves a convex function. -/
theorem convexOn_rpow_five_thirds_sub_sq (s : ℝ) :
    ConvexOn ℝ (Icc 0 s)
      (fun t : ℝ => t ^ ((5 : ℝ) / 3) -
        (5 / 9 : ℝ) * s ^ (-(1 : ℝ) / 3) * t ^ 2) := by
  let c := (5 / 9 : ℝ) * s ^ (-(1 : ℝ) / 3)
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (f' := fun t => (5 / 3 : ℝ) * t ^ ((2 : ℝ) / 3) - c * (2 * t))
    (f'' := fun t => (10 / 9 : ℝ) * t ^ (-(1 : ℝ) / 3) - 2 * c)
  · exact ((continuous_id.rpow_const (by norm_num)).sub
      ((continuous_const.mul (continuous_id.pow 2)))).continuousOn
  · intro t ht
    rw [interior_Icc] at ht
    have h := (Real.hasDerivAt_rpow_const (x := t) (p := (5 : ℝ) / 3)
      (Or.inl ht.1.ne')).sub ((hasDerivAt_pow 2 t).const_mul c)
    convert h.hasDerivWithinAt using 1
    norm_num [c]
  · intro t ht
    rw [interior_Icc] at ht
    have h := ((Real.hasDerivAt_rpow_const (x := t) (p := (2 : ℝ) / 3)
      (Or.inl ht.1.ne')).const_mul (5 / 3 : ℝ)).sub
      (((hasDerivAt_id t).const_mul 2).const_mul c)
    convert h.hasDerivWithinAt using 1
    · funext y
      dsimp [c]
    · norm_num [c]
      ring
  · intro t ht
    rw [interior_Icc] at ht
    have h := Real.rpow_le_rpow_of_nonpos ht.1 ht.2.le
      (by norm_num : -(1 : ℝ) / 3 ≤ 0)
    dsimp [c]
    nlinarith

/-- Scalar midpoint defect, with the quotient interpreted as zero at zero. -/
theorem rpow_five_thirds_midpoint_defect (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (5 / 36 : ℝ) * (u - v) ^ 2 / (u + v) ^ ((1 : ℝ) / 3) ≤
      (u ^ ((5 : ℝ) / 3) + v ^ ((5 : ℝ) / 3)) / 2 -
        ((u + v) / 2) ^ ((5 : ℝ) / 3) := by
  by_cases hs : u + v = 0
  · have hu0 : u = 0 := by linarith
    have hv0 : v = 0 := by linarith
    simp [hu0, hv0, Real.zero_rpow (by norm_num : (5 : ℝ) / 3 ≠ 0)]
  have hpos : 0 < u + v := lt_of_le_of_ne (add_nonneg hu hv) (Ne.symm hs)
  have h := (convexOn_rpow_five_thirds_sub_sq (u + v)).2
    (show u ∈ Icc 0 (u + v) by constructor <;> linarith)
    (show v ∈ Icc 0 (u + v) by constructor <;> linarith)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at h
  have hm : (1 / 2 : ℝ) * u + (1 / 2 : ℝ) * v = (u + v) / 2 := by ring
  rw [hm, show -(1 : ℝ) / 3 = -((1 : ℝ) / 3) by ring,
    Real.rpow_neg hpos.le] at h
  rw [div_eq_mul_inv]
  nlinarith only [h]

end LiebThirring.TFMinimizer

end
