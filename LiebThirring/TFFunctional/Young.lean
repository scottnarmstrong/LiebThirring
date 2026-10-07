/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.MeanInequalities

/-! # A scaled Young inequality for Thomas--Fermi coercivity -/

public section

namespace LiebThirring.TFFunctional

/-- Young's inequality with the conjugate exponents used to absorb the
`3/5`-power attraction estimate into the Thomas--Fermi kinetic term. -/
theorem mul_rpow_three_fifths_le (a A K : ℝ) (ha : 0 < a) (hA : 0 ≤ A) (hK : 0 ≤ K) :
    A * K ^ ((3 : ℝ) / 5) ≤ a / 2 * K +
      (2 / 5 : ℝ) * (A * ((5 / 6 : ℝ) * a) ^ (-(3 : ℝ) / 5)) ^ ((5 : ℝ) / 2) := by
  let u := ((5 / 6 : ℝ) * a) ^ ((3 : ℝ) / 5) * K ^ ((3 : ℝ) / 5)
  let v := A * ((5 / 6 : ℝ) * a) ^ (-(3 : ℝ) / 5)
  have hua : 0 ≤ u := mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hK _)
  have hva : 0 ≤ v := mul_nonneg hA (Real.rpow_nonneg (by positivity) _)
  have hpq : (5 / 3 : ℝ).HolderConjugate (5 / 2 : ℝ) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hy := Real.young_inequality_of_nonneg hua hva hpq
  dsimp only [u, v] at hy
  have hab : 0 < (5 / 6 : ℝ) * a := mul_pos (by norm_num) ha
  let B := ((5 / 6 : ℝ) * a) ^ ((3 : ℝ) / 5) * K ^ ((3 : ℝ) / 5)
  have hu : B ^ ((5 : ℝ) / 3) / ((5 : ℝ) / 3) = a / 2 * K := by
    dsimp only [B]
    rw [Real.mul_rpow (Real.rpow_nonneg hab.le _) (Real.rpow_nonneg hK _),
      ← Real.rpow_mul hab.le, ← Real.rpow_mul hK]
    norm_num
    ring
  have huv : ((5 / 6 : ℝ) * a) ^ ((3 : ℝ) / 5) * K ^ ((3 : ℝ) / 5) *
      (A * ((5 / 6 : ℝ) * a) ^ (-(3 : ℝ) / 5)) = A * K ^ ((3 : ℝ) / 5) := by
    calc
      _ = A * K ^ ((3 : ℝ) / 5) *
          (((5 / 6 : ℝ) * a) ^ ((3 : ℝ) / 5) *
            ((5 / 6 : ℝ) * a) ^ (-(3 : ℝ) / 5)) := by ring
      _ = A * K ^ ((3 : ℝ) / 5) := by
        rw [← Real.rpow_add hab]
        norm_num
  rw [hu, huv] at hy
  convert hy using 1
  ring

end LiebThirring.TFFunctional

end
