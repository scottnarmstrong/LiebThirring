/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Algebraic data for the Swiss-cheese packing

This module fixes the scale ratio, multiplicities, radii, and volume weights used in ball packing of
the thermodynamic-limit argument. The level index is zero-based: `j` represents the source's
level `h = j + 1`.
-/

@[expose] public section

open Filter Finset

namespace LiebThirring

/-- The residual volume ratio `γ = 27 / 28`. -/
noncomputable def swissCheeseGamma : ℝ := 27 / 28

/-- The multiplicity at zero-based level `j`, corresponding to `n_(j+1)`. -/
def swissCheeseMultiplicity (j : ℕ) : ℕ := 27 ^ j * 28 ^ (2 * (j + 1))

/-- The radius at zero-based level `j` inside a ball of radius `R`. -/
noncomputable def swissCheeseRadius (R : ℝ) (j : ℕ) : ℝ :=
  R * (28 : ℝ) ^ (-(j + 1 : ℤ))

theorem swissCheeseMultiplicity_pos (j : ℕ) : 0 < swissCheeseMultiplicity j := by
  simp [swissCheeseMultiplicity]

theorem swissCheeseMultiplicity_even (j : ℕ) : Even (swissCheeseMultiplicity j) := by
  rw [even_iff_two_dvd]
  apply dvd_mul_of_dvd_right
  exact dvd_pow (by norm_num) (by omega)

theorem swissCheeseRadius_pos {R : ℝ} (hR : 0 < R) (j : ℕ) :
    0 < swissCheeseRadius R j := by
  simp only [swissCheeseRadius]
  positivity

/-- The volume fraction occupied by zero-based level `j`. -/
theorem swissCheese_weight (j : ℕ) :
    (swissCheeseMultiplicity j : ℝ) * ((28 : ℝ) ^ (-(j + 1 : ℤ))) ^ 3 =
      (1 / 28 : ℝ) * swissCheeseGamma ^ j := by
  simp only [swissCheeseMultiplicity, swissCheeseGamma, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [zpow_neg, div_pow]
  field_simp
  have hz : (28 : ℝ) ^ ((j : ℤ) + 1) = 28 ^ (j + 1) := by
    rw [← Int.natCast_one, ← Int.natCast_add, zpow_natCast]
  rw [hz]
  calc
    (28 : ℝ) ^ (2 * (j + 1)) * 28 * 28 ^ j =
        28 ^ (2 * (j + 1)) * (28 ^ j * 28) := by ring
    _ = 28 ^ (2 * (j + 1) + (j + 1)) := by rw [← pow_succ, ← pow_add]
    _ = 28 ^ ((j + 1) * 3) := by
      congr 1
      omega
    _ = (28 ^ (j + 1)) ^ 3 := by rw [pow_mul]

/-- The fraction occupied by the first `t` levels is `1 - γ^t`. -/
theorem sum_swissCheese_weight (t : ℕ) :
    ∑ j ∈ range t, (1 / 28 : ℝ) * swissCheeseGamma ^ j = 1 - swissCheeseGamma ^ t := by
  rw [← Finset.mul_sum]
  change (1 / 28 : ℝ) * ∑ j ∈ range t, (27 / 28 : ℝ) ^ j = 1 - (27 / 28 : ℝ) ^ t
  have h := geom_sum_mul_neg (27 / 28 : ℝ) t
  norm_num at h ⊢
  linarith

/-- The residual fraction `γ^t` tends to zero. -/
theorem tendsto_swissCheese_residual :
    Tendsto (fun t : ℕ ↦ swissCheeseGamma ^ t) atTop (nhds 0) := by
  apply tendsto_pow_atTop_nhds_zero_of_lt_one
  · norm_num [swissCheeseGamma]
  · norm_num [swissCheeseGamma]

/-- The older-level surface sum, in the real form used by the boundary-loss estimate. -/
theorem sum_old_surface_multiplicity_real (j : ℕ) :
    1 + ∑ k ∈ range j, (27 : ℝ) ^ k = ((27 : ℝ) ^ j + 25) / 26 := by
  have h := geom_sum_mul (27 : ℝ) j
  norm_num at h ⊢
  linarith

/-- The older-level surface sum is at most its final coarse scale `27^j`. -/
theorem sum_old_surface_multiplicity_real_le (j : ℕ) :
    1 + ∑ k ∈ range j, (27 : ℝ) ^ k ≤ (27 : ℝ) ^ j := by
  rw [sum_old_surface_multiplicity_real]
  have hj : (1 : ℝ) ≤ 27 ^ j := one_le_pow₀ (by norm_num)
  linarith

/-- Multiplicity times squared relative radius is the surface weight `27^j`. -/
theorem swissCheese_surface_weight (j : ℕ) :
    (swissCheeseMultiplicity j : ℝ) * ((28 : ℝ) ^ (-(j + 1 : ℤ))) ^ 2 =
      (27 : ℝ) ^ j := by
  simp only [swissCheeseMultiplicity, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [zpow_neg]
  field_simp
  have hz : (28 : ℝ) ^ ((j : ℤ) + 1) = 28 ^ (j + 1) := by
    rw [← Int.natCast_one, ← Int.natCast_add, zpow_natCast]
  rw [hz, pow_two, ← pow_add]
  congr 1
  omega

/-- The residual volume fraction in terms of the next relative radius and surface weight. -/
theorem swissCheese_residual_eq_scale_mul_surface (j : ℕ) :
    swissCheeseGamma ^ j =
      28 * (28 : ℝ) ^ (-(j + 1 : ℤ)) * (27 : ℝ) ^ j := by
  simp only [swissCheeseGamma]
  rw [div_pow, zpow_neg]
  field_simp
  have hz : (28 : ℝ) ^ ((j : ℤ) + 1) = 28 ^ (j + 1) := by
    rw [← Int.natCast_one, ← Int.natCast_add, zpow_natCast]
  rw [hz, pow_succ']
  ring

/-- The fixed ratio `b = 28` satisfies the numerical packing condition. -/
theorem swissCheese_packing_constant :
    14 * Real.sqrt 3 + 6 / Real.pi < (28 : ℝ) := by
  have hsqrt : Real.sqrt 3 < (7 / 4 : ℝ) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 7 / 4), Real.sqrt_lt_sqrt_iff]
    · norm_num
    · positivity
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hdiv : 6 / Real.pi < (2 : ℝ) := by
    apply (div_lt_iff₀ (by positivity : 0 < Real.pi)).2
    linarith
  linarith

end LiebThirring

end
