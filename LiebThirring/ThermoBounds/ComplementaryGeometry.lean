/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoBounds.ComparisonLimits
import Mathlib.Tactic

/-! # Pointwise geometry of the complementary comparison -/

public section

open Set

namespace LiebThirring.ThermoBounds

/-- The elementary pointwise geometry used in the complementary lower comparison. -/
theorem complementary_geometry
    {ρ s W U η g : ℝ}
    (hρ : 0 < ρ) (hs : s ∈ Icc (ρ / 2) (2 * ρ))
    (hW : (28 : ℝ) ^ (-3 : ℤ) ≤ W) (_hW1 : W ≤ 1)
    (hU : 0 ≤ U) (hη : 0 ≤ η) (hsum : W + U + η = 1)
    (hg : g ∈ Icc (0 : ℝ) 1) (hηg : η ≤ g) :
    let c := 1 - g
    let Δ := 1 - W - c * U
    let sp := s * (W + c * U)
    0 ≤ Δ ∧ Δ ≤ 2 * g ∧
      0 ≤ U ∧ U ≤ 1 ∧
      sp ∈ Icc ((ρ / 2) * (28 : ℝ) ^ (-3 : ℤ)) (2 * ρ) ∧
      |sp - s| ≤ 4 * ρ * g ∧
      Δ = (1 - c) * (1 - W) + c * η := by
  dsimp
  have hW0 : 0 ≤ W := le_trans (by norm_num) hW
  have hU1 : U ≤ 1 := by linarith
  have hc0 : 0 ≤ 1 - g := sub_nonneg.mpr hg.2
  have hdef := complementary_deficit_bounds hW0 hU hη hsum hηg
  have hfactorLower : (28 : ℝ) ^ (-3 : ℤ) ≤ W + (1 - g) * U :=
    hW.trans (le_add_of_nonneg_right (mul_nonneg hc0 hU))
  have hfactorUpper : W + (1 - g) * U ≤ 1 := by
    nlinarith
  have hs0 : 0 ≤ s := le_trans (by linarith [hρ]) hs.1
  have hspLower₁ : (ρ / 2) * (28 : ℝ) ^ (-3 : ℤ) ≤
      s * (28 : ℝ) ^ (-3 : ℤ) :=
    mul_le_mul_of_nonneg_right hs.1 (by norm_num)
  have hspLower₂ : s * (28 : ℝ) ^ (-3 : ℤ) ≤ s * (W + (1 - g) * U) :=
    mul_le_mul_of_nonneg_left hfactorLower hs0
  have hspUpper : s * (W + (1 - g) * U) ≤ 2 * ρ :=
    (mul_le_mul_of_nonneg_left hfactorUpper hs0).trans (by simpa using hs.2)
  have hdiff : s * (W + (1 - g) * U) - s =
      -s * (1 - W - (1 - g) * U) := by ring
  have habs : |s * (W + (1 - g) * U) - s| ≤ 4 * ρ * g := by
    rw [hdiff, abs_mul, abs_neg, abs_of_nonneg hs0, abs_of_nonneg hdef.1]
    have hmul := mul_le_mul hdef.2 hs.2 hs0 (mul_nonneg (by norm_num) hg.1)
    nlinarith
  have hid : 1 - W - (1 - g) * U =
      (1 - (1 - g)) * (1 - W) + (1 - g) * η := by
    nlinarith
  exact ⟨hdef.1, hdef.2, hU, hU1,
    ⟨hspLower₁.trans hspLower₂, hspUpper⟩, habs, hid⟩

end LiebThirring.ThermoBounds

end
