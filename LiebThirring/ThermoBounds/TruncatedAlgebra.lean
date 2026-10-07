/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoBounds.Energy
import Mathlib.Tactic

/-!
# Exact budgets and energy weights for finite truncations

Interior packing comparison and complementary packing comparison use classes `j < t` inside cubes of volume `V_k`, with
`t < k`. Thus all standard indices `k-j-1` are positive: the inflated seed
of canonical recurrence never occurs in these comparisons.
-/

public section

open Finset Metric
open LiebThirring.ThermoLimit

namespace LiebThirring.ThermoBounds

theorem truncatedVolume_weight {k j : ℕ} (hj : j < k) :
    (swissCheeseMultiplicity j : ℝ) * standardVolume ballVolumeConstant (k - j - 1) =
      standardVolume ballVolumeConstant k * ((1 / 28 : ℝ) * swissCheeseGamma ^ j) := by
  have he : (k - j - 1) + j + 1 = k := by omega
  simpa only [he] using standardVolume_weight ballVolumeConstant_pos (k - j - 1) j

theorem sum_truncatedVolume_mul {k t : ℕ} (htk : t ≤ k) (g : ℕ → ℝ) :
    (∑ j ∈ range t, (swissCheeseMultiplicity j : ℝ) *
      (standardVolume ballVolumeConstant (k - j - 1) * g j)) =
      standardVolume ballVolumeConstant k *
        ∑ j ∈ range t, ((1 / 28 : ℝ) * swissCheeseGamma ^ j) * g j := by
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [← mul_assoc, truncatedVolume_weight (lt_of_lt_of_le (mem_range.mp hj) htk)]
  ring

theorem sum_truncatedBudget {k t : ℕ} (htk : t ≤ k) (s : ℝ) :
    (∑ j ∈ range t, (swissCheeseMultiplicity j : ℝ) *
      (s * standardVolume ballVolumeConstant (k - j - 1))) =
      s * standardVolume ballVolumeConstant k * (1 - swissCheeseGamma ^ t) := by
  have he := sum_truncatedVolume_mul htk (fun _ => s)
  simp only [← sum_mul, sum_swissCheese_weight] at he
  calc
    _ = ∑ j ∈ range t, (swissCheeseMultiplicity j : ℝ) *
        (standardVolume ballVolumeConstant (k - j - 1) * s) := by
      apply sum_congr rfl
      intro j _
      rw [mul_comm s]
    _ = _ := by rw [he]; ring

theorem interpolate_standard_energy {E : Set Position → ℕ → ℝ} {j : ℕ}
    (hj : 0 < j) (s : ℝ) :
    interpolate (E (ball (0 : Position) ((28 : ℝ) ^ j)))
        (s * standardVolume ballVolumeConstant j) =
      standardVolume ballVolumeConstant j * neutralStandardSequence E j s := by
  rw [neutralStandardSequence_eq hj]
  exact (mul_div_cancel₀ _ (standardVolume_pos ballVolumeConstant_pos j).ne').symm

theorem sum_truncatedEnergy {E : Set Position → ℕ → ℝ} {k t : ℕ}
    (htk : t < k) (s : ℝ) :
    (∑ j ∈ range t, (swissCheeseMultiplicity j : ℝ) *
      interpolate (E (ball (0 : Position) ((28 : ℝ) ^ (k - j - 1))))
        (s * standardVolume ballVolumeConstant (k - j - 1))) =
      standardVolume ballVolumeConstant k *
        ∑ j ∈ range t, ((1 / 28 : ℝ) * swissCheeseGamma ^ j) *
          neutralStandardSequence E (k - j - 1) s := by
  calc
    _ = ∑ j ∈ range t, (swissCheeseMultiplicity j : ℝ) *
        (standardVolume ballVolumeConstant (k - j - 1) *
          neutralStandardSequence E (k - j - 1) s) := by
      apply sum_congr rfl
      intro j hj
      rw [interpolate_standard_energy (by have := mem_range.mp hj; omega)]
    _ = _ := sum_truncatedVolume_mul htk.le _

end LiebThirring.ThermoBounds

end
