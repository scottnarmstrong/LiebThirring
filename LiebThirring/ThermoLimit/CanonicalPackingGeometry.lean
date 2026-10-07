/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.CanonicalAlgebra
public import LiebThirring.Packing.SwissCheeseScaling
import Mathlib.Tactic

/-!
# Standard-scale form of the actual Swiss-cheese packing

Canonical recurrence reindexes the geometric size classes of ball packing. These lemmas use the
proved geometric construction, including its exact multiplicities.
-/

public section

open Finset Metric Set

namespace LiebThirring.ThermoLimit

/-- At scale `K+1`, size class `h` has the standard radius `28^(K-h)`. -/
theorem swissCheeseRadius_standard {K h : ℕ} (hh : h ≤ K) :
    swissCheeseRadius ((28 : ℝ) ^ (K + 1)) h = (28 : ℝ) ^ (K - h) := by
  unfold swissCheeseRadius
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (28 : ℝ) ≠ 0)]
  have he : ((K + 1 : ℕ) : ℤ) + -(h + 1 : ℤ) = ((K - h : ℕ) : ℤ) := by omega
  rw [he, zpow_natCast]

/-- Reindex a label sum by the radius index instead of the size-class index. -/
theorem sum_swissCheeseLevels_standard (g : ℕ → ℝ) (K : ℕ) :
    ∑ i ∈ swissCheeseLevels (K + 1), g (K - i.1) =
      ∑ j ∈ range (K + 1), (swissCheeseMultiplicity (K - j) : ℝ) * g j := by
  classical
  rw [swissCheeseLevels, sum_sigma]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ K := by have := mem_range.mp hj; omega
  have he : K + 1 - 1 - j = K - j := by omega
  have he' : K - (K - j) = j := by omega
  rw [he, he']

theorem sum_sizeClass_standard (g : ℕ → ℝ) (K : ℕ) :
    (∑ h ∈ range (K + 1), (swissCheeseMultiplicity h : ℝ) * g (K - h)) =
      ∑ j ∈ range (K + 1), (swissCheeseMultiplicity (K - j) : ℝ) * g j := by
  classical
  have hh := sum_swissCheeseLevels_standard g K
  rw [swissCheeseLevels, sum_sigma] at hh
  simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using hh

/-- The exact seed and later budgets sum to the containing ball's budget. -/
theorem sum_standardBudget_labels {σ : ℝ} (hσ : 0 < σ) (ρ : ℝ) (K : ℕ) :
    ∑ i ∈ swissCheeseLevels (K + 1), standardBudget σ ρ (K - i.1) =
      ρ * standardVolume σ (K + 1) := by
  rw [sum_swissCheeseLevels_standard]
  convert sum_standardBudget hσ ρ K using 1
  apply sum_congr rfl
  intro j _
  have he : K + 1 - j - 1 = K - j := by omega
  rw [he]

/-- Actual finite disjoint balls used by the canonical recurrence. -/
theorem exists_standard_ball_packing (K : ℕ) :
    ∃ c : SwissCheeseLabel → Position,
      (∀ i ∈ swissCheeseLevels (K + 1),
        closedBall (c i) ((28 : ℝ) ^ (K - i.1)) ⊆
          ball (0 : Position) ((28 : ℝ) ^ (K + 1))) ∧
      (swissCheeseLevels (K + 1) : Set SwissCheeseLabel).PairwiseDisjoint
        (fun i => ball (c i) ((28 : ℝ) ^ (K - i.1))) := by
  obtain ⟨c, hc, hd⟩ := exists_swissCheese_ball (0 : Position)
    (pow_pos (by norm_num : (0 : ℝ) < 28) (K + 1))
  refine ⟨c, ?_, ?_⟩
  · intro i hi
    have hh : i.1 ≤ K := by have := mem_swissCheeseLevels.mp hi; omega
    simpa only [swissCheeseRadius_standard hh] using hc i
  · intro i hi j hj hij
    have hi' : i.1 ≤ K := by have := mem_swissCheeseLevels.mp hi; omega
    have hj' : j.1 ≤ K := by have := mem_swissCheeseLevels.mp hj; omega
    simpa only [swissCheeseRadius_standard hi', swissCheeseRadius_standard hj'] using hd hij

end LiebThirring.ThermoLimit

end
