/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.CanonicalPackingGeometry
import Mathlib.Tactic

/-!
# Half-and-half budgets in the Swiss-cheese family

Limit convexity uses the even multiplicities of ball packing. Each size class is split
exactly into two equal groups, without changing its geometry.
-/

@[expose] public section

open Finset

namespace LiebThirring.ThermoLimit

theorem sum_fin_halves {n : ℕ} (hn : Even n) (a b : ℝ) :
    (∑ i : Fin n, if i.val < n / 2 then a else b) = (n : ℝ) * (a + b) / 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < (k + k) / 2 then a else b) (k + k),
    sum_range_add]
  have he : (k + k) / 2 = k := by omega
  rw [he]
  have hleft : (∑ i ∈ range k, if i < k then a else b) = (k : ℝ) * a := by
    calc
      _ = ∑ _i ∈ range k, a := by
        apply sum_congr rfl
        intro i hi
        simp only [ite_eq_left (mem_range.mp hi)]
      _ = _ := by simp
  have hright : (∑ i ∈ range k, if k + i < k then a else b) = (k : ℝ) * b := by
    have hnot (i : ℕ) : ¬k + i < k := by omega
    simp only [hnot, ite_false, sum_const, card_range, nsmul_eq_mul]
  rw [hleft, hright, Nat.cast_add]
  ring

/-- Split each size class into its two equal groups. -/
noncomputable def halfBudget (x y : ℕ → ℝ) (i : SwissCheeseLabel) : ℝ :=
  if i.2.val < swissCheeseMultiplicity i.1 / 2 then x i.1 else y i.1

theorem sum_halfBudget (x y : ℕ → ℝ) (t : ℕ) :
    ∑ i ∈ swissCheeseLevels t, halfBudget x y i =
      ((∑ j ∈ range t, (swissCheeseMultiplicity j : ℝ) * x j) +
        (∑ j ∈ range t, (swissCheeseMultiplicity j : ℝ) * y j)) / 2 := by
  classical
  rw [swissCheeseLevels, sum_sigma]
  simp only [halfBudget]
  simp_rw [sum_fin_halves (swissCheeseMultiplicity_even _)]
  simp_rw [mul_add, add_div]
  rw [sum_add_distrib, ← sum_div, ← sum_div, ← add_div]

theorem sum_standard_halfBudget {σ : ℝ} (hσ : 0 < σ) (ρ₁ ρ₂ : ℝ) (K : ℕ) :
    (∑ i ∈ swissCheeseLevels (K + 1),
      halfBudget (fun h => standardBudget σ ρ₁ (K - h))
        (fun h => standardBudget σ ρ₂ (K - h)) i) =
      ((ρ₁ + ρ₂) / 2) * standardVolume σ (K + 1) := by
  rw [sum_halfBudget]
  have hsum (ρ : ℝ) : (∑ j ∈ range (K + 1), (swissCheeseMultiplicity j : ℝ) *
      standardBudget σ ρ (K - j)) = ρ * standardVolume σ (K + 1) := by
    have hh := sum_standardBudget_labels hσ ρ K
    rw [swissCheeseLevels, sum_sigma] at hh
    simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
  rw [hsum ρ₁, hsum ρ₂]
  ring

end LiebThirring.ThermoLimit

end
