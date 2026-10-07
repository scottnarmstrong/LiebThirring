/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.SwissCheeseAlgebra
import Mathlib.Tactic

/-!
# Exact budgets for the canonical standard sequence

The canonical recurrence. The volume parameter is the
positive unit-ball volume.
These are internal algebraic helpers, with no thermodynamic-limit assertion.
-/

@[expose] public section

open Finset

namespace LiebThirring.ThermoLimit

/-- Volume of the standard ball of radius `28 ^ k`. -/
noncomputable def standardVolume (σ : ℝ) (k : ℕ) : ℝ := σ * (28 : ℝ) ^ (3 * k)

/-- Real multiplet budget: only the unit-radius seed has inflated density. -/
noncomputable def standardBudget (σ ρ : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 28 * ρ * σ else ρ * standardVolume σ k

/-- Interpolated energy per volume, with the inflated seed at index zero. -/
noncomputable def standardSequence (F : ℕ → ℝ → ℝ) (σ ρ : ℝ) (k : ℕ) : ℝ :=
  F k (standardBudget σ ρ k) / standardVolume σ k

theorem standardVolume_pos {σ : ℝ} (hσ : 0 < σ) (k : ℕ) :
    0 < standardVolume σ k := mul_pos hσ (pow_pos (by norm_num) _)

@[simp] theorem standardVolume_zero (σ : ℝ) : standardVolume σ 0 = σ := by
  simp [standardVolume]

@[simp] theorem standardBudget_zero (σ ρ : ℝ) : standardBudget σ ρ 0 = 28 * ρ * σ := by
  simp [standardBudget]

theorem standardBudget_succ (σ ρ : ℝ) (k : ℕ) :
    standardBudget σ ρ (k + 1) = ρ * standardVolume σ (k + 1) := by
  simp [standardBudget]

theorem standardBudget_nonneg {σ ρ : ℝ} (hσ : 0 ≤ σ) (hρ : 0 ≤ ρ) (k : ℕ) :
    0 ≤ standardBudget σ ρ k := by
  unfold standardBudget standardVolume
  split_ifs <;> positivity

theorem continuous_standardBudget (σ : ℝ) (k : ℕ) :
    Continuous (fun ρ : ℝ => standardBudget σ ρ k) := by
  unfold standardBudget
  split_ifs <;> fun_prop

theorem standardSequence_continuousOn {F : ℕ → ℝ → ℝ} {σ : ℝ} (hσ : 0 ≤ σ)
    (hF : ∀ k, ContinuousOn (F k) (Set.Ici 0)) (k : ℕ) :
    ContinuousOn (fun ρ => standardSequence F σ ρ k) (Set.Ici 0) := by
  exact ((hF k).comp (continuous_standardBudget σ k).continuousOn
    (fun ρ hρ => standardBudget_nonneg hσ hρ k)).div_const _

theorem standardSequence_vacuum {F : ℕ → ℝ → ℝ} {σ : ℝ}
    (hF : ∀ k, F k 0 = 0) (k : ℕ) : standardSequence F σ 0 k = 0 := by
  simp [standardSequence, standardBudget, hF]

/-- Each source multiplicity gives exactly its geometric volume weight. -/
theorem standardVolume_weight {σ : ℝ} (hσ : 0 < σ) (j h : ℕ) :
    (swissCheeseMultiplicity h : ℝ) * standardVolume σ j =
      standardVolume σ (j + h + 1) * ((1 / 28 : ℝ) * swissCheeseGamma ^ h) := by
  unfold standardVolume swissCheeseMultiplicity swissCheeseGamma
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_pow]
  have he : 3 * (j + h + 1) = 3 * j + 2 * (h + 1) + (h + 1) := by omega
  rw [he, pow_add, pow_add, pow_succ]
  field_simp

/-- Budget coefficients include a factor `28` only in the seed class. -/
theorem standardBudget_weight {σ : ℝ} (hσ : 0 < σ) (ρ : ℝ) {K j : ℕ} (hj : j < K) :
    (swissCheeseMultiplicity (K - j - 1) : ℝ) * standardBudget σ ρ j =
      ρ * standardVolume σ K *
        (((1 / 28 : ℝ) * swissCheeseGamma ^ (K - j - 1)) *
          (if j = 0 then 28 else 1)) := by
  have he : j + (K - j - 1) + 1 = K := by omega
  have hw := standardVolume_weight hσ j (K - j - 1)
  rw [he] at hw
  by_cases hz : j = 0
  · subst j
    simp only [standardBudget_zero, standardVolume_zero, ite_true] at *
    calc
      _ = (28 * ρ) * ((swissCheeseMultiplicity (K - 0 - 1) : ℝ) * σ) := by ring
      _ = _ := by rw [hw]; ring
  · simp only [standardBudget, ite_eq_right hz, mul_one]
    calc
      _ = ρ * ((swissCheeseMultiplicity (K - j - 1) : ℝ) * standardVolume σ j) := by ring
      _ = _ := by rw [hw]; ring

/-- The inflated seed compensates exactly for all the unfilled volume. -/
theorem sum_standardBudget_coefficients (K : ℕ) :
    ∑ j ∈ range (K + 1),
      ((1 / 28 : ℝ) * swissCheeseGamma ^ (K + 1 - j - 1)) *
        (if j = 0 then 28 else 1) = 1 := by
  rw [sum_range_succ']
  simp only [Nat.add_sub_add_right, Nat.sub_zero, Nat.succ_ne_zero, ite_false,
    ite_true, mul_one]
  have hs : (∑ j ∈ range K, (1 / 28 : ℝ) * swissCheeseGamma ^ (K - j - 1)) =
      1 - swissCheeseGamma ^ K := by
    rw [← sum_swissCheese_weight K]
    simpa only [Nat.sub_sub, Nat.add_comm] using
      sum_range_reflect (fun j => (1 / 28 : ℝ) * swissCheeseGamma ^ j) K
  rw [hs]
  have he : K + 1 - 1 = K := by omega
  rw [he]
  ring

/-- Exact total multiplet budget at every positive scale. -/
theorem sum_standardBudget {σ : ℝ} (hσ : 0 < σ) (ρ : ℝ) (K : ℕ) :
    ∑ j ∈ range (K + 1), (swissCheeseMultiplicity (K + 1 - j - 1) : ℝ) *
      standardBudget σ ρ j = ρ * standardVolume σ (K + 1) := by
  calc
    _ = ∑ j ∈ range (K + 1), ρ * standardVolume σ (K + 1) *
        (((1 / 28 : ℝ) * swissCheeseGamma ^ (K + 1 - j - 1)) *
          (if j = 0 then 28 else 1)) := by
      apply sum_congr rfl
      intro j hj
      exact standardBudget_weight hσ ρ (mem_range.mp hj)
    _ = _ := by rw [← mul_sum, sum_standardBudget_coefficients, mul_one]

/-- The grouped energy sum has precisely the renewal weights. -/
theorem standardSequence_weighted_sum
    {F : ℕ → ℝ → ℝ} {σ ρ : ℝ} (hσ : 0 < σ) (K : ℕ) :
    (∑ j ∈ range (K + 1), (swissCheeseMultiplicity (K + 1 - j - 1) : ℝ) *
      F j (standardBudget σ ρ j)) =
      (∑ j ∈ range (K + 1), (1 / 28 : ℝ) * swissCheeseGamma ^ (K - j) *
        standardSequence F σ ρ j) * standardVolume σ (K + 1) := by
  unfold standardSequence
  rw [sum_mul]
  apply sum_congr rfl
  intro j hj
  have he : j + (K - j) + 1 = K + 1 := by have := mem_range.mp hj; omega
  have hw := standardVolume_weight hσ j (K - j)
  rw [he] at hw
  have he' : K + 1 - j - 1 = K - j := by omega
  rw [he']
  have hvj := (standardVolume_pos hσ j).ne'
  have hw' : (swissCheeseMultiplicity (K - j) : ℝ) =
      standardVolume σ (K + 1) * ((1 / 28 : ℝ) * swissCheeseGamma ^ (K - j)) /
        standardVolume σ j := (eq_div_iff hvj).mpr hw
  rw [hw']
  ring

/-- Divide a grouped packing comparison by the containing volume. The
packing premise here is an internal intermediate inequality, not an input to
any thermodynamic theorem. -/
theorem standardSequence_recurrence_of_grouped_packing
    {F : ℕ → ℝ → ℝ} {σ ρ : ℝ} (hσ : 0 < σ) (K : ℕ)
    (hpacking : F (K + 1) (ρ * standardVolume σ (K + 1)) ≤
      ∑ j ∈ range (K + 1), (swissCheeseMultiplicity (K + 1 - j - 1) : ℝ) *
        F j (standardBudget σ ρ j)) :
    standardSequence F σ ρ (K + 1) ≤
      ∑ j ∈ range (K + 1), (1 / 28 : ℝ) * swissCheeseGamma ^ (K - j) *
        standardSequence F σ ρ j := by
  rw [standardSequence_weighted_sum hσ] at hpacking
  exact (div_le_iff₀ (standardVolume_pos hσ (K + 1))).mpr
    (by simpa only [standardSequence, standardBudget_succ] using hpacking)

/-- Extensive stability persists in every uninflated member of the sequence. -/
theorem standardSequence_lower_bound {F : ℕ → ℝ → ℝ} {σ ρ A : ℝ}
    (hσ : 0 < σ) (hρ : 0 ≤ ρ)
    (hlower : ∀ k x, 0 ≤ x → -A * x ≤ F k x) (k : ℕ) :
    -A * ρ ≤ standardSequence F σ ρ (k + 1) := by
  unfold standardSequence
  rw [standardBudget_succ]
  apply (le_div_iff₀ (standardVolume_pos hσ _)).2
  convert hlower (k + 1) (ρ * standardVolume σ (k + 1))
    (mul_nonneg hρ (standardVolume_pos hσ _).le) using 1
  ring

end LiebThirring.ThermoLimit

end
