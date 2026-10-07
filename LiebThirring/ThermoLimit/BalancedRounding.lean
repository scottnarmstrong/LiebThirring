/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.Interpolation
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Balanced finite rounding

The prefix-floor construction couples all regional roundings through one offset.  Telescoping
makes its total exact whenever the total real budget is integral.
-/

@[expose] public section

namespace LiebThirring.ThermoLimit

/-- Prefix sum of a finite vector of real budgets. -/
noncomputable def budgetPrefix {k : ℕ} (x : Fin k → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, if hi : i < k then x ⟨i, hi⟩ else 0

/-- Coupled prefix-floor rounding with offset `u`. -/
noncomputable def balancedRound {k : ℕ} (x : Fin k → ℝ) (u : ℝ) (i : Fin k) : ℤ :=
  ⌊budgetPrefix x (i.val + 1) + u⌋ - ⌊budgetPrefix x i.val + u⌋

theorem budgetPrefix_succ {k : ℕ} (x : Fin k → ℝ) (i : Fin k) :
    budgetPrefix x (i.val + 1) = budgetPrefix x i.val + x i := by
  simp only [budgetPrefix, Finset.sum_range_succ, i.isLt, ↓reduceDIte]

/-- Prefix rounding telescopes exactly. -/
theorem sum_balancedRound {k : ℕ} (x : Fin k → ℝ) (u : ℝ) :
    ∑ i, balancedRound x u i = ⌊(∑ i, x i) + u⌋ - ⌊u⌋ := by
  rw [Finset.sum_fin_eq_sum_range]
  simp only [balancedRound]
  have hremove :
      (∑ i ∈ Finset.range k,
        if h : i < k then
          ⌊budgetPrefix x (i + 1) + u⌋ - ⌊budgetPrefix x i + u⌋ else 0) =
      ∑ i ∈ Finset.range k,
        (⌊budgetPrefix x (i + 1) + u⌋ - ⌊budgetPrefix x i + u⌋) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  rw [hremove]
  have telescoping (f : ℕ → ℤ) (n : ℕ) :
      ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  calc
    _ = ⌊budgetPrefix x k + u⌋ - ⌊budgetPrefix x 0 + u⌋ :=
      telescoping (fun j => ⌊budgetPrefix x j + u⌋) k
    _ = ⌊(∑ i, x i) + u⌋ - ⌊u⌋ := by
      simp [budgetPrefix, Finset.sum_fin_eq_sum_range]

/-- Each prefix-floor allocation differs from its real regional budget by less than one. -/
theorem abs_balancedRound_sub_lt_one {k : ℕ} (x : Fin k → ℝ) (u : ℝ) (i : Fin k) :
    |(balancedRound x u i : ℝ) - x i| < 1 := by
  rw [balancedRound, Int.cast_sub]
  have hp := budgetPrefix_succ x i
  rw [hp]
  have ha := Int.sub_one_lt_floor (budgetPrefix x (i.val + 1) + u)
  have hb := Int.floor_le (budgetPrefix x (i.val + 1) + u)
  have hc := Int.sub_one_lt_floor (budgetPrefix x i.val + u)
  have hd := Int.floor_le (budgetPrefix x i.val + u)
  rw [hp] at ha hb
  rw [abs_lt]
  constructor <;> linarith

end LiebThirring.ThermoLimit

end
