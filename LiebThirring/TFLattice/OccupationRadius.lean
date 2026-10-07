/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.FilledModes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Cube-root bounds on filled occupations

The comparison cube has more than `n` admissible modes. This gives a coarse
radius of order `n^(1/3)`, independently of any Weyl asymptotic, and is enough
for the filled-density convergence collision estimate. Source: Lieb–Simon (1977) III.13, pp. 67–69.
-/

@[expose] public section

namespace LiebThirring.TFLattice

theorem cube_root_cubed (n : ℕ) : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = n := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  norm_num

theorem card_lt_comparison_box {q : ℕ} (hq : 0 < q) (n : ℕ) :
    n < q * (⌈(n : ℝ) ^ (1 / 3 : ℝ)⌉₊ + 1) ^ 3 := by
  have hr := Nat.le_ceil ((n : ℝ) ^ (1 / 3 : ℝ))
  have hp : (n : ℝ) ^ (1 / 3 : ℝ) <
      (⌈(n : ℝ) ^ (1 / 3 : ℝ)⌉₊ + 1 : ℕ) := by
    push_cast
    linarith
  have hroot := Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 3 : ℝ)
  have hcube : (n : ℝ) < ((⌈(n : ℝ) ^ (1 / 3 : ℝ)⌉₊ + 1 : ℕ) : ℝ) ^ 3 := by
    calc
      _ = ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := (cube_root_cubed n).symm
      _ < _ := pow_lt_pow_left₀ hp hroot (by decide : (3 : ℕ) ≠ 0)
  have hn : n < (⌈(n : ℝ) ^ (1 / 3 : ℝ)⌉₊ + 1) ^ 3 := by exact_mod_cast hcube
  have hq' : 1 ≤ q := hq
  exact hn.trans_le (by simpa only [one_mul] using
    Nat.mul_le_mul_right ((⌈(n : ℝ) ^ (1 / 3 : ℝ)⌉₊ + 1) ^ 3) hq')

theorem dirichlet_occupation_subset_comparison_box {q : ℕ} (hq : 0 < q)
    {s : Finset (ModeIndex q)} (hs : IsFilled IsDirichletIndex s) :
    s ⊆ modeBox q 0 (2 * (1 + (⌈(s.card : ℝ) ^ (1 / 3 : ℝ)⌉₊ + 1)) + 1) := by
  apply subset_modeBox_of_isFilled hs
  · intro r hr
    exact isDirichletIndex_of_mem_modeBox (by decide) hr
  · exact card_lt_comparison_box hq s.card

theorem comparison_box_side_le {n : ℕ} (hn : 1 ≤ n) :
    ((2 * (1 + (⌈(n : ℝ) ^ (1 / 3 : ℝ)⌉₊ + 1)) + 1 : ℕ) : ℝ) ≤
      9 * (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hroot : 1 ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 3 : ℝ))
  push_cast
  linarith

end LiebThirring.TFLattice

end
