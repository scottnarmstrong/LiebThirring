/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Vanishing kinetic and mixed Coulomb escape costs -/

public section

open Filter
open scoped Topology

namespace LiebThirring

/-- The exact `L⁻² K + n/(3L)` error tends to zero at infinity. -/
theorem escape_error_tendsto_zero (K : ℝ) (n : ℕ) :
    Tendsto (fun L : ℝ => L⁻¹ ^ 2 * K + (n : ℝ) / (3 * L)) atTop (𝓝 0) := by
  have hi : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have ht := ((hi.pow 2).mul_const K).add (hi.const_mul ((n : ℝ) / 3))
  simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero, zero_add] at ht
  convert ht using 1
  ext L
  rw [div_eq_mul_inv, mul_inv_rev, div_eq_mul_inv]
  ring

/-- Every positive error tolerance admits a positive finite scale. -/
theorem escape_exists_scale (K : ℝ) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ L⁻¹ ^ 2 * K + (n : ℝ) / (3 * L) < ε := by
  have he := (escape_error_tendsto_zero K n).eventually (eventually_lt_nhds hε)
  obtain ⟨L, hL, heL⟩ := (eventually_gt_atTop (0 : ℝ)).and he |>.exists
  exact ⟨L, hL, heL⟩

end LiebThirring

end
