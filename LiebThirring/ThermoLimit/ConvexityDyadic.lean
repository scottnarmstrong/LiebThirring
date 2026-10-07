/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.Convexity
import Mathlib.Tactic

/-! # Dyadic convex combinations from midpoint convexity -/

public section

namespace LiebThirring.ThermoLimit

/-- Midpoint convexity on nonnegative reals implies the convexity inequality at every
dyadic coefficient. -/
theorem midpoint_convex_dyadic
    {f : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ x → ∀ y, 0 ≤ y → f ((x + y) / 2) ≤ (f x + f y) / 2)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n m : ℕ) (hm : m ≤ 2 ^ n) :
    f (((m : ℝ) / (2 : ℝ) ^ n) * x + (1 - (m : ℝ) / (2 : ℝ) ^ n) * y) ≤
      ((m : ℝ) / (2 : ℝ) ^ n) * f x +
        (1 - (m : ℝ) / (2 : ℝ) ^ n) * f y := by
  induction n generalizing m with
  | zero =>
      interval_cases m <;> norm_num
  | succ n ih =>
      obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
      · have hk : k ≤ 2 ^ n := by
          rw [pow_succ] at hm
          omega
        have h := ih k hk
        have hcoef :
            (((2 * k : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) =
              (k : ℝ) / (2 : ℝ) ^ n := by
          push_cast
          rw [pow_succ]
          field_simp
        simpa only [hcoef] using h
      · have hk : k ≤ 2 ^ n := by
          rw [pow_succ] at hm
          omega
        have hk1 : k + 1 ≤ 2 ^ n := by
          rw [pow_succ] at hm
          omega
        let a : ℝ := (k : ℝ) / (2 : ℝ) ^ n
        let b : ℝ := ((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n
        let p : ℝ := a * x + (1 - a) * y
        let q : ℝ := b * x + (1 - b) * y
        have ha0 : 0 ≤ a := div_nonneg (Nat.cast_nonneg k) (by positivity)
        have ha1 : a ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact_mod_cast hk
        have hb0 : 0 ≤ b := div_nonneg (Nat.cast_nonneg _) (by positivity)
        have hb1 : b ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact_mod_cast hk1
        have hp0 : 0 ≤ p := by
          dsimp [p]
          positivity
        have hq0 : 0 ≤ q := by
          dsimp [q]
          positivity
        have hpk := ih k hk
        have hqk := ih (k + 1) hk1
        have hmid := hf p hp0 q hq0
        have harg :
            (((((2 * k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) * x +
                (1 - ((2 * k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) * y)) =
              (p + q) / 2 := by
          dsimp [p, q, a, b]
          push_cast
          rw [pow_succ]
          field_simp
          ring
        rw [harg]
        calc
          f ((p + q) / 2) ≤ (f p + f q) / 2 := hmid
          _ ≤ (((a * f x + (1-a) * f y) +
              (b * f x + (1-b) * f y)) / 2) := by
            have hpbound : f p ≤ a * f x + (1-a) * f y := by
              simpa [p, a] using hpk
            have hqbound : f q ≤ b * f x + (1-b) * f y := by
              simpa [q, b] using hqk
            gcongr
          _ = (((2 * k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) * f x +
                (1 - ((2 * k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) * f y := by
            dsimp [a, b]
            push_cast
            rw [pow_succ]
            field_simp
            ring

end LiebThirring.ThermoLimit

end
