/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! # Lower limits of bounded nonnegative real energy sequences -/

public section

open Filter

namespace LiebThirring

/-- Nonnegative bounded real energy terms may be combined before taking a lower limit. -/
theorem liminf_add_le_liminf_of_nonneg_bounded (a b : ℕ → ℝ) (A B : ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (haA : ∀ n, a n ≤ A)
    (hb0 : ∀ n, 0 ≤ b n) (hbB : ∀ n, b n ≤ B) :
    liminf a atTop + liminf b atTop ≤ liminf (fun n => a n + b n) atTop := by
  have hal : IsBoundedUnder (· ≥ ·) atTop a := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n : ℕ in atTop, 0 ≤ a n
    exact Eventually.of_forall ha0
  have hbl : IsBoundedUnder (· ≥ ·) atTop b := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n : ℕ in atTop, 0 ≤ b n
    exact Eventually.of_forall hb0
  have hau : IsBoundedUnder (· ≤ ·) atTop a := by
    refine ⟨A, ?_⟩
    change ∀ᶠ n : ℕ in atTop, a n ≤ A
    exact Eventually.of_forall haA
  have hbu : IsBoundedUnder (· ≤ ·) atTop b := by
    refine ⟨B, ?_⟩
    change ∀ᶠ n : ℕ in atTop, b n ≤ B
    exact Eventually.of_forall hbB
  exact le_liminf_add hal hau hbl hbu.isCoboundedUnder_ge

end LiebThirring
end
