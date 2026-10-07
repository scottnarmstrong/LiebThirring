/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.BigOperators.Fin

/-! # Decomposing finite ordered-pair sums -/

public section
open scoped BigOperators
namespace LiebThirring

/-- Split an ordered-pair sum on `Fin (n+1)` into the pairs involving the
first index and the ordered pairs among the remaining indices. -/
theorem sum_orderedPairs_fin_succ {A : Type*} [AddCommMonoid A] (n : ℕ)
    (F : Fin (n+1) → Fin (n+1) → A) :
    (∑ i, ∑ j with i < j, F i j) =
      (∑ j : Fin n, F 0 j.succ) +
        ∑ i : Fin n, ∑ j : Fin n with i < j, F i.succ j.succ := by
  classical
  rw [Fin.sum_univ_succ]
  congr 1
  · rw [Finset.sum_filter]
    rw [Fin.sum_univ_succ]
    simp
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_filter]
    rw [Fin.sum_univ_succ]
    simp
    rw [Finset.sum_filter]

end LiebThirring
end
