/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Configuration

/-! # Regrouping ordered electron pairs -/

public section

namespace LiebThirring

/-- An ordered sum without its diagonal regroups by the increasing-pair convention. -/
theorem sum_ordered_pairs_eq_sum_increasing {N : ℕ} (f : Fin N → Fin N → ℝ) :
    (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), f i j) =
      ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (f i j + f j i) := by
  classical
  have hp (i j : Fin N) : (if j ≠ i then f i j else 0) =
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_gt h, not_lt_of_gt h]
    · subst j
      simp
    · simp [h, ne_of_lt h, not_lt_of_gt h]
  simp only [Finset.sum_filter]
  simp_rw [hp, Finset.sum_add_distrib]
  have hq (i j : Fin N) : (if i < j then f i j + f j i else 0) =
      (if i < j then f i j else 0) + (if i < j then f j i else 0) := by
    split_ifs <;> simp
  simp_rw [hq, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]

end LiebThirring

end
