/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Electrostatics.Gaussian

/-! # Ordered pair sums and electron repulsion

A symmetric off-diagonal pair sum is twice its strict upper-triangle sum.
The identity holds in the nonnegative extended reals, including collisions;
it identifies the factor one half in the Slater direct-minus-exchange formula.
kinetic normalization; direct proof finite algebra.
-/

public section
open scoped ENNReal
namespace LiebThirring

/-- A symmetric ordered pair sum is the sum of two equal upper-triangle sums. -/
theorem sum_off_diagonal_eq_sum_lt_add_sum_lt {A : Type*} [AddCommMonoid A]
    {N : ℕ} (f : Fin N → Fin N → A) (hf : ∀ i j, f i j = f j i) :
    (∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else f i j) =
      (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j) +
        ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j := by
  classical
  have hp (i j : Fin N) :
      (if i = j then (0 : A) else f i j) =
        (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp only [ite_eq_right h.ne, ite_eq_left h,
        ite_eq_right (not_lt_of_ge h.le), add_zero]
    · subst j
      simp only [ite_true, lt_self_iff_false, ite_false, add_zero]
    · simp only [ite_eq_right h.ne.symm, ite_eq_left h,
        ite_eq_right (not_lt_of_ge h.le), zero_add]
  simp_rw [hp, Finset.sum_add_distrib]
  congr 1
  · simp only [Finset.sum_filter]
  · rw [Finset.sum_comm]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hf j i]

/-- The pair repulsion is precisely one half of the ordered pair sum. -/
theorem electronRepulsion_eq_half_ordered_sum {N : ℕ} (X : Configuration N) :
    electronRepulsion X = (2 : ℝ≥0∞)⁻¹ *
      ∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else
        coulombKernel (particlePosition X i) (particlePosition X j) := by
  classical
  rw [sum_off_diagonal_eq_sum_lt_add_sum_lt _
    (fun i j => coulombKernel_symm (particlePosition X i) (particlePosition X j))]
  change electronRepulsion X = (2 : ℝ≥0∞)⁻¹ *
    (electronRepulsion X + electronRepulsion X)
  rw [← two_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num), one_mul]

end LiebThirring
end
