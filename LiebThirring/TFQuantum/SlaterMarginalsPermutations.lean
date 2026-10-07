/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.GroupTheory.Perm.Sign

/-! # Surviving permutation contractions in Slater marginals

Integrating all but one particle forces equal permutations. Integrating all but
two particles leaves the equal and exchanged pairings.
-/

public section
namespace LiebThirring
variable {α : Type*} [DecidableEq α]

/-- Permutations agreeing away from a single coordinate agree everywhere. -/
theorem slater_perm_eq_of_eq_off_one (σ τ : Equiv.Perm α) (i : α)
    (h : ∀ j, j ≠ i → σ j = τ j) : σ = τ := by
  ext j
  by_cases hj : j = i
  · subst j
    let k := τ.symm (σ i)
    have hk : τ k = σ i := τ.apply_symm_apply _
    by_cases hki : k = i
    · rw [hki] at hk
      exact hk.symm
    · have hsk : σ k = σ i := (h k hki).trans hk
      exact (hki (σ.injective hsk)).elim
  · exact h j hj

/-- A permutation fixing every coordinate except two is identity or their swap. -/
theorem slater_perm_eq_one_or_swap (σ : Equiv.Perm α) (i k : α)
    (h : ∀ j, j ≠ i → j ≠ k → σ j = j) :
    σ = 1 ∨ σ = Equiv.swap i k := by
  by_cases hik : i = k
  · subst k
    left
    exact slater_perm_eq_of_eq_off_one σ 1 i (fun j hj => h j hj hj)
  have hi : σ i = i ∨ σ i = k := by
    by_contra hh
    push Not at hh
    have he := h (σ i) hh.1 hh.2
    exact hh.1 (σ.injective he)
  rcases hi with hi | hi
  · left
    apply slater_perm_eq_of_eq_off_one σ 1 k
    intro j hj
    by_cases hji : j = i
    · subst j
      exact hi
    · exact h j hji hj
  · right
    have hk : σ k = i := by
      by_contra hki
      have hkk : σ k ≠ k := fun he => hik (σ.injective (hi.trans he.symm))
      have he := h (σ k) hki hkk
      exact hkk (σ.injective he)
    ext j
    by_cases hji : j = i
    · subst j
      simpa only [Equiv.swap_apply_left] using hi
    by_cases hjk : j = k
    · subst j
      simpa only [Equiv.swap_apply_right] using hk
    rw [h j hji hjk, Equiv.swap_apply_of_ne_of_ne hji hjk]

/-- The two surviving pairings in a two-particle determinant contraction. -/
theorem slater_perm_eq_or_mul_swap_of_eq_off_two (σ τ : Equiv.Perm α) (i k : α)
    (h : ∀ j, j ≠ i → j ≠ k → σ j = τ j) :
    τ = σ ∨ τ = σ * Equiv.swap i k := by
  have he : ∀ j, j ≠ i → j ≠ k → (σ.symm * τ) j = j := by
    intro j hji hjk
    change σ.symm (τ j) = j
    rw [← h j hji hjk, σ.symm_apply_apply]
  rcases slater_perm_eq_one_or_swap (σ.symm * τ) i k he with he | he
  · left
    ext j
    have hf := congrArg (fun ρ : Equiv.Perm α => σ (ρ j)) he
    change σ (σ.symm (τ j)) = σ j at hf
    simpa only [σ.apply_symm_apply] using hf
  · right
    ext j
    have hf := congrArg (fun ρ : Equiv.Perm α => σ (ρ j)) he
    change σ (σ.symm (τ j)) = σ ((Equiv.swap i k) j) at hf
    simpa only [σ.apply_symm_apply, Equiv.Perm.mul_apply] using hf

end LiebThirring
end
