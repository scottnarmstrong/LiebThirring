/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterGram
public import LiebThirring.TFQuantum.SlaterMarginalsPermutations

/-! # One- and two-particle Slater contractions

Spectator integrations give Kronecker deltas. One unintegrated row leaves the
diagonal pairing; two distinct rows leave the direct and exchanged pairings
with opposite signs. Summing particle labels avoids permutation-fiber counts.
direct proof finite permutation algebra.
-/

public section
namespace LiebThirring

/-- The same one-body spectator contraction on the other-particle subtype. -/
theorem permutation_delta_product_other {N : ℕ} (σ τ : Equiv.Perm (Fin N))
    (i : Fin N) :
    (∏ j : {j : Fin N // j ≠ i}, if σ j = τ j then (1 : ℂ) else 0) =
      if σ = τ then 1 else 0 := by
  classical
  by_cases h : σ = τ
  · subst τ
    simp
  · rw [ite_eq_right h]
    have hex : ∃ j, j ≠ i ∧ σ j ≠ τ j := by
      by_contra hn
      apply h
      apply slater_perm_eq_of_eq_off_one σ τ i
      intro j hj
      by_contra he
      exact hn ⟨j, hj, he⟩
    obtain ⟨j, hj, he⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨j, hj⟩) (ite_eq_right he)

/-- The two possible spectator contractions for distinct particle rows. -/
theorem permutation_delta_product_erase_two {N : ℕ} (σ τ : Equiv.Perm (Fin N))
    (i k : Fin N) :
    (∏ j ∈ (Finset.univ.erase i).erase k, if σ j = τ j then (1 : ℂ) else 0) =
      if τ = σ ∨ τ = σ * Equiv.swap i k then 1 else 0 := by
  classical
  by_cases h : τ = σ ∨ τ = σ * Equiv.swap i k
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro j hj
    have hjk := (Finset.mem_erase.mp hj).1
    have hji := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    rcases h with h | h
    · subst τ
      simp
    · rw [h, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hji hjk]
      simp
  · rw [ite_eq_right h]
    have hex : ∃ j, j ≠ i ∧ j ≠ k ∧ σ j ≠ τ j := by
      by_contra hn
      apply h
      apply slater_perm_eq_or_mul_swap_of_eq_off_two σ τ i k
      intro j hji hjk
      by_contra he
      exact hn ⟨j, hji, hjk, he⟩
    obtain ⟨j, hji, hjk, he⟩ := hex
    exact Finset.prod_eq_zero
      (Finset.mem_erase.mpr ⟨hjk, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩⟩)
      (ite_eq_right he)

/-- A surviving exchanged pairing has the negative fermionic sign. -/
theorem permutationSignComplex_mul_swap {N : ℕ} (σ : Equiv.Perm (Fin N))
    (i k : Fin N) (hik : i ≠ k) :
    (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
      (((Equiv.Perm.sign (σ * Equiv.swap i k) : ℤˣ) : ℤ) : ℂ) = -1 := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hik]
  simp only [Units.val_neg, Int.cast_neg, mul_neg, mul_one, permutationSignComplex_mul_self]

/-- Two-body spectator contraction gives the direct term minus the exchanged term. -/
theorem sum_permutation_two_body_contraction {N : ℕ} (σ : Equiv.Perm (Fin N))
    (i k : Fin N) (hik : i ≠ k) (F : Equiv.Perm (Fin N) → ℂ) :
    (∑ τ : Equiv.Perm (Fin N),
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
        (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) *
        (∏ j ∈ (Finset.univ.erase i).erase k, if σ j = τ j then (1 : ℂ) else 0) * F τ) =
      F σ - F (σ * Equiv.swap i k) := by
  classical
  have hne : σ * Equiv.swap i k ≠ σ := by
    intro h
    have hi := congrArg (fun ρ : Equiv.Perm (Fin N) => ρ i) h
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at hi
    exact hik (σ.injective hi).symm
  have hc (τ : Equiv.Perm (Fin N)) :
      (∏ j ∈ (Finset.univ.erase i).erase k, if σ j = τ j then (1 : ℂ) else 0) =
        (if τ = σ then 1 else 0) + (if τ = σ * Equiv.swap i k then 1 else 0) := by
    rw [permutation_delta_product_erase_two]
    by_cases h₁ : τ = σ
    · subst τ
      simp [hne.symm]
    · by_cases h₂ : τ = σ * Equiv.swap i k <;> simp [h₁, h₂, hik]
  simp_rw [hc, mul_add, add_mul]
  rw [Finset.sum_add_distrib]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, permutationSignComplex_mul_self,
    permutationSignComplex_mul_swap σ i k hik, one_mul, neg_one_mul, sub_eq_add_neg]

/-- Summing all particle labels removes permutation multiplicities in a one-body marginal. -/
theorem sum_permutation_sum_particle {N : ℕ} (f : Fin N → ℂ) :
    (∑ σ : Equiv.Perm (Fin N), ∑ i : Fin N, f (σ i)) =
      (N.factorial : ℂ) * ∑ j : Fin N, f j := by
  classical
  simp only [Equiv.sum_comp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_perm, Fintype.card_fin]

/-- The ordered two-body particle sum removes the same factorial multiplicity. -/
theorem sum_permutation_sum_particle_pair {N : ℕ} (f : Fin N → Fin N → ℂ) :
    (∑ σ : Equiv.Perm (Fin N), ∑ i : Fin N, ∑ k : Fin N,
      if i = k then 0 else f (σ i) (σ k)) =
      (N.factorial : ℂ) * ∑ j : Fin N, ∑ l : Fin N, if j = l then 0 else f j l := by
  classical
  have hs (σ : Equiv.Perm (Fin N)) :
      (∑ i : Fin N, ∑ k : Fin N, if i = k then (0 : ℂ) else f (σ i) (σ k)) =
        ∑ j : Fin N, ∑ l : Fin N, if j = l then 0 else f j l := by
    have hi (i : Fin N) :
        (∑ k : Fin N, if i = k then (0 : ℂ) else f (σ i) (σ k)) =
          ∑ l : Fin N, if σ i = l then 0 else f (σ i) l := by
      calc
        _ = ∑ k : Fin N, if σ i = σ k then (0 : ℂ) else f (σ i) (σ k) := by
          simp only [σ.injective.eq_iff]
        _ = _ := Equiv.sum_comp σ (fun l => if σ i = l then 0 else f (σ i) l)
    simp_rw [hi]
    exact Equiv.sum_comp σ (fun j => ∑ l : Fin N, if j = l then 0 else f j l)
  simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_perm, Fintype.card_fin]

end LiebThirring
end
