/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterBasic

/-! # The finite determinant contractions for Slater normalization

Column permutation expansion keeps particle rows fixed. The complex double
expansion contracts to `N!` when the one-particle inner products are Kronecker
deltas. These identities include the empty determinant convention.
Lieb–Simon (1977) III.11, (60), p. 66; direct proof finite algebra.
-/

public section
open scoped ComplexConjugate
namespace LiebThirring

/-- Column-permutation expansion, matching the occupied-orbital convention. -/
theorem det_eq_sum_permutation_columns {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    A.det = ∑ σ : Equiv.Perm (Fin N),
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ∏ i, A i (σ i) := by
  classical
  calc
    A.det = A.transpose.det := (Matrix.det_transpose A).symm
    _ = _ := Matrix.det_apply' A.transpose

/-- Exact finite contraction expansion of two complex determinants. -/
theorem det_conj_mul_det_eq_sum {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) :
    conj A.det * B.det =
      ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
        (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) *
        ∏ i, conj (A i (σ i)) * B i (τ i) := by
  classical
  rw [det_eq_sum_permutation_columns, det_eq_sum_permutation_columns, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  rw [map_mul, map_prod, map_intCast, Finset.prod_mul_distrib]
  ring

/-- The exact actual Slater determinant in occupied-orbital permutation form. -/
theorem slaterDeterminant_eq_sum {N q : ℕ} (u : Fin N → State 1 q)
    (x : Configuration N) (s : SpinLabels N q) :
    slaterDeterminant u x s = ∑ σ : Equiv.Perm (Fin N),
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
      ∏ i, orbitalValue (u (σ i)) (particlePosition x i) (s i) :=
  det_eq_sum_permutation_columns _

/-- A product of permutation Kronecker deltas is precisely equality of the permutations. -/
theorem permutation_delta_product {N : ℕ} (σ τ : Equiv.Perm (Fin N)) :
    (∏ i, if σ i = τ i then (1 : ℂ) else 0) = if σ = τ then 1 else 0 := by
  classical
  by_cases h : σ = τ
  · subst τ
    simp
  · rw [ite_eq_right h]
    have hex : ∃ i, σ i ≠ τ i := by
      by_contra hn
      apply h
      exact Equiv.ext (by simpa only [not_exists, not_not] using hn)
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- A real fermionic sign has complex square one. -/
theorem permutationSignComplex_mul_self {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]

/-- Orthonormal contractions leave exactly one unit term per permutation, hence `N!`. -/
theorem sum_permutation_delta_products (N : ℕ) :
    (∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
      (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) *
      ∏ i, if σ i = τ i then (1 : ℂ) else 0) = (N.factorial : ℂ) := by
  classical
  simp only [permutation_delta_product, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, permutationSignComplex_mul_self,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_perm, Fintype.card_fin]

end LiebThirring
end
