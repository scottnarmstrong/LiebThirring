/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterContractions
public import LiebThirring.TFQuantum.SlaterMarginals
public import LiebThirring.TFQuantum.SlaterProduct

/-! # Occupied-orbital trace and Slater normalization factor

The diagonal spin contraction is the actual occupied density. The inverse
square-root factorial cancels the number of surviving permutations, including
the empty determinant. Proof: Slater determinant identities, direct proof finite algebra.
-/

public section
open scoped ComplexConjugate
namespace LiebThirring

/-- The squared conventional Slater normalization cancels `N!`. -/
theorem slater_normalization_factor_mul_factorial (N : ℕ) :
    ((Real.sqrt N.factorial : ℂ)⁻¹ ^ 2) * (N.factorial : ℂ) = 1 := by
  have hs : (Real.sqrt N.factorial : ℂ)^2 = (N.factorial : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ N.factorial from Nat.cast_nonneg _)
  rw [inv_pow, hs, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr N.factorial_ne_zero)]

/-- A one-orbital diagonal contraction is its spin-summed norm squared. -/
theorem orbitalContraction_self_eq_sum {q : ℕ} (u : State 1 q) (x : Position) :
    orbitalContraction u u x = ((∑ s : Fin q, ‖orbitalValue u x s‖ ^ 2 : ℝ) : ℂ) := by
  simp only [orbitalContraction, Complex.conj_mul', Complex.ofReal_sum, Complex.ofReal_pow]

/-- Summing the occupied trace gives precisely the stated orbital density. -/
theorem sum_orbitalContraction_self_eq_density {N q : ℕ} (u : Fin N → State 1 q)
    (x : Position) :
    (∑ j : Fin N, orbitalContraction (u j) (u j) x) = (slaterOrbitalDensity u x : ℂ) := by
  simp only [orbitalContraction_self_eq_sum, slaterOrbitalDensity, Complex.ofReal_sum]
  exact Finset.sum_comm

/-- Exact one-body spectator contraction for orthonormal orbitals. -/
theorem sum_orthonormal_one_body_spectator {N q : ℕ} (u : Fin N → State 1 q)
    (hu : Orthonormal ℂ u) (σ : Equiv.Perm (Fin N)) (i : Fin N) (x : Position) :
    (∑ τ : Equiv.Perm (Fin N),
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
        (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) *
        (orbitalContraction (u (σ i)) (u (τ i)) x *
          ∏ j : {j : Fin N // j ≠ i}, inner ℂ (u (σ j)) (u (τ j)))) =
      orbitalContraction (u (σ i)) (u (σ i)) x := by
  classical
  simp only [orthonormal_iff_ite.mp hu, permutation_delta_product_other,
    mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [permutationSignComplex_mul_self, one_mul]

end LiebThirring
end
