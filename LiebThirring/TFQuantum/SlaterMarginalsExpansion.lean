/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterGram
public import LiebThirring.TFQuantum.SlaterProduct

/-! # The exact spin-summed mixed determinant expansion

The finite sums are rearranged pointwise, before making any assertion about
integrability. The orbitals are arbitrary one-particle states.
-/

public section
open scoped ComplexConjugate
namespace LiebThirring

/-- Spin-summed determinants expand into products of the actual orbital contractions. -/
theorem sum_slaterDeterminant_conj_mul {N q : ℕ} (u v : Fin N → State 1 q)
    (X : Configuration N) :
    (∑ s : SpinLabels N q, conj (slaterDeterminant u X s) * slaterDeterminant v X s) =
      ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
          (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) *
          ∏ i : Fin N, orbitalContraction (u (σ i)) (v (τ i)) (particlePosition X i) := by
  classical
  have he (s : SpinLabels N q) :
      conj (slaterDeterminant u X s) * slaterDeterminant v X s =
        ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
            (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) *
            ∏ i : Fin N, conj (orbitalValue (u (σ i)) (particlePosition X i) (s i)) *
              orbitalValue (v (τ i)) (particlePosition X i) (s i) :=
    det_conj_mul_det_eq_sum
      (Matrix.of fun i j => orbitalValue (u j) (particlePosition X i) (s i))
      (Matrix.of fun i j => orbitalValue (v j) (particlePosition X i) (s i))
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  rw [← Finset.mul_sum]
  congr 1
  exact sum_prod_orbital_eq_prod_contraction (u ∘ σ) (v ∘ τ) X

end LiebThirring
end
