/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeNeumannForm
public import LiebThirring.TFProduct.ScalarEigenvalue

/-! # The physical scalar cube form used in particle tensorization -/

@[expose] public section
open MeasureTheory
open scoped InnerProductSpace BigOperators
namespace LiebThirring.TFProduct
open TFCubes

/-- The mixed scalar derivative basis gives directional Neumann Parseval. -/
theorem hasSum_scalarCube_direction (ℓ : {x : ℝ // 0 < x}) (b : Position)
    (a : Fin 3) {u g : RegionState Position ℂ (cubeInterior b ℓ)}
    (h : HasWeakDerivativeOn (cubeInterior b ℓ)
      (EuclideanSpace.basisFun (Fin 3) ℝ a) u g) :
    HasSum (fun k : Fin 3 → ℕ => intervalFrequency ℓ (k a) ^ 2 *
      ‖(neumannCubeScalarBasis ℓ b).repr u k‖ ^ 2) (‖g‖ ^ 2) := by
  have hs := hasSum_weighted_state_of_basis_embedding
    (neumannMixedCubeScalarBasis ℓ b a) (neumannCubeScalarBasis ℓ b)
    u g (fun k : NeumannMixedFrequencyIndex a => k.val) Subtype.val_injective
    (fun k => intervalFrequency ℓ (k a) ^ 2)
    (fun k hk => by
      have hz : k a = 0 := by
        by_contra hn
        exact hk ⟨⟨k, Nat.pos_of_ne_zero hn⟩, rfl⟩
      simp [hz, intervalFrequency])
    (fun k => by
      rw [neumannMixedCubeScalarBasis_eq_testLimit ℓ b a (k, (0 : Fin 1))]
      have hc := h.neumannCube_mixed_coeff ℓ b k.val a ⟨k.val a, k.property⟩
      change inner ℂ (neumannCubeMixedTestLimitL2 ℓ b k.val a
        ⟨k.val a, k.property⟩) g = -(intervalFrequency ℓ (k.val a) : ℂ) *
          inner ℂ (neumannCubeScalarBasis ℓ b
            (Function.update k.val a (k.val a))) u at hc
      rw [Function.update_eq_self] at hc
      rw [hc, norm_mul, norm_neg, mul_pow]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (intervalFrequency_nonneg ℓ _)])
  simpa only [HilbertBasis.repr_apply_apply] using hs

/-- Full scalar cube energy from the actual three weak derivatives. -/
theorem hasSum_scalarCube_form (ℓ : {x : ℝ // 0 < x}) (b : Position)
    (u : RegionState Position ℂ (cubeInterior b ℓ))
    (g : Fin 3 → RegionState Position ℂ (cubeInterior b ℓ))
    (h : ∀ a, HasWeakDerivativeOn (cubeInterior b ℓ)
      (EuclideanSpace.basisFun (Fin 3) ℝ a) u (g a)) :
    HasSum (fun k => scalarCubeEigenvalue ℓ k *
      ‖(neumannCubeScalarBasis ℓ b).repr u k‖ ^ 2)
      (∑ a : Fin 3, ‖g a‖ ^ 2) := by
  have hs := hasSum_cubeCoordinateEnergy
    (fun a k => intervalFrequency ℓ (k a) ^ 2 *
      ‖(neumannCubeScalarBasis ℓ b).repr u k‖ ^ 2) g
    (fun a => hasSum_scalarCube_direction ℓ b a (h a))
  apply hs.congr_fun
  intro k
  rw [← Finset.sum_mul, ← scalarCubeEigenvalue_eq_sum]

end LiebThirring.TFProduct
end
