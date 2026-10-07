/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.SpectralInput

/-! # From fermionic coefficient exclusion to a physical spectral lower bound -/

@[expose] public section
namespace LiebThirring.TFSectors
open TFCubes TFLattice

theorem hilbertBasis_hasSum_norm_sq {I E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (B : HilbertBasis I ℂ E) (u : E) :
    HasSum (fun k => ‖B.repr u k‖ ^ 2) (‖u‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] using
    lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (B.repr u)

/-- A lower diagonal weight on every nonzero coefficient gives the lower form bound. -/
theorem diagonal_lower_bound_of_coefficient_exclusion {I E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (B : HilbertBasis I ℂ E) (u : E)
    (eigenvalue : I → ℝ) (L T : ℝ) (admissible : I → Prop)
    (hzero : ∀ k, ¬admissible k → B.repr u k = 0)
    (hlower : ∀ k, admissible k → L ≤ eigenvalue k)
    (hdiag : HasSum (fun k => eigenvalue k * ‖B.repr u k‖ ^ 2) T) :
    L * ‖u‖ ^ 2 ≤ T := by
  apply hasSum_le _ ((hilbertBasis_hasSum_norm_sq B u).mul_left L) hdiag
  intro k
  by_cases hk : admissible k
  · exact mul_le_mul_of_nonneg_right (hlower k hk) (sq_nonneg _)
  · simp only [hzero k hk, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]

theorem localGradientEnergy_ge_occupationSum_of_diagonal_and_exclusion
    {N q : ℕ} (hq : 1 ≤ q) (ℓ : {x : ℝ // 0 < x}) (Cq : ℝ)
    (hsharp : ∀ s : Finset (ModeIndex q), IsFilled (fun _ => True) s →
      (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ ((5 : ℝ) / 3) -
        Cq * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ ((4 : ℝ) / 3) ≤
          ∑ p ∈ s, cubeEigenvalue ℓ p)
    (b : Fin N → LatticeIndex) (spec : NeumannProductSpectralData N q ℓ b)
    (v : localFormGraph N q (openAssignmentCell ℓ b))
    (hzero : ∀ k, ¬DistinctWithinCubes b k →
      spec.basis.repr ((v : LocalFormGraphAmbient N q (openAssignmentCell ℓ b)) none) k = 0) :
    (∑ β ∈ TFCoulomb.occupiedCubes b,
      ((tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 *
        (TFCoulomb.sectorCount b β : ℝ) ^ ((5 : ℝ) / 3) -
      Cq * ℓ.val⁻¹ ^ 2 * (TFCoulomb.sectorCount b β : ℝ) ^ ((4 : ℝ) / 3))) *
      ‖(v : LocalFormGraphAmbient N q (openAssignmentCell ℓ b)) none‖ ^ 2 ≤
        localGradientEnergy (v : LocalFormGraphAmbient N q (openAssignmentCell ℓ b)) :=
  diagonal_lower_bound_of_coefficient_exclusion spec.basis _ _ _ _ _ hzero
    (fun k hk => productEigenvalue_ge_occupationSum_of_filled_bound hq ℓ Cq hsharp b k hk)
    (spec.diagonal v)

end LiebThirring.TFSectors
end
