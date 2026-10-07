/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.StepDensity
public import LiebThirring.TFSectors.OccupationConvexity

/-! # The uniform Neumann occupation error in TF scaling -/

@[expose] public section
open MeasureTheory
namespace LiebThirring.TFSectors

noncomputable def occupationKineticLower {N : ℕ} (K Cq ℓ : ℝ)
    (b : Fin N → LatticeIndex) : ℝ :=
  ∑ β ∈ TFCoulomb.occupiedCubes b,
    (K * ℓ⁻¹ ^ 2 * (TFCoulomb.sectorCount b β : ℝ) ^ ((5 : ℝ) / 3) -
      Cq * ℓ⁻¹ ^ 2 * (TFCoulomb.sectorCount b β : ℝ) ^ ((4 : ℝ) / 3))

theorem occupationKineticLower_ge_uniform {N : ℕ} (K ℓ : ℝ) {Cq : ℝ}
    (hCq : 0 ≤ Cq) (b : Fin N → LatticeIndex) :
    K * ℓ⁻¹ ^ 2 * (∑ β ∈ TFCoulomb.occupiedCubes b,
      (TFCoulomb.sectorCount b β : ℝ) ^ ((5 : ℝ) / 3)) -
        Cq * ℓ⁻¹ ^ 2 * (N : ℝ) ^ ((4 : ℝ) / 3) ≤ occupationKineticLower K Cq ℓ b := by
  unfold occupationKineticLower
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left
    (sum_sectorCount_rpow_four_thirds_le b) (mul_nonneg hCq (sq_nonneg _))) _

theorem scaled_particle_error_identity {N : ℕ} (α : {x : ℝ // 0 < x})
    (ν : ℝ) (hN : (N : ℝ) = α.val * ν) :
    α.val ^ (-(5 : ℝ) / 3) * (N : ℝ) ^ ((4 : ℝ) / 3) =
      α.val ^ (-(1 : ℝ) / 3) * ν ^ ((4 : ℝ) / 3) := by
  have hν : 0 ≤ ν := nonneg_of_mul_nonneg_right (hN ▸ Nat.cast_nonneg N) α.property
  rw [hN, Real.mul_rpow α.property.le hν, ← mul_assoc, ← Real.rpow_add α.property]
  norm_num

theorem scaled_occupationKineticLower_ge_stepKinetic_sub_error {N : ℕ}
    (α ℓ : {x : ℝ // 0 < x}) (K : ℝ) {t Cq : ℝ} (ht : 0 ≤ t) (hCq : 0 ≤ Cq)
    (ν : ℝ) (hN : (N : ℝ) = α.val * ν) (b : Fin N → LatticeIndex) :
    t * K * (∫ x : Position, ((sectorStepDensity α ℓ b).val x) ^ ((5 : ℝ) / 3)) -
      t * Cq * ℓ.val⁻¹ ^ 2 * α.val ^ (-(1 : ℝ) / 3) * ν ^ ((4 : ℝ) / 3) ≤
        α.val ^ (-(5 : ℝ) / 3) * t * occupationKineticLower K Cq ℓ b := by
  have h := mul_le_mul_of_nonneg_left (occupationKineticLower_ge_uniform K ℓ.val hCq b)
    (mul_nonneg (Real.rpow_nonneg α.property.le (-(5 : ℝ) / 3)) ht)
  rw [mul_sub] at h
  rw [integral_sectorStepDensity_rpow]
  have he := scaled_particle_error_identity α ν hN
  calc
    _ = (α.val ^ (-(5 : ℝ) / 3) * t) *
        (K * ℓ.val⁻¹ ^ 2 * ∑ β ∈ TFCoulomb.occupiedCubes b,
          (TFCoulomb.sectorCount b β : ℝ) ^ ((5 : ℝ) / 3)) -
        (t * Cq * ℓ.val⁻¹ ^ 2) *
          (α.val ^ (-(5 : ℝ) / 3) * (N : ℝ) ^ ((4 : ℝ) / 3)) := by rw [he]; ring
    _ ≤ _ := by convert h using 1; ring

end LiebThirring.TFSectors
end
