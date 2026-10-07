/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.StepDensity

/-! # Exact box energy of an occupation step density -/

public section

open scoped ENNReal BigOperators

namespace LiebThirring.TFSectors

theorem sectorCount_eq_zero_of_not_mem_occupiedCubes {N : ℕ}
    (b : Fin N → LatticeIndex) {β : LatticeIndex}
    (hβ : β ∉ TFCoulomb.occupiedCubes b) : TFCoulomb.sectorCount b β = 0 := by
  unfold TFCoulomb.sectorCount
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro i _ hi
  exact hβ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)

/-- The box Coulomb energy scales exactly as the direct occupation energy. -/
theorem tfBoxCoulombEnergy_sectorStepDensity {N : ℕ}
    (α ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex) :
    TFCoulomb.tfBoxCoulombEnergy ℓ (sectorStepDensity α ℓ b) =
      α.val⁻¹ ^ 2 * TFCoulomb.sectorDirectEnergy ℓ b := by
  unfold TFCoulomb.tfBoxCoulombEnergy TFCoulomb.boxCoulombEnergy
  let μ := tfDensityMeasure (sectorStepDensity α ℓ b)
  have hμ (β : LatticeIndex) : μ (latticeCell ℓ β) =
      ENNReal.ofReal ((TFCoulomb.sectorCount b β : ℝ) / α) :=
    tfDensityMeasure_sectorStepDensity_latticeCell α ℓ b β
  have hinner (β : LatticeIndex) :
      (∑' γ : LatticeIndex, ENNReal.ofReal (TFCoulomb.cubeWeight ℓ β γ) *
        μ (latticeCell ℓ β) * μ (latticeCell ℓ γ)) =
      ∑ γ ∈ TFCoulomb.occupiedCubes b,
        ENNReal.ofReal (TFCoulomb.cubeWeight ℓ β γ) *
          μ (latticeCell ℓ β) * μ (latticeCell ℓ γ) := by
    apply tsum_eq_sum
    intro γ hγ
    have hc := sectorCount_eq_zero_of_not_mem_occupiedCubes b hγ
    rw [hμ γ, hc]
    simp
  have houter :
      (∑' β : LatticeIndex, ∑' γ : LatticeIndex,
        ENNReal.ofReal (TFCoulomb.cubeWeight ℓ β γ) *
          μ (latticeCell ℓ β) * μ (latticeCell ℓ γ)) =
      ∑ β ∈ TFCoulomb.occupiedCubes b, ∑' γ : LatticeIndex,
        ENNReal.ofReal (TFCoulomb.cubeWeight ℓ β γ) *
          μ (latticeCell ℓ β) * μ (latticeCell ℓ γ) := by
    apply tsum_eq_sum
    intro β hβ
    have hc := sectorCount_eq_zero_of_not_mem_occupiedCubes b hβ
    simp only [hμ β, hc, Nat.cast_zero, zero_div, ENNReal.ofReal_zero,
      mul_zero, zero_mul, tsum_zero]
  change ((∑' β : LatticeIndex, ∑' γ : LatticeIndex,
    ENNReal.ofReal (TFCoulomb.cubeWeight ℓ β γ) *
      μ (latticeCell ℓ β) * μ (latticeCell ℓ γ)) / 2).toReal = _
  rw [houter]
  simp_rw [hinner]
  simp_rw [hμ]
  rw [ENNReal.toReal_div]
  have hfinite (β γ : LatticeIndex) :
      ENNReal.ofReal (TFCoulomb.cubeWeight ℓ β γ) *
        ENNReal.ofReal ((TFCoulomb.sectorCount b β : ℝ) / α) *
        ENNReal.ofReal ((TFCoulomb.sectorCount b γ : ℝ) / α) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_sum (fun β _ => ENNReal.sum_ne_top.mpr (fun γ _ => hfinite β γ))]
  have hrow (β : LatticeIndex) :
      (∑ γ ∈ TFCoulomb.occupiedCubes b,
        ENNReal.ofReal (TFCoulomb.cubeWeight ℓ β γ) *
          ENNReal.ofReal ((TFCoulomb.sectorCount b β : ℝ) / α) *
          ENNReal.ofReal ((TFCoulomb.sectorCount b γ : ℝ) / α)).toReal =
      ∑ γ ∈ TFCoulomb.occupiedCubes b, TFCoulomb.cubeWeight ℓ β γ *
        ((TFCoulomb.sectorCount b β : ℝ) / α) * ((TFCoulomb.sectorCount b γ : ℝ) / α) := by
    rw [ENNReal.toReal_sum (fun γ _ => hfinite β γ)]
    simp only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (TFCoulomb.cubeWeight_pos ℓ.property _ _).le,
      ENNReal.toReal_ofReal (div_nonneg (Nat.cast_nonneg _) α.property.le)]
  simp_rw [hrow]
  norm_num only [ENNReal.toReal_ofNat]
  unfold TFCoulomb.sectorDirectEnergy
  rw [← mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  simp only [div_eq_mul_inv]
  ring

end LiebThirring.TFSectors

end
