/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.LocalPartition

/-! # Normalization of the actual local weak-gradient energies -/

@[expose] public section
open LiebThirring.TFCubes LiebThirring.Sobolev
namespace LiebThirring.TFSectors

/-- Conditional kinetic expectation, with an explicit value on null sectors. -/
noncomputable def normalizedAssignmentGradientEnergy {N q : ℕ} (ℓ : ℝ)
    (v : formGraph N q) (F : (Fin N → LatticeIndex) → ℝ)
    (b : Fin N → LatticeIndex) : ℝ :=
  let p := sectorProbability ℓ ((v : FormGraphAmbient N q) none) b
  if p = 0 then F b else p⁻¹ * assignmentGradientEnergy ℓ v b

theorem weighted_normalizedAssignmentGradientEnergy {N q : ℕ} (ℓ : ℝ)
    (v : formGraph N q) (F : (Fin N → LatticeIndex) → ℝ)
    (hnull : ∀ b, sectorProbability ℓ ((v : FormGraphAmbient N q) none) b = 0 →
      assignmentGradientEnergy ℓ v b = 0) (b : Fin N → LatticeIndex) :
    sectorProbability ℓ ((v : FormGraphAmbient N q) none) b *
      normalizedAssignmentGradientEnergy ℓ v F b = assignmentGradientEnergy ℓ v b := by
  unfold normalizedAssignmentGradientEnergy
  dsimp only
  split
  next hp => simp [hp, hnull b hp]
  next hp => rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]

theorem hasSum_normalizedAssignmentGradientEnergy {N q : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (v : formGraph N q) (F : (Fin N → LatticeIndex) → ℝ)
    (hnull : ∀ b, sectorProbability ℓ ((v : FormGraphAmbient N q) none) b = 0 →
      assignmentGradientEnergy ℓ v b = 0) :
    HasSum (fun b => sectorProbability ℓ ((v : FormGraphAmbient N q) none) b *
      normalizedAssignmentGradientEnergy ℓ v F b)
      (kineticEnergy ((v : FormGraphAmbient N q) none)).toReal := by
  simp_rw [weighted_normalizedAssignmentGradientEnergy ℓ v F hnull]
  exact hasSum_assignmentGradientEnergy hℓ v

theorem le_normalizedAssignmentGradientEnergy {N q : ℕ} (ℓ : ℝ)
    (v : formGraph N q) (F : (Fin N → LatticeIndex) → ℝ)
    (hlocal : ∀ b, F b * sectorProbability ℓ ((v : FormGraphAmbient N q) none) b ≤
      assignmentGradientEnergy ℓ v b) (b : Fin N → LatticeIndex) :
    F b ≤ normalizedAssignmentGradientEnergy ℓ v F b := by
  unfold normalizedAssignmentGradientEnergy
  dsimp only
  split
  · exact le_rfl
  next hp =>
    have hpos := lt_of_le_of_ne (sectorProbability_nonneg ℓ _ b) (Ne.symm hp)
    rw [← div_eq_inv_mul, le_div_iff₀ hpos]
    exact hlocal b

end LiebThirring.TFSectors
end
