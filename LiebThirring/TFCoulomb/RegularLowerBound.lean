/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCoulomb.RegularDiscrete
public import LiebThirring.TFCoulomb.SectorPairs
public import LiebThirring.TFCoulomb.UniformComparison
public import LiebThirring.ThomasFermi.KineticConstant

/-!
# Conditional sector assembly for the regular-potential lower bound

This module isolates the final order-theoretic assembly in the regular-potential lower bound. Its
hypotheses are the named outputs still owed by the cube-form, lattice-counting,
and Neumann-sector developments: three sector decompositions, a sector kinetic
bound, an exact step-density attraction identity, and a sector repulsion bound.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LiebThirring.TFCoulomb

/-- Conditional regular-potential lower bound sector assembly. The index is the literal ordered cube
assignment. No convexity of the box interaction is assumed or used: the
whole sector energy is averaged before taking its infimum. -/
theorem regularScaledQuantumEnergy_ge_discreteTFInfimum_of_sector_bounds
    {N q M : ℕ} (hq : 1 ≤ q) {α δ t ν ℓ Cq : ℝ}
    (hα : 0 < α) (hℓ : 0 < ℓ)
    (hN : (N : ℝ) = α * ν)
    (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ψ : FormDomain N q) (_hnorm : ‖(ψ : State N q)‖ = 1)
    (p : (Fin N → LatticeIndex) → ℝ)
    (sectorKinetic sectorAttraction sectorRepulsion : (Fin N → LatticeIndex) → ℝ)
    (stepDensity : (Fin N → LatticeIndex) → TFDensity)
    (sectorMeasure : (Fin N → LatticeIndex) → Measure (Configuration N))
    (hprobability : ∀ b, IsProbabilityMeasure (sectorMeasure b))
    (hp_nonneg : ∀ b, 0 ≤ p b) (hp_sum : HasSum p 1)
    (hkinetic_decomp : HasSum (fun b ↦ p b * sectorKinetic b)
      (α ^ (-(5 : ℝ) / 3) * t * (kineticEnergy (ψ : State N q)).toReal))
    (hattraction_decomp : HasSum (fun b ↦ p b * sectorAttraction b)
      (α⁻¹ * cappedAttractionExpectation δ z R ψ))
    (hrepulsion_decomp : HasSum (fun b ↦ p b * sectorRepulsion b)
      (α⁻¹ ^ 2 * repulsionExpectation ψ))
    (hmass : ∀ b, tfMass (stepDensity b) = ν)
    (hkinetic : ∀ b,
      t * (tfKineticConstant ⟨q, hq⟩).val * (∫ x : Position,
        ((stepDensity b).val x) ^ ((5 : ℝ) / 3)) -
          t * Cq * ℓ⁻¹ ^ 2 * α ^ (-(1 : ℝ) / 3) * ν ^ ((4 : ℝ) / 3) ≤
        sectorKinetic b)
    (hattraction : ∀ b, sectorAttraction b ≤
      ∫ x : Position, boxCappedPotential δ ℓ z R x * (stepDensity b).val x)
    (hsector_support : ∀ b, ∀ᵐ x ∂sectorMeasure b,
      ∀ i, particlePosition x i ∈ latticeClosedCell ℓ (b i))
    (hsector_repulsion_finite : ∀ b,
      (∫⁻ x, electronRepulsion x ∂sectorMeasure b) ≠ ⊤)
    (hrepulsion_decomp_sector : ∀ b, sectorRepulsion b =
      α⁻¹ ^ 2 * (∫⁻ x, electronRepulsion x ∂sectorMeasure b).toReal)
    (hstep_box : ∀ b, tfBoxCoulombEnergy ℓ (stepDensity b) =
      α⁻¹ ^ 2 * sectorDirectEnergy ℓ b)
    (hbounded : BddBelow (regularDiscreteTFValues
      (t * (tfKineticConstant ⟨q, hq⟩).val) ν δ ℓ z R)) :
    regularDiscreteTFInfimum (t * (tfKineticConstant ⟨q, hq⟩).val) ν δ ℓ z R -
        t * Cq * ℓ⁻¹ ^ 2 * α ^ (-(1 : ℝ) / 3) * ν ^ ((4 : ℝ) / 3) -
        ν / (2 * Real.sqrt 3 * α * ℓ) ≤
      regularScaledQuantumEnergy α δ t z R ψ := by
  let I := Fin N → LatticeIndex
  let kineticError := t * Cq * ℓ⁻¹ ^ 2 * α ^ (-(1 : ℝ) / 3) * ν ^ ((4 : ℝ) / 3)
  let selfError := ν / (2 * Real.sqrt 3 * α * ℓ)
  let a := t * (tfKineticConstant ⟨q, hq⟩).val
  let L := regularDiscreteTFInfimum a ν δ ℓ z R - kineticError - selfError
  have hrepulsion (b : I) :
      tfBoxCoulombEnergy ℓ (stepDensity b) - selfError ≤ sectorRepulsion b := by
    let _ : IsProbabilityMeasure (sectorMeasure b) := hprobability b
    have hd := sectorDirectEnergy_le_repulsion_integral_add hℓ b (sectorMeasure b)
      (hsector_support b) (hsector_repulsion_finite b)
    have hs : α⁻¹ ^ 2 * ((N : ℝ) / (2 * Real.sqrt 3 * ℓ)) = selfError := by
      dsimp only [selfError]
      rw [hN]
      field_simp
    rw [hstep_box b, hrepulsion_decomp_sector b, ← hs]
    linarith only [mul_le_mul_of_nonneg_left hd (sq_nonneg α⁻¹)]
  have hsector (b : I) : L ≤ sectorKinetic b - sectorAttraction b + sectorRepulsion b := by
    have hin : regularDiscreteTFInfimum a ν δ ℓ z R ≤
        regularDiscreteTFFunctional a δ ℓ z R (stepDensity b) := by
      apply csInf_le hbounded
      exact ⟨stepDensity b, hmass b, rfl⟩
    dsimp only [L, a, kineticError, selfError]
    unfold regularDiscreteTFFunctional at hin
    linarith only [hin, hkinetic b, hattraction b, hrepulsion b]
  have hcombined : HasSum
      (fun b : I ↦ p b * (sectorKinetic b - sectorAttraction b + sectorRepulsion b))
      (regularScaledQuantumEnergy α δ t z R ψ) := by
    have h := (hkinetic_decomp.sub hattraction_decomp).add hrepulsion_decomp
    simpa only [regularScaledQuantumEnergy, mul_sub, mul_add, sub_add_eq_add_sub,
      add_sub_assoc, add_comm, add_left_comm, add_assoc] using h
  have hlower : HasSum (fun b : I ↦ p b * L) L := by
    simpa only [mul_comm, one_mul] using hp_sum.mul_left L
  change L ≤ regularScaledQuantumEnergy α δ t z R ψ
  rw [← hlower.tsum_eq, ← hcombined.tsum_eq]
  exact Summable.tsum_le_tsum
    (fun b ↦ mul_le_mul_of_nonneg_left (hsector b) (hp_nonneg b))
    hlower.summable hcombined.summable

end LiebThirring.TFCoulomb

end
