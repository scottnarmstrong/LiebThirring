/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.SpectralLowerBound
public import LiebThirring.TFSectors.CoefficientExclusion
public import LiebThirring.TFSectors.NullSectorGradient
public import LiebThirring.TFSectors.InteriorTransport
public import LiebThirring.TFSectors.NormalizedKinetic
public import LiebThirring.TFSectors.KineticScaling
public import LiebThirring.TFSectors.AttractionBound
public import LiebThirring.TFSectors.ReferenceConfiguration
public import LiebThirring.TFSectors.StepBoxEnergy
public import LiebThirring.TFCoulomb.RegularLowerBound
import LiebThirring.TFCoulomb.InfimumComparison

/-!
# Neumann sector estimates and regular-potential lower bounds from spectral inputs

The only conditional mathematical inputs are the literal product-cube Neumann
basis/form identity and the sharp eigenvalue sums filled-set sharp eigenvalue sum. The sector
partition, all conditional expectations, Pauli exclusion, occupation sums and
step-density identities are supplied by the implementation.
-/

@[expose] public section
open MeasureTheory
open scoped NNReal
open LiebThirring.TFCubes LiebThirring.Sobolev LiebThirring.TFLattice
namespace LiebThirring.TFSectors

theorem assignmentGradientEnergy_ge_occupationKineticLower_of_neumann_data
    {N q : ℕ} (hq : 1 ≤ q) (ℓ : {x : ℝ // 0 < x}) (Cq : ℝ)
    (hsharp : ∀ s : Finset (ModeIndex q), IsFilled (fun _ => True) s →
      (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ ((5 : ℝ) / 3) -
        Cq * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ ((4 : ℝ) / 3) ≤
          ∑ p ∈ s, cubeEigenvalue ℓ p)
    (v : formGraph N q) (hanti : antisymmetric ((v : FormGraphAmbient N q) none))
    (b : Fin N → LatticeIndex) (spec : NeumannProductSpectralData N q ℓ b) :
    occupationKineticLower (tfKineticConstant ⟨q, hq⟩).val Cq ℓ.val b *
      sectorProbability ℓ.val ((v : FormGraphAmbient N q) none) b ≤
        assignmentGradientEnergy ℓ.val v b := by
  rw [sectorProbability_eq_norm_sq_openRestriction,
    ← localGradientEnergy_openAssignmentRestriction_eq]
  exact localGradientEnergy_ge_occupationSum_of_diagonal_and_exclusion hq ℓ Cq hsharp b spec
    (restrictFormGraph (openAssignmentCell ℓ.val b) v)
    (fun k hk => neumannProductBasis_repr_eq_zero_of_not_distinctWithinCubes
      ((v : FormGraphAmbient N q) none) hanti ℓ b spec k hk)

/-- Regular-potential lower bound conditional on the product-cube spectral identities
and sharp lattice eigenvalue sums. -/
theorem regularScaledQuantumEnergy_ge_discreteTFInfimum_of_neumann_data
    {N q M : ℕ} (hq : 1 ≤ q) (α ℓ : {x : ℝ // 0 < x})
    {δ t ν Cq : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) (hCq : 0 ≤ Cq)
    (hN : (N : ℝ) = α.val * ν)
    (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ψ : FormDomain N q) (hnorm : ‖(ψ : State N q)‖ = 1)
    (spectral : ∀ b : Fin N → LatticeIndex, NeumannProductSpectralData N q ℓ b)
    (hsharp : ∀ s : Finset (ModeIndex q), IsFilled (fun _ => True) s →
      (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ ((5 : ℝ) / 3) -
        Cq * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ ((4 : ℝ) / 3) ≤
          ∑ p ∈ s, cubeEigenvalue ℓ p) :
    TFCoulomb.regularDiscreteTFInfimum (t * (tfKineticConstant ⟨q, hq⟩).val)
        ν δ ℓ.val z R -
      t * Cq * ℓ.val⁻¹ ^ 2 * α.val ^ (-(1 : ℝ) / 3) * ν ^ ((4 : ℝ) / 3) -
      ν / (2 * Real.sqrt 3 * α.val * ℓ.val) ≤
        TFCoulomb.regularScaledQuantumEnergy α.val δ t z R ψ := by
  obtain ⟨g, hg⟩ := (kineticEnergy_lt_top_iff_exists_weakDerivatives (ψ : State N q)).mp ψ.property.2
  let v : formGraph N q := ⟨WithLp.toLp 2 (fun i => i.elim (ψ : State N q) g), fun a => hg a⟩
  have hv : (v : FormGraphAmbient N q) none = (ψ : State N q) := rfl
  let F : (Fin N → LatticeIndex) → ℝ :=
    occupationKineticLower (tfKineticConstant ⟨q, hq⟩).val Cq ℓ.val
  let p := sectorProbability ℓ.val (ψ : State N q)
  let kin := fun b => α.val ^ (-(5 : ℝ) / 3) * t * normalizedAssignmentGradientEnergy ℓ.val v F b
  let σ := referenceSectorMeasure (N := N) ℓ.val
  have hnull := fun b => assignmentGradientEnergy_eq_zero_of_sectorProbability_eq_zero ℓ.val v b
  have hlocal := fun b => assignmentGradientEnergy_ge_occupationKineticLower_of_neumann_data
    hq ℓ Cq hsharp v ψ.property.1 b (spectral b)
  have hdecomp : HasSum (fun b => p b * kin b)
      (α.val ^ (-(5 : ℝ) / 3) * t * (kineticEnergy (ψ : State N q)).toReal) := by
    have h := (hasSum_normalizedAssignmentGradientEnergy ℓ.property v F hnull).mul_left
      (α.val ^ (-(5 : ℝ) / 3) * t)
    simpa only [hv, p, kin, mul_left_comm] using h
  have hkin : ∀ b,
      t * (tfKineticConstant ⟨q, hq⟩).val *
        (∫ x : Position, ((sectorStepDensity α ℓ b).val x) ^ ((5 : ℝ) / 3)) -
      t * Cq * ℓ.val⁻¹ ^ 2 * α.val ^ (-(1 : ℝ) / 3) * ν ^ ((4 : ℝ) / 3) ≤ kin b := by
    intro b
    exact (scaled_occupationKineticLower_ge_stepKinetic_sub_error α ℓ _ ht hCq ν hN b).trans
      (mul_le_mul_of_nonneg_left (le_normalizedAssignmentGradientEnergy ℓ.val v F hlocal b)
        (mul_nonneg (Real.rpow_nonneg α.property.le _) ht))
  apply TFCoulomb.regularScaledQuantumEnergy_ge_discreteTFInfimum_of_sector_bounds
    hq α.property ℓ.property hN z R ψ hnorm p kin
    (sectorAttraction α.val δ ℓ.val z R ψ σ) (sectorRepulsion α.val ℓ.val ψ σ)
    (sectorStepDensity α ℓ) (sectorMeasure ℓ.val (ψ : State N q) σ)
    (fun b => isProbabilityMeasure_sectorMeasure ℓ.val _ σ (fun _ => inferInstance) b)
    (sectorProbability_nonneg ℓ.val _) (hasSum_sectorProbability ℓ.property _ hnorm)
    hdecomp (hasSum_sectorAttraction hδ ℓ.property α.val z R ψ σ)
    (hasSum_sectorRepulsion ℓ.property α.val ψ σ)
    (tfMass_sectorStepDensity_eq α ℓ ν hN) hkin
  · intro b
    rw [integral_boxCappedPotential_mul_sectorStepDensity α ℓ hδ z R b]
    exact sectorAttraction_le_cubeSum α.property hδ ℓ.property.le z R ψ σ
      (fun _ => inferInstance) (referenceSectorMeasure_ae_mem_closedCell ℓ.property) b
  · exact ae_sectorMeasure_closedCell ℓ.val _ σ
      (referenceSectorMeasure_ae_mem_closedCell ℓ.property)
  · exact lintegral_sectorRepulsion_ne_top ℓ.val ψ σ
      (lintegral_electronRepulsion_referenceSectorMeasure_ne_top ℓ.property)
  · exact fun _ => rfl
  · exact tfBoxCoulombEnergy_sectorStepDensity α ℓ
  · exact TFCoulomb.regularDiscreteTFValues_bddBelow
      (mul_nonneg ht (tfKineticConstant ⟨q, hq⟩).property.le) hδ ℓ.property z R

end LiebThirring.TFSectors
end
