/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.SectorLowerBound
public import LiebThirring.TFCoulomb.InfimumComparison
public import LiebThirring.TFCoulomb.ScalingErrors

/-! # Asymptotic regular-potential lower bound from cube spectral data and sharp eigenvalue sums -/

@[expose] public section
open MeasureTheory Filter
open scoped NNReal
open LiebThirring.TFLattice
namespace LiebThirring.TFSectors

/-- The mesh and charge threshold are uniform in the actual normalized quantum
state. Every Neumann sector estimate sector premise has been eliminated. -/
theorem regularScaledQuantumEnergy_eventually_ge_of_neumann_data
    {q M : ℕ} (hq : 1 ≤ q) {δ t Cq : ℝ} (hδ : 0 < δ) (ht : 0 < t) (hCq : 0 ≤ Cq)
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (spectral : ∀ (N : ℕ) (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex),
      NeumannProductSpectralData N q ℓ b)
    (hsharp : ∀ (ℓ : {x : ℝ // 0 < x}) (s : Finset (ModeIndex q)),
      IsFilled (fun _ => True) s →
      (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ ((5 : ℝ) / 3) -
        Cq * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ ((4 : ℝ) / 3) ≤
          ∑ p ∈ s, cubeEigenvalue ℓ p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ A > 0, ∀ (α : ℝ), A < α → ∀ (N : ℕ),
      (N : ℝ) = α * (ν : ℝ) → ∀ (ψ : FormDomain N q),
      ‖(ψ : State N q)‖ = 1 →
      TFCoulomb.regularTFInfimum (t * (tfKineticConstant ⟨q, hq⟩).val) (ν : ℝ) δ z R - ε ≤
        TFCoulomb.regularScaledQuantumEnergy α δ t z R ψ := by
  let a := t * (tfKineticConstant ⟨q, hq⟩).val
  have ha : 0 < a := mul_pos ht (tfKineticConstant ⟨q, hq⟩).property
  obtain ⟨η, hη, hinf⟩ := TFCoulomb.regularTFInfimum_le_discrete_add ha hδ ν z R
    (ε / 2) (half_pos hε)
  let ℓ := η / 2
  have hℓ : 0 < ℓ := half_pos hη
  have hmesh : ℓ < η := half_lt_self hη
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    (TFCoulomb.eventually_abs_scalingError_lt t Cq (ν : ℝ) hℓ (half_pos hε))
  refine ⟨ℓ, hℓ, max A 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro α hαA N hN ψ hnorm
  have hα : 0 < α := lt_trans (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hαA
  have herr := hA α ((le_max_left _ _).trans hαA.le)
  have herr' : TFCoulomb.scalingError t Cq ℓ (ν : ℝ) α < ε / 2 :=
    (le_abs_self _).trans_lt herr
  have hquant := regularScaledQuantumEnergy_ge_discreteTFInfimum_of_neumann_data hq
    ⟨α, hα⟩ ⟨ℓ, hℓ⟩ hδ ht.le hCq hN z R ψ hnorm
    (spectral N ⟨ℓ, hℓ⟩) (hsharp ⟨ℓ, hℓ⟩)
  have hcont := hinf ℓ hℓ hmesh
  unfold TFCoulomb.scalingError at herr'
  change TFCoulomb.regularTFInfimum a (ν : ℝ) δ z R - ε ≤ _
  linarith only [hcont, hquant, herr']

end LiebThirring.TFSectors
end
