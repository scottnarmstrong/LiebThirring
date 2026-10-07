/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.AsymptoticLowerBound
import LiebThirring.TFLattice.EigenvalueEstimate

/-! # The uniform regular lower estimate consumed by the electronic limit

This is regular-potential lower bound at the retained kinetic fraction `1 - η`, with precisely the
quantifier order of `TFLimit`'s lower input. The final theorem consumes the
proved sharp eigenvalue sums sharp sum; only the Neumann product spectral expansion remains an
analytic input. The generic remainder-constant interface is also retained.
-/

public section
open scoped NNReal
open LiebThirring.TFLattice
namespace LiebThirring.TFSectors

/-- The exact regular lower input to the electronic limit assembly. The charge
threshold is uniform over particle numbers and normalized form-domain states. -/
theorem regularScaledQuantumEnergy_eventually_ge_reduced_kinetic_of_neumann_data
    (q : {q : ℕ // 1 ≤ q}) {M : ℕ} {Cq : ℝ} (hCq : 0 ≤ Cq)
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (spectral : ∀ (N : ℕ) (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex),
      NeumannProductSpectralData N q.val ℓ b)
    (hsharp : ∀ (ℓ : {x : ℝ // 0 < x}) (s : Finset (ModeIndex q.val)),
      IsFilled (fun _ => True) s →
      (tfKineticConstant q).val * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ ((5 : ℝ) / 3) -
        Cq * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ ((4 : ℝ) / 3) ≤
          ∑ p ∈ s, cubeEigenvalue ℓ p) :
    ∀ (η : ℝ), 0 < η → η < 1 → ∀ (δ : ℝ), 0 < δ →
      ∀ (ε : ℝ), 0 < ε → ∃ A > 0, ∀ (α : ℝ≥0), A < (α : ℝ) →
      ∀ (n : ℕ), (n : ℝ) = (α : ℝ) * (ν : ℝ) →
      ∀ (ψ : FormDomain n q.val), ‖ψ.val‖ = 1 →
        TFCoulomb.regularTFInfimum ((1 - η) * (tfKineticConstant q).val) (ν : ℝ) δ z R - ε ≤
          TFCoulomb.regularScaledQuantumEnergy (α : ℝ) δ (1 - η) z R ψ := by
  intro η _hη hη1 δ hδ ε hε
  obtain ⟨ℓ, _hℓ, A, hA, hbound⟩ :=
    regularScaledQuantumEnergy_eventually_ge_of_neumann_data q.property hδ
      (sub_pos.mpr hη1) hCq ν z R spectral hsharp ε hε
  exact ⟨A, hA, fun α hα n hn ψ hnorm => hbound (α : ℝ) hα n hn ψ hnorm⟩

/-- The exact electronic assembly lower input with sharp eigenvalue sums discharged. The proved
sharp sum supplies its fixed error constant; only Neumann spectral data remain. -/
theorem regularScaledQuantumEnergy_eventually_ge_reduced_kinetic_of_neumann_spectral_data
    (q : {q : ℕ // 1 ≤ q}) {M : ℕ}
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (spectral : ∀ (N : ℕ) (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex),
      NeumannProductSpectralData N q.val ℓ b) :
    ∀ (η : ℝ), 0 < η → η < 1 → ∀ (δ : ℝ), 0 < δ →
      ∀ (ε : ℝ), 0 < ε → ∃ A > 0, ∀ (α : ℝ≥0), A < (α : ℝ) →
      ∀ (n : ℕ), (n : ℝ) = (α : ℝ) * (ν : ℝ) →
      ∀ (ψ : FormDomain n q.val), ‖ψ.val‖ = 1 →
        TFCoulomb.regularTFInfimum ((1 - η) * (tfKineticConstant q).val) (ν : ℝ) δ z R - ε ≤
          TFCoulomb.regularScaledQuantumEnergy (α : ℝ) δ (1 - η) z R ψ := by
  exact regularScaledQuantumEnergy_eventually_ge_reduced_kinetic_of_neumann_data
    q (cubeEigenvalueErrorConstant_nonneg q.val) ν z R spectral
    (fun ℓ _s hs => sum_cubeEigenvalue_neumann_lower q.property ℓ hs)

end LiebThirring.TFSectors
end
