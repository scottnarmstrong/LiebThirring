/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.Expectations

/-! # The cube-sup attraction bound in an actual normalized sector -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.TFSectors

theorem cappedPotential_le_cubeSup {M : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (ℓ : ℝ) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (β : LatticeIndex) {x : Position} (hx : x ∈ latticeClosedCell ℓ β) :
    tfCappedNuclearPotential δ z R x ≤ TFCoulomb.cubeSupCappedPotential δ ℓ z R β := by
  exact le_csSup (TFCoulomb.cubeCappedPotentialValues_bddAbove hδ ℓ z R β) ⟨x, hx, rfl⟩

theorem cubeSupCappedPotential_nonneg {M : ℕ} {δ ℓ : ℝ} (hδ : 0 < δ) (hℓ : 0 ≤ ℓ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (β : LatticeIndex) :
    0 ≤ TFCoulomb.cubeSupCappedPotential δ ℓ z R β :=
  (tfCappedNuclearPotential_nonneg hδ z R (latticeCorner ℓ β)).trans
    (cappedPotential_le_cubeSup hδ ℓ z R β (latticeCorner_mem_closedCell hℓ β))

theorem cappedAttraction_integral_le_cubeSum {N M : ℕ} {δ ℓ : ℝ}
    (hδ : 0 < δ) (hℓ : 0 ≤ ℓ) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (b : Fin N → LatticeIndex) (μ : Measure (Configuration N)) [IsProbabilityMeasure μ]
    (hsupport : ∀ᵐ x ∂μ, ∀ i, particlePosition x i ∈ latticeClosedCell ℓ (b i)) :
    (∫⁻ x, ENNReal.ofReal (∑ i : Fin N,
      tfCappedNuclearPotential δ z R (particlePosition x i)) ∂μ).toReal ≤
        ∑ i : Fin N, TFCoulomb.cubeSupCappedPotential δ ℓ z R (b i) := by
  have hn : 0 ≤ ∑ i : Fin N, TFCoulomb.cubeSupCappedPotential δ ℓ z R (b i) :=
    Finset.sum_nonneg (fun i _ => cubeSupCappedPotential_nonneg hδ hℓ z R (b i))
  have hbound : (∫⁻ x, ENNReal.ofReal (∑ i : Fin N,
      tfCappedNuclearPotential δ z R (particlePosition x i)) ∂μ) ≤
        ENNReal.ofReal (∑ i : Fin N, TFCoulomb.cubeSupCappedPotential δ ℓ z R (b i)) := by
    calc
      _ ≤ ∫⁻ _ : Configuration N, ENNReal.ofReal
          (∑ i : Fin N, TFCoulomb.cubeSupCappedPotential δ ℓ z R (b i)) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hsupport] with x hx
        exact ENNReal.ofReal_le_ofReal (Finset.sum_le_sum (fun i _ =>
          cappedPotential_le_cubeSup hδ ℓ z R (b i) (hx i)))
      _ = _ := by simp
  simpa only [ENNReal.toReal_ofReal hn] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound

theorem sectorAttraction_le_cubeSum {N q M : ℕ} {α δ ℓ : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hℓ : 0 ≤ ℓ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : FormDomain N q)
    (σ : (Fin N → LatticeIndex) → Measure (Configuration N))
    (hσprob : ∀ b, IsProbabilityMeasure (σ b))
    (hσsupport : ∀ b, ∀ᵐ x ∂σ b, ∀ i, particlePosition x i ∈ latticeClosedCell ℓ (b i))
    (b : Fin N → LatticeIndex) :
    sectorAttraction α δ ℓ z R ψ σ b ≤
      α⁻¹ * ∑ i : Fin N, TFCoulomb.cubeSupCappedPotential δ ℓ z R (b i) := by
  have := isProbabilityMeasure_sectorMeasure ℓ (ψ : State N q) σ hσprob b
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hα.le)
  exact cappedAttraction_integral_le_cubeSum hδ hℓ z R b _
    (ae_sectorMeasure_closedCell ℓ (ψ : State N q) σ hσsupport b)

end LiebThirring.TFSectors
end
