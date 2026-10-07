/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.StateMeasure
public import LiebThirring.TFCoulomb.RegularDiscrete
import LiebThirring.Variational.FormFinite

/-! # Exact attraction and repulsion decompositions for the sector law -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.TFSectors

noncomputable def sectorAttraction {N q M : ℕ} (α δ ℓ : ℝ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : FormDomain N q)
    (σ : (Fin N → LatticeIndex) → Measure (Configuration N))
    (b : Fin N → LatticeIndex) : ℝ :=
  α⁻¹ * (∫⁻ x, ENNReal.ofReal (∑ i : Fin N,
    tfCappedNuclearPotential δ z R (particlePosition x i))
      ∂sectorMeasure ℓ (ψ : State N q) σ b).toReal

noncomputable def sectorRepulsion {N q : ℕ} (α ℓ : ℝ) (ψ : FormDomain N q)
    (σ : (Fin N → LatticeIndex) → Measure (Configuration N))
    (b : Fin N → LatticeIndex) : ℝ :=
  α⁻¹ ^ 2 * (∫⁻ x, electronRepulsion x ∂sectorMeasure ℓ (ψ : State N q) σ b).toReal

theorem measurable_cappedAttraction {N M : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    Measurable (fun x : Configuration N => ENNReal.ofReal (∑ i : Fin N,
      tfCappedNuclearPotential δ z R (particlePosition x i))) := by
  apply Measurable.ennreal_ofReal
  exact Finset.measurable_sum _ (fun i _ =>
    (continuous_tfCappedNuclearPotential hδ z R).measurable.comp (measurable_particlePosition i))

theorem lintegral_cappedAttraction_stateMeasure_ne_top {N q M : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : State N q) :
    (∫⁻ x, ENNReal.ofReal (∑ i : Fin N,
      tfCappedNuclearPotential δ z R (particlePosition x i)) ∂stateMeasure ψ) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (b := ∫⁻ _ : Configuration N,
    ENNReal.ofReal ((N : ℝ) * ((∑ k, (z k : ℝ)) / δ)) ∂stateMeasure ψ)
  · rw [lintegral_const]
    finiteness
  · apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ∑ _i : Fin N, (∑ k, (z k : ℝ)) / δ :=
        Finset.sum_le_sum (fun i _ => tfCappedNuclearPotential_le hδ z R (particlePosition x i))
      _ = _ := by simp

theorem lintegral_repulsion_stateMeasure_ne_top {N q : ℕ} (ψ : FormDomain N q) :
    (∫⁻ x, electronRepulsion x ∂stateMeasure (ψ : State N q)) ≠ ⊤ := by
  rw [lintegral_stateMeasure _ _ Assembly.measurable_electronRepulsion]
  exact (lintegral_electronRepulsion_lt_top (ψ : State N q) ψ.property.2).ne

theorem hasSum_sectorAttraction {N q M : ℕ} {δ ℓ : ℝ} (hδ : 0 < δ) (hℓ : 0 < ℓ)
    (α : ℝ) (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : FormDomain N q)
    (σ : (Fin N → LatticeIndex) → Measure (Configuration N)) :
    HasSum (fun b => sectorProbability ℓ (ψ : State N q) b *
      sectorAttraction α δ ℓ z R ψ σ b) (α⁻¹ * TFCoulomb.cappedAttractionExpectation δ z R ψ) := by
  have h := (hasSum_sectorExpectation hℓ (ψ : State N q) σ _
    (lintegral_cappedAttraction_stateMeasure_ne_top hδ z R (ψ : State N q))).mul_left α⁻¹
  rw [lintegral_stateMeasure _ _ (measurable_cappedAttraction hδ z R)] at h
  simpa only [sectorAttraction, TFCoulomb.cappedAttractionExpectation,
    mul_left_comm] using h

theorem hasSum_sectorRepulsion {N q : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (α : ℝ)
    (ψ : FormDomain N q)
    (σ : (Fin N → LatticeIndex) → Measure (Configuration N)) :
    HasSum (fun b => sectorProbability ℓ (ψ : State N q) b *
      sectorRepulsion α ℓ ψ σ b) (α⁻¹ ^ 2 * TFCoulomb.repulsionExpectation ψ) := by
  have h := (hasSum_sectorExpectation hℓ (ψ : State N q) σ electronRepulsion
    (lintegral_repulsion_stateMeasure_ne_top ψ)).mul_left (α⁻¹ ^ 2)
  rw [lintegral_stateMeasure _ _ Assembly.measurable_electronRepulsion] at h
  simpa only [sectorRepulsion, TFCoulomb.repulsionExpectation, mul_left_comm] using h

theorem lintegral_sectorRepulsion_ne_top {N q : ℕ} (ℓ : ℝ) (ψ : FormDomain N q)
    (σ : (Fin N → LatticeIndex) → Measure (Configuration N))
    (hσ : ∀ b, (∫⁻ x, electronRepulsion x ∂σ b) ≠ ⊤) (b : Fin N → LatticeIndex) :
    (∫⁻ x, electronRepulsion x ∂sectorMeasure ℓ (ψ : State N q) σ b) ≠ ⊤ :=
  lintegral_conditionalMeasure_ne_top _ _ _ _ (hσ b) (lintegral_repulsion_stateMeasure_ne_top ψ)

end LiebThirring.TFSectors
end
