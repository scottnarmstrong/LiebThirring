/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.AssignmentGeometry
public import LiebThirring.TFSectors.ProbabilityKernel
import LiebThirring.Kinetic.DensityBasic

/-! # Literal quantum-state law and its ordered sector probabilities -/

@[expose] public section
open MeasureTheory Set Function
open scoped ENNReal NNReal
namespace LiebThirring.TFSectors

/-- The position law with density equal to the squared spin-amplitude norm. -/
noncomputable def stateMeasure {N q : ℕ} (ψ : State N q) : Measure (Configuration N) :=
  volume.withDensity (fun x => (‖ψ x‖₊ : ℝ≥0∞) ^ 2)

instance stateMeasure_isFiniteMeasure {N q : ℕ} (ψ : State N q) :
    IsFiniteMeasure (stateMeasure ψ) := by
  apply isFiniteMeasure_withDensity
  rw [lintegral_state_norm_sq]
  finiteness

theorem isProbabilityMeasure_stateMeasure {N q : ℕ} (ψ : State N q)
    (hψ : ‖ψ‖ = 1) : IsProbabilityMeasure (stateMeasure ψ) := by
  constructor
  rw [stateMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_state_norm_sq]
  have hn : ‖ψ‖₊ = 1 := NNReal.eq hψ
  simp [hn]

theorem lintegral_stateMeasure {N q : ℕ} (ψ : State N q)
    (f : Configuration N → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂stateMeasure ψ) =
      ∫⁻ x, f x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2 := by
  rw [stateMeasure, lintegral_withDensity_eq_lintegral_mul _ (measurable_state_norm_sq ψ) hf]
  simp only [Pi.mul_apply, mul_comm]

/-- Probability of the literal ordered cube-assignment event. -/
noncomputable def sectorProbability {N q : ℕ} (ℓ : ℝ) (ψ : State N q)
    (b : Fin N → LatticeIndex) : ℝ :=
  (stateMeasure ψ (assignmentCell ℓ b)).toReal

theorem sectorProbability_nonneg {N q : ℕ} (ℓ : ℝ) (ψ : State N q)
    (b : Fin N → LatticeIndex) : 0 ≤ sectorProbability ℓ ψ b :=
  ENNReal.toReal_nonneg

theorem hasSum_sectorProbability {N q : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (ψ : State N q) (hψ : ‖ψ‖ = 1) : HasSum (sectorProbability ℓ ψ) 1 := by
  have := isProbabilityMeasure_stateMeasure ψ hψ
  exact hasSum_partition_probability (stateMeasure ψ) (assignmentCell ℓ)
    (measurableSet_assignmentCell ℓ) (fun _ _ h => assignmentCell_disjoint hℓ h)
    (iUnion_assignmentCell hℓ)

/-- The actual conditional position law, completed by an explicit null-event reference. -/
noncomputable def sectorMeasure {N q : ℕ} (ℓ : ℝ) (ψ : State N q)
    (σ : (Fin N → LatticeIndex) → Measure (Configuration N))
    (b : Fin N → LatticeIndex) : Measure (Configuration N) :=
  conditionalMeasure (stateMeasure ψ) (assignmentCell ℓ b) (σ b)

theorem isProbabilityMeasure_sectorMeasure {N q : ℕ} (ℓ : ℝ) (ψ : State N q)
    (σ : (Fin N → LatticeIndex) → Measure (Configuration N))
    (hσ : ∀ b, IsProbabilityMeasure (σ b)) (b : Fin N → LatticeIndex) :
    IsProbabilityMeasure (sectorMeasure ℓ ψ σ b) := by
  have := hσ b
  exact isProbabilityMeasure_conditionalMeasure _ _ _

theorem hasSum_sectorExpectation {N q : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (ψ : State N q) (σ : (Fin N → LatticeIndex) → Measure (Configuration N))
    (f : Configuration N → ℝ≥0∞) (hf : (∫⁻ x, f x ∂stateMeasure ψ) ≠ ⊤) :
    HasSum (fun b => sectorProbability ℓ ψ b *
      (∫⁻ x, f x ∂sectorMeasure ℓ ψ σ b).toReal)
      (∫⁻ x, f x ∂stateMeasure ψ).toReal :=
  hasSum_weighted_conditional_lintegral _ (assignmentCell ℓ) σ
    (measurableSet_assignmentCell ℓ) (fun _ _ h => assignmentCell_disjoint hℓ h)
    (iUnion_assignmentCell hℓ) f hf

theorem ae_sectorMeasure_closedCell {N q : ℕ} (ℓ : ℝ) (ψ : State N q)
    (σ : (Fin N → LatticeIndex) → Measure (Configuration N))
    (hσ : ∀ b, ∀ᵐ x ∂σ b, ∀ i, particlePosition x i ∈ latticeClosedCell ℓ (b i))
    (b : Fin N → LatticeIndex) :
    ∀ᵐ x ∂sectorMeasure ℓ ψ σ b,
      ∀ i, particlePosition x i ∈ latticeClosedCell ℓ (b i) := by
  apply ae_conditionalMeasure _ _ _ (hσ b)
  filter_upwards [ae_restrict_mem (measurableSet_assignmentCell ℓ b)] with x hx
  exact fun i => latticeCell_subset_closedCell ℓ (b i) (hx i)

end LiebThirring.TFSectors
end
