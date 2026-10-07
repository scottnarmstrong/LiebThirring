/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.ClusterTensor
public import LiebThirring.ThermoClusters.Marginals
public import LiebThirring.Electrostatics.Gaussian

/-! # Joint product expectations and independent cross marginals

An ordered product's joint spatial probability is the product of the two
correlated cluster probabilities. Only different clusters are independent.
Coordinate pushforwards identify each cross pair with its one-body measures.
Lieb–Lebowitz (1972) II.E before (2.25).
-/

public section
open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap
namespace LiebThirring

/-- Probability on a Schwartz representative is its actual squared-amplitude density. -/
theorem quantumProbabilityMeasure_schwartz {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    quantumProbabilityMeasure (f.toLp 2 volume) =
      volume.withDensity (fun X => (‖f X‖₊ : ℝ≥0∞)^2) := by
  unfold quantumProbabilityMeasure
  apply withDensity_congr_ae
  filter_upwards [f.coeFn_toLp 2 volume] with X hX
  rw [hX, enorm_eq_nnnorm]

/-- Every joint product observable is integrated against the product probability. -/
theorem clusterProductSchwartz_expectation {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X))
    (w : QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂ → ℝ≥0∞)
    (hw : Measurable w) :
    (∫⁻ X, w (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂ X)
      ∂quantumProbabilityMeasure ((clusterProductSchwartz f h hf hh).toLp 2 volume)) =
    ∫⁻ Z, w Z ∂(quantumProbabilityMeasure (f.toLp 2 volume)).prod
      (quantumProbabilityMeasure (h.toLp 2 volume)) := by
  rw [quantumProbabilityMeasure_schwartz, quantumProbabilityMeasure_schwartz,
    quantumProbabilityMeasure_schwartz]
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (g := fun X => w (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂ X))
    ((clusterProductSchwartz f h hf hh).continuous.measurable.nnnorm.coe_nnreal_ennreal.pow_const 2)
    (hw.comp (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂).measurable)]
  change (∫⁻ X, (‖clusterProduct (fun X => f X) (fun X => h X) X‖₊ : ℝ≥0∞)^2 *
    w (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂ X)) = _
  simp only [clusterProduct_nnnorm_sq]
  rw [prod_withDensity (f.continuous.measurable.nnnorm.coe_nnreal_ennreal.pow_const 2)
    (h.continuous.measurable.nnnorm.coe_nnreal_ennreal.pow_const 2)]
  rw [lintegral_withDensity_eq_lintegral_mul _
    (f := fun Z : QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂ =>
      (‖f Z.1‖₊ : ℝ≥0∞)^2 * (‖h Z.2‖₊ : ℝ≥0∞)^2)
    (((f.continuous.measurable.nnnorm.coe_nnreal_ennreal.pow_const 2).comp measurable_fst).mul
      ((h.continuous.measurable.nnnorm.coe_nnreal_ennreal.pow_const 2).comp measurable_snd)) hw]
  exact (measurePreserving_quantumClusterSplit n₁ n₂ m₁ m₂).lintegral_comp_emb
    (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂).toMeasurableEquiv.measurableEmbedding
    (fun Z => ((‖f Z.1‖₊ : ℝ≥0∞)^2 * (‖h Z.2‖₊ : ℝ≥0∞)^2) * w Z)

/-- An internal observable factors with the other cluster's actual L² mass. -/
theorem clusterProductSchwartz_expectation_left {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X))
    (w : QuantumConfiguration n₁ m₁ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ X, w (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst
      ∂quantumProbabilityMeasure ((clusterProductSchwartz f h hf hh).toLp 2 volume)) =
    (∫⁻ Y, w Y ∂quantumProbabilityMeasure (f.toLp 2 volume)) * ‖h.toLp 2 volume‖ₑ ^ 2 := by
  change (∫⁻ X, (fun Z : QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂ => w Z.1)
    (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂ X)
    ∂quantumProbabilityMeasure ((clusterProductSchwartz f h hf hh).toLp 2 volume)) = _
  rw [clusterProductSchwartz_expectation f h hf hh (fun Z => w Z.1)
    (hw.comp measurable_fst)]
  have he := lintegral_prod_mul (μ := quantumProbabilityMeasure (f.toLp 2 volume))
    (ν := quantumProbabilityMeasure (h.toLp 2 volume)) hw.aemeasurable
    (measurable_const (a := (1 : ℝ≥0∞))).aemeasurable
  simpa only [mul_one, lintegral_const, one_mul, quantumProbabilityMeasure_mass] using he

/-- The second internal observable factors with the first cluster's actual L² mass. -/
theorem clusterProductSchwartz_expectation_right {n₁ n₂ m₁ m₂ q : ℕ}
    (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X))
    (w : QuantumConfiguration n₂ m₂ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ X, w (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd
      ∂quantumProbabilityMeasure ((clusterProductSchwartz f h hf hh).toLp 2 volume)) =
    ‖f.toLp 2 volume‖ₑ ^ 2 * ∫⁻ Y, w Y ∂quantumProbabilityMeasure (h.toLp 2 volume) := by
  change (∫⁻ X, (fun Z : QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂ => w Z.2)
    (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂ X)
    ∂quantumProbabilityMeasure ((clusterProductSchwartz f h hf hh).toLp 2 volume)) = _
  rw [clusterProductSchwartz_expectation f h hf hh (fun Z => w Z.2)
    (hw.comp measurable_snd)]
  have he := lintegral_prod_mul (μ := quantumProbabilityMeasure (f.toLp 2 volume))
    (ν := quantumProbabilityMeasure (h.toLp 2 volume))
    (measurable_const (a := (1 : ℝ≥0∞))).aemeasurable hw.aemeasurable
  simpa only [one_mul, lintegral_const, quantumProbabilityMeasure_mass] using he

/-- Positive mutual Coulomb energy; finite separation will ensure it is finite. -/
@[expose] noncomputable def clusterCoulombInteraction (μ ν : Measure Position) : ℝ≥0∞ :=
  ∫⁻ Z : Position × Position, coulombKernel Z.1 Z.2 ∂μ.prod ν

/-- Mutual energy is additive in its first positive measure. -/
theorem clusterCoulombInteraction_sum_left {ι : Type*} [Fintype ι]
    (μ : ι → Measure Position) (ν : Measure Position) [SFinite ν] :
    clusterCoulombInteraction (∑ i, μ i) ν = ∑ i, clusterCoulombInteraction (μ i) ν := by
  classical
  unfold clusterCoulombInteraction
  rw [lintegral_prod (f := fun Z : Position × Position => coulombKernel Z.1 Z.2)
    measurable_coulombKernel.aemeasurable]
  rw [lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro i _
  exact (lintegral_prod (f := fun Z : Position × Position => coulombKernel Z.1 Z.2)
    measurable_coulombKernel.aemeasurable).symm

/-- Mutual energy is additive in its second positive measure. -/
theorem clusterCoulombInteraction_sum_right {ι : Type*} [Fintype ι]
    (μ : Measure Position) (ν : ι → Measure Position) [∀ i, IsFiniteMeasure (ν i)] :
    clusterCoulombInteraction μ (∑ i, ν i) = ∑ i, clusterCoulombInteraction μ (ν i) := by
  classical
  unfold clusterCoulombInteraction
  rw [lintegral_prod (f := fun Z : Position × Position => coulombKernel Z.1 Z.2)
    measurable_coulombKernel.aemeasurable]
  simp only [lintegral_finsetSum_measure]
  rw [lintegral_finsetSum Finset.univ
    (fun i _ => measurable_coulombKernel.lintegral_prod_right)]
  apply Finset.sum_congr rfl
  intro i _
  exact (lintegral_prod (f := fun Z : Position × Position => coulombKernel Z.1 Z.2)
    measurable_coulombKernel.aemeasurable).symm

/-- Cross pair interactions depend exactly on the two spatial pushforward measures. -/
theorem clusterCoulombInteraction_map {N₁ N₂ M₁ M₂ q : ℕ}
    (ψ : QuantumState N₁ M₁ q) (χ : QuantumState N₂ M₂ q)
    (a : QuantumConfiguration N₁ M₁ → Position) (ha : Measurable a)
    (b : QuantumConfiguration N₂ M₂ → Position) (hb : Measurable b) :
    clusterCoulombInteraction ((quantumProbabilityMeasure ψ).map a)
      ((quantumProbabilityMeasure χ).map b) =
      ∫⁻ Z : QuantumConfiguration N₁ M₁ × QuantumConfiguration N₂ M₂,
        coulombKernel (a Z.1) (b Z.2) ∂(quantumProbabilityMeasure ψ).prod
          (quantumProbabilityMeasure χ) := by
  rw [clusterCoulombInteraction, Measure.map_prod_map _ _ ha hb]
  exact lintegral_map measurable_coulombKernel (ha.prodMap hb)

/-- Summed one-body pushforwards give exactly the independent cross-particle pair sum. -/
theorem clusterCoulombInteraction_sum_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    {N₁ N₂ M₁ M₂ q : ℕ} (ψ : QuantumState N₁ M₁ q) (χ : QuantumState N₂ M₂ q)
    (a : ι → QuantumConfiguration N₁ M₁ → Position) (ha : ∀ i, Measurable (a i))
    (b : κ → QuantumConfiguration N₂ M₂ → Position) (hb : ∀ j, Measurable (b j)) :
    clusterCoulombInteraction (∑ i, (quantumProbabilityMeasure ψ).map (a i))
      (∑ j, (quantumProbabilityMeasure χ).map (b j)) =
      ∑ i, ∑ j, ∫⁻ Z : QuantumConfiguration N₁ M₁ × QuantumConfiguration N₂ M₂,
        coulombKernel (a i Z.1) (b j Z.2) ∂(quantumProbabilityMeasure ψ).prod
          (quantumProbabilityMeasure χ) := by
  classical
  rw [clusterCoulombInteraction_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [clusterCoulombInteraction_sum_right]
  apply Finset.sum_congr rfl
  intro j _
  exact clusterCoulombInteraction_map ψ χ (a i) (ha i) (b j) (hb j)

end LiebThirring
end
