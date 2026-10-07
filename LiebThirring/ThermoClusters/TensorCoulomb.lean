/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.TensorPotentials
public import LiebThirring.ThermoClusters.TensorExpectations
public import LiebThirring.Thermodynamic.QuantumRepulsionEnergy
public import LiebThirring.Thermodynamic.QuantumAttractionEnergy
import LiebThirring.Kinetic.DensityBasic

/-! # Coulomb energies of ordered correlated cluster products

Normalized compact Schwartz clusters give exact identities for the
positive repulsion and attraction energies. Internal expectations retain
all electron–nuclear correlations; the four cross-species terms depend on
the one-body number measures through genuine product-measure interactions.
No finiteness or statistics premise is needed for these positive identities.

A separate conditional real identity takes finite total repulsive and
attractive expectations, deriving all necessary summand finiteness.
Lieb–Lebowitz (1972) II.E before (2.25).
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap
namespace LiebThirring
private def elPos {N M : ℕ} (i : Fin N) (X : QuantumConfiguration N M) : Position :=
  particlePosition X.fst i
private def nucPos {N M : ℕ} (k : Fin M) (X : QuantumConfiguration N M) : Position :=
  particlePosition X.snd k
private theorem elPos_measurable (N M : ℕ) (i : Fin N) : Measurable (elPos (M:=M) i) :=
  (measurable_particlePosition i).comp (WithLp.fstL 2 ℝ _ _).continuous.measurable
private theorem nucPos_measurable (N M : ℕ) (k : Fin M) : Measurable (nucPos (N:=N) k) :=
  (measurable_particlePosition k).comp (WithLp.sndL 2 ℝ _ _).continuous.measurable
private theorem kernel_measurable {A : Type*} [MeasurableSpace A]
    (a b : A → Position) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun X => coulombKernel (a X) (b X)) := by
  unfold coulombKernel
  exact ((ha.sub hb).norm.ennreal_ofReal).inv
private noncomputable def crossPotential {A B ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → A → Position) (b : κ → B → Position) (Z : A × B) : ℝ≥0∞ :=
  ∑ i, ∑ j, coulombKernel (a i Z.1) (b j Z.2)
private theorem crossPotential_measurable {A B ι κ : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [Fintype ι] [Fintype κ]
    (a : ι → A → Position) (ha : ∀ i, Measurable (a i))
    (b : κ → B → Position) (hb : ∀ j, Measurable (b j)) :
    Measurable (crossPotential a b) := by
  classical
  unfold crossPotential
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact kernel_measurable (fun Z : A × B => a i Z.1) (fun Z => b j Z.2)
    ((ha i).comp measurable_fst) ((hb j).comp measurable_snd)
private noncomputable def repPotential {N M : ℕ} (z : ℕ) (X : QuantumConfiguration N M) : ℝ≥0∞ :=
  electronRepulsion X.fst + nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0)) (particlePosition X.snd)
private noncomputable def attrPotential {N M : ℕ} (z : ℕ) (X : QuantumConfiguration N M) : ℝ≥0∞ :=
  attraction (fun _ : Fin M => (z : ℝ≥0)) (particlePosition X.snd) X.fst
private theorem repPotential_measurable (N M z : ℕ) : Measurable (repPotential (N:=N) (M:=M) z) := by
  classical
  unfold repPotential electronRepulsion nuclearRepulsion
  apply Measurable.add
  · apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact kernel_measurable (elPos i) (elPos j) (elPos_measurable N M i) (elPos_measurable N M j)
  · apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact (measurable_const (a := (z : ℝ≥0∞)*(z : ℝ≥0∞))).mul
      (kernel_measurable (nucPos i) (nucPos j) (nucPos_measurable N M i) (nucPos_measurable N M j))
private theorem attrPotential_measurable (N M z : ℕ) : Measurable (attrPotential (N:=N) (M:=M) z) := by
  classical
  unfold attrPotential attraction
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro k _
  exact (measurable_const (a := (z : ℝ≥0∞))).mul
    (kernel_measurable (elPos i) (nucPos k) (elPos_measurable N M i) (nucPos_measurable N M k))
private theorem probability_mass_one {N M q : ℕ} (ψ : QuantumState N M q) (hψ : ‖ψ‖=1) :
    quantumProbabilityMeasure ψ Set.univ = 1 := by
  rw [quantumProbabilityMeasure_mass, ← ofReal_norm, hψ]
  simp
private theorem product_internal_fst {N₁ N₂ M₁ M₂ q : ℕ}
    (ψ : QuantumState N₁ M₁ q) (χ : QuantumState N₂ M₂ q) (hχ : ‖χ‖ = 1)
    (w : QuantumConfiguration N₁ M₁ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ Z : QuantumConfiguration N₁ M₁ × QuantumConfiguration N₂ M₂, w Z.1
      ∂(quantumProbabilityMeasure ψ).prod (quantumProbabilityMeasure χ)) =
    ∫⁻ X, w X ∂quantumProbabilityMeasure ψ := by
  rw [lintegral_prod (f := fun Z : QuantumConfiguration N₁ M₁ × QuantumConfiguration N₂ M₂ => w Z.1) (hw.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, probability_mass_one χ hχ, mul_one]
private theorem product_internal_snd {N₁ N₂ M₁ M₂ q : ℕ}
    (ψ : QuantumState N₁ M₁ q) (χ : QuantumState N₂ M₂ q) (hψ : ‖ψ‖ = 1)
    (w : QuantumConfiguration N₂ M₂ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ Z : QuantumConfiguration N₁ M₁ × QuantumConfiguration N₂ M₂, w Z.2
      ∂(quantumProbabilityMeasure ψ).prod (quantumProbabilityMeasure χ)) =
    ∫⁻ X, w X ∂quantumProbabilityMeasure χ := by
  rw [lintegral_prod (f := fun Z : QuantumConfiguration N₁ M₁ × QuantumConfiguration N₂ M₂ => w Z.2) (hw.comp measurable_snd).aemeasurable]
  change (∫⁻ _ : QuantumConfiguration N₁ M₁, (∫⁻ Y, w Y ∂quantumProbabilityMeasure χ)
    ∂quantumProbabilityMeasure ψ) = _
  rw [lintegral_const, probability_mass_one ψ hψ, mul_one]
private theorem crossPotential_expectation {N₁ N₂ M₁ M₂ q : ℕ}
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ψ : QuantumState N₁ M₁ q) (χ : QuantumState N₂ M₂ q)
    (a : ι → QuantumConfiguration N₁ M₁ → Position) (ha : ∀ i, Measurable (a i))
    (b : κ → QuantumConfiguration N₂ M₂ → Position) (hb : ∀ j, Measurable (b j)) :
    (∫⁻ Z, crossPotential a b Z ∂(quantumProbabilityMeasure ψ).prod (quantumProbabilityMeasure χ)) =
    clusterCoulombInteraction (∑ i, (quantumProbabilityMeasure ψ).map (a i))
      (∑ j, (quantumProbabilityMeasure χ).map (b j)) := by
  classical
  rw [clusterCoulombInteraction_sum_map ψ χ a ha b hb]
  unfold crossPotential
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [lintegral_finsetSum]
    intro j _
    exact kernel_measurable (fun Z : QuantumConfiguration N₁ M₁ × QuantumConfiguration N₂ M₂ => a i Z.1) (fun Z => b j Z.2)
      ((ha i).comp measurable_fst) ((hb j).comp measurable_snd)
  · intro i _
    apply Finset.measurable_sum
    intro j _
    exact kernel_measurable (fun Z : QuantumConfiguration N₁ M₁ × QuantumConfiguration N₂ M₂ => a i Z.1) (fun Z => b j Z.2)
      ((ha i).comp measurable_fst) ((hb j).comp measurable_snd)
private theorem repEnergy_probability {N M q : ℕ} (z : ℕ) (ψ : QuantumState N M q) :
    quantumRepulsionEnergy z ψ = ∫⁻ X, repPotential z X ∂quantumProbabilityMeasure ψ := by
  rw [quantumProbabilityMeasure_lintegral ψ _ (repPotential_measurable N M z)]
  rfl
private theorem attrEnergy_probability {N M q : ℕ} (z : ℕ) (ψ : QuantumState N M q) :
    quantumAttractionEnergy z ψ = ∫⁻ X, attrPotential z X ∂quantumProbabilityMeasure ψ := by
  rw [quantumProbabilityMeasure_lintegral ψ _ (attrPotential_measurable N M z)]
  rfl

private theorem repPotential_split {n₁ n₂ m₁ m₂ : ℕ} (z : ℕ)
    (X : QuantumConfiguration (n₁+n₂) (m₁+m₂)) :
    repPotential z X =
      repPotential z (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst +
      repPotential z (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd +
      crossPotential (elPos (N:=n₁) (M:=m₁)) (elPos (N:=n₂) (M:=m₂))
        (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂ X) +
      (z : ℝ≥0∞)^2 * crossPotential (nucPos (N:=n₁) (M:=m₁)) (nucPos (N:=n₂) (M:=m₂))
        (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂ X) := by
  unfold repPotential
  rw [electronRepulsion_configurationClusterSplit,
    nuclearRepulsion_configurationClusterSplit]
  simp only [← Finset.mul_sum]
  change _ = _ + _ + (∑ i : Fin n₁, ∑ j : Fin n₂,
      coulombKernel (particlePosition (configurationClusterSplit n₁ n₂ X.fst).fst i)
        (particlePosition (configurationClusterSplit n₁ n₂ X.fst).snd j)) +
    (z : ℝ≥0∞)^2 * (∑ i : Fin m₁, ∑ j : Fin m₂,
      coulombKernel (particlePosition (configurationClusterSplit m₁ m₂ X.snd).fst i)
        (particlePosition (configurationClusterSplit m₁ m₂ X.snd).snd j))
  rw [pow_two]
  ac_rfl

private theorem attrPotential_split {n₁ n₂ m₁ m₂ : ℕ} (z : ℕ)
    (X : QuantumConfiguration (n₁+n₂) (m₁+m₂)) :
    attrPotential z X =
      attrPotential z (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst +
      attrPotential z (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd +
      (z : ℝ≥0∞) * crossPotential (elPos (N:=n₁) (M:=m₁)) (nucPos (N:=n₂) (M:=m₂))
        (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂ X) +
      (z : ℝ≥0∞) * crossPotential (nucPos (N:=n₁) (M:=m₁)) (elPos (N:=n₂) (M:=m₂))
        (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂ X) := by
  unfold attrPotential
  rw [attraction_quantumClusterSplit]
  simp only [crossPotential, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact coulombKernel_symm _ _


private theorem lintegral_add_four {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (u v w t : A → ℝ≥0∞) (hu : Measurable u) (hv : Measurable v) (hw : Measurable w) :
    (∫⁻ X, u X + v X + w X + t X ∂μ) =
      (∫⁻ X, u X ∂μ) + (∫⁻ X, v X ∂μ) + (∫⁻ X, w X ∂μ) + (∫⁻ X, t X ∂μ) := by
  rw [lintegral_add_left (f := fun X => u X + v X + w X) ((hu.add hv).add hw) t,
    lintegral_add_left (f := fun X => u X + v X) (hu.add hv) w,
    lintegral_add_left hu v]

/-- Normalized ordered correlated clusters split the actual positive repulsion energy. -/
theorem quantumRepulsionEnergy_clusterProductSchwartz_of_normalized {n₁ n₂ m₁ m₂ q : ℕ}
    (z : ℕ) (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X))
    (hnf : ‖f.toLp 2 volume‖ = 1) (hnh : ‖h.toLp 2 volume‖ = 1) :
    quantumRepulsionEnergy z ((clusterProductSchwartz f h hf hh).toLp 2 volume) =
      quantumRepulsionEnergy z (f.toLp 2 volume) + quantumRepulsionEnergy z (h.toLp 2 volume) +
      clusterCoulombInteraction (quantumElectronMeasure (f.toLp 2 volume))
        (quantumElectronMeasure (h.toLp 2 volume)) +
      (z : ℝ≥0∞)^2 * clusterCoulombInteraction (quantumNuclearMeasure (f.toLp 2 volume))
        (quantumNuclearMeasure (h.toLp 2 volume)) := by
  let ψ := f.toLp 2 volume
  let χ := h.toLp 2 volume
  let ee := crossPotential (elPos (N:=n₁) (M:=m₁)) (elPos (N:=n₂) (M:=m₂))
  let nn := crossPotential (nucPos (N:=n₁) (M:=m₁)) (nucPos (N:=n₂) (M:=m₂))
  have hee : Measurable ee := crossPotential_measurable _
    (elPos_measurable n₁ m₁) _ (elPos_measurable n₂ m₂)
  have hnn : Measurable nn := crossPotential_measurable _
    (nucPos_measurable n₁ m₁) _ (nucPos_measurable n₂ m₂)
  have hr₁ : Measurable (fun Z : QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂ =>
      repPotential z Z.1) := (repPotential_measurable n₁ m₁ z).comp measurable_fst
  have hr₂ : Measurable (fun Z : QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂ =>
      repPotential z Z.2) := (repPotential_measurable n₂ m₂ z).comp measurable_snd
  let w := fun Z : QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂ =>
    repPotential z Z.1 + repPotential z Z.2 + ee Z + (z : ℝ≥0∞)^2 * nn Z
  have hw : Measurable w := ((hr₁.add hr₂).add hee).add (measurable_const.mul hnn)
  rw [repEnergy_probability]
  calc
    _ = ∫⁻ X, w (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂ X)
        ∂quantumProbabilityMeasure ((clusterProductSchwartz f h hf hh).toLp 2 volume) := by
      exact lintegral_congr (repPotential_split z)
    _ = ∫⁻ Z, w Z ∂(quantumProbabilityMeasure ψ).prod (quantumProbabilityMeasure χ) :=
      clusterProductSchwartz_expectation f h hf hh w hw
    _ = _ := by
      change (∫⁻ Z, repPotential z Z.1 + repPotential z Z.2 + ee Z + (z : ℝ≥0∞)^2 * nn Z
        ∂(quantumProbabilityMeasure ψ).prod (quantumProbabilityMeasure χ)) = _
      rw [lintegral_add_four _ _ _ _ _ hr₁ hr₂ hee,
        product_internal_fst ψ χ hnh _ (repPotential_measurable n₁ m₁ z),
        product_internal_snd ψ χ hnf _ (repPotential_measurable n₂ m₂ z),
        ← repEnergy_probability, ← repEnergy_probability, lintegral_const_mul _ hnn]
      rw [crossPotential_expectation ψ χ _ (elPos_measurable n₁ m₁) _ (elPos_measurable n₂ m₂),
        crossPotential_expectation ψ χ _ (nucPos_measurable n₁ m₁) _ (nucPos_measurable n₂ m₂)]
      rfl

/-- Both independent cross electron–nucleus terms occur in the actual positive attraction. -/
theorem quantumAttractionEnergy_clusterProductSchwartz_of_normalized {n₁ n₂ m₁ m₂ q : ℕ}
    (z : ℕ) (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X))
    (hnf : ‖f.toLp 2 volume‖ = 1) (hnh : ‖h.toLp 2 volume‖ = 1) :
    quantumAttractionEnergy z ((clusterProductSchwartz f h hf hh).toLp 2 volume) =
      quantumAttractionEnergy z (f.toLp 2 volume) + quantumAttractionEnergy z (h.toLp 2 volume) +
      (z : ℝ≥0∞) * clusterCoulombInteraction (quantumElectronMeasure (f.toLp 2 volume))
        (quantumNuclearMeasure (h.toLp 2 volume)) +
      (z : ℝ≥0∞) * clusterCoulombInteraction (quantumNuclearMeasure (f.toLp 2 volume))
        (quantumElectronMeasure (h.toLp 2 volume)) := by
  let ψ := f.toLp 2 volume
  let χ := h.toLp 2 volume
  let en := crossPotential (elPos (N:=n₁) (M:=m₁)) (nucPos (N:=n₂) (M:=m₂))
  let ne := crossPotential (nucPos (N:=n₁) (M:=m₁)) (elPos (N:=n₂) (M:=m₂))
  have hen : Measurable en := crossPotential_measurable _
    (elPos_measurable n₁ m₁) _ (nucPos_measurable n₂ m₂)
  have hne : Measurable ne := crossPotential_measurable _
    (nucPos_measurable n₁ m₁) _ (elPos_measurable n₂ m₂)
  have ha₁ : Measurable (fun Z : QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂ =>
      attrPotential z Z.1) := (attrPotential_measurable n₁ m₁ z).comp measurable_fst
  have ha₂ : Measurable (fun Z : QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂ =>
      attrPotential z Z.2) := (attrPotential_measurable n₂ m₂ z).comp measurable_snd
  let w := fun Z : QuantumConfiguration n₁ m₁ × QuantumConfiguration n₂ m₂ =>
    attrPotential z Z.1 + attrPotential z Z.2 + (z : ℝ≥0∞) * en Z + (z : ℝ≥0∞) * ne Z
  have hzen : Measurable (fun Z => (z : ℝ≥0∞)*en Z) := measurable_const.mul hen
  have hw : Measurable w := ((ha₁.add ha₂).add hzen).add (measurable_const.mul hne)
  rw [attrEnergy_probability]
  calc
    _ = ∫⁻ X, w (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂ X)
        ∂quantumProbabilityMeasure ((clusterProductSchwartz f h hf hh).toLp 2 volume) := by
      exact lintegral_congr (attrPotential_split z)
    _ = ∫⁻ Z, w Z ∂(quantumProbabilityMeasure ψ).prod (quantumProbabilityMeasure χ) :=
      clusterProductSchwartz_expectation f h hf hh w hw
    _ = _ := by
      change (∫⁻ Z, attrPotential z Z.1 + attrPotential z Z.2 + (z : ℝ≥0∞)*en Z + (z : ℝ≥0∞)*ne Z
        ∂(quantumProbabilityMeasure ψ).prod (quantumProbabilityMeasure χ)) = _
      rw [lintegral_add_four _ _ _ _ _ ha₁ ha₂ hzen,
        product_internal_fst ψ χ hnh _ (attrPotential_measurable n₁ m₁ z),
        product_internal_snd ψ χ hnf _ (attrPotential_measurable n₂ m₂ z),
        ← attrEnergy_probability, ← attrEnergy_probability,
        lintegral_const_mul _ hen, lintegral_const_mul _ hne]
      rw [crossPotential_expectation ψ χ _ (elPos_measurable n₁ m₁) _ (nucPos_measurable n₂ m₂),
        crossPotential_expectation ψ χ _ (nucPos_measurable n₁ m₁) _ (elPos_measurable n₂ m₂)]
      rfl


/-- The real difference formula, conditional only on finite total positive expectations.
No finite-energy premise is used in the preceding positive identities. -/
theorem clusterProductSchwartz_coulomb_toReal_of_finite {n₁ n₂ m₁ m₂ q : ℕ}
    (z : ℕ) (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
    (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
    (hf : HasCompactSupport (fun X => f X)) (hh : HasCompactSupport (fun X => h X))
    (hnf : ‖f.toLp 2 volume‖ = 1) (hnh : ‖h.toLp 2 volume‖ = 1)
    (hR : quantumRepulsionEnergy z ((clusterProductSchwartz f h hf hh).toLp 2 volume) < ⊤)
    (hA : quantumAttractionEnergy z ((clusterProductSchwartz f h hf hh).toLp 2 volume) < ⊤) :
    let ψ := f.toLp 2 volume
    let χ := h.toLp 2 volume
    let Ψ := (clusterProductSchwartz f h hf hh).toLp 2 volume
    (quantumRepulsionEnergy z Ψ).toReal - (quantumAttractionEnergy z Ψ).toReal =
      ((quantumRepulsionEnergy z ψ).toReal - (quantumAttractionEnergy z ψ).toReal) +
      ((quantumRepulsionEnergy z χ).toReal - (quantumAttractionEnergy z χ).toReal) +
      (clusterCoulombInteraction (quantumElectronMeasure ψ) (quantumElectronMeasure χ)).toReal +
      (z : ℝ)^2 * (clusterCoulombInteraction (quantumNuclearMeasure ψ) (quantumNuclearMeasure χ)).toReal -
      (z : ℝ) * (clusterCoulombInteraction (quantumElectronMeasure ψ) (quantumNuclearMeasure χ)).toReal -
      (z : ℝ) * (clusterCoulombInteraction (quantumNuclearMeasure ψ) (quantumElectronMeasure χ)).toReal := by
  dsimp only
  have hr := quantumRepulsionEnergy_clusterProductSchwartz_of_normalized z f h hf hh hnf hnh
  have ha := quantumAttractionEnergy_clusterProductSchwartz_of_normalized z f h hf hh hnf hnh
  rw [hr] at hR
  rw [ha] at hA
  obtain ⟨hR₁₂ee, hnn⟩ := ENNReal.add_lt_top.mp hR
  obtain ⟨hR₁₂, hee⟩ := ENNReal.add_lt_top.mp hR₁₂ee
  obtain ⟨hR₁, hR₂⟩ := ENNReal.add_lt_top.mp hR₁₂
  obtain ⟨hA₁₂en, hne⟩ := ENNReal.add_lt_top.mp hA
  obtain ⟨hA₁₂, hen⟩ := ENNReal.add_lt_top.mp hA₁₂en
  obtain ⟨hA₁, hA₂⟩ := ENNReal.add_lt_top.mp hA₁₂
  rw [hr, ha,
    ENNReal.toReal_add hR₁₂ee.ne hnn.ne, ENNReal.toReal_add hR₁₂.ne hee.ne,
    ENNReal.toReal_add hR₁.ne hR₂.ne,
    ENNReal.toReal_add hA₁₂en.ne hne.ne, ENNReal.toReal_add hA₁₂.ne hen.ne,
    ENNReal.toReal_add hA₁.ne hA₂.ne]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  ring

end LiebThirring

end
