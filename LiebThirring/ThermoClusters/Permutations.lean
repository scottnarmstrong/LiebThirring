/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.HardyJoint
public import LiebThirring.Ionization.EscapePotential

/-!
# Joint particle-label permutations

Electrons are simultaneously permuted in position and spin; nuclei are permuted
in position. The resulting linear isometry preserves the Fourier kinetic
energies and both nonnegative Coulomb expectations, without statistics premises.
The same action transports compact Schwartz supports by a joint-coordinate
homeomorphism. Proof: cluster assembly, shuffle construction.
-/

public section
open MeasureTheory WithLp Set
open scoped ENNReal NNReal SchwartzMap FourierTransform
namespace LiebThirring

/-- Independent electron and nuclear label permutations on the joint spatial carrier. -/
@[expose] noncomputable def quantumPermutation {N M : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) :
    QuantumConfiguration N M ≃ₗᵢ[ℝ] QuantumConfiguration N M :=
  LinearIsometryEquiv.withLpProdCongr 2 (permutationLinearIsometryEquiv σ)
    (permutationLinearIsometryEquiv τ)

@[simp] theorem particlePosition_quantumPermutation_fst {N M : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M))
    (X : QuantumConfiguration N M) (i : Fin N) :
    particlePosition (quantumPermutation σ τ X).fst i = particlePosition X.fst (σ i) := rfl

@[simp] theorem particlePosition_quantumPermutation_snd {N M : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M))
    (X : QuantumConfiguration N M) (k : Fin M) :
    particlePosition (quantumPermutation σ τ X).snd k = particlePosition X.snd (τ k) := rfl

/-- Simultaneous position/spin electron permutation and nuclear position permutation on L². -/
@[expose] noncomputable def quantumStatePermutation {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) :
    QuantumState N M q →ₗᵢ[ℂ] QuantumState N M q :=
  (l2TargetEquiv volume (spinPermutationLinearIsometryEquiv (q := q) σ)).toLinearIsometry.comp
    (Lp.compMeasurePreservingₗᵢ ℂ (quantumPermutation σ τ)
      (quantumPermutation σ τ).measurePreserving)

/-- The L² permutation has the exact simultaneous amplitude representative. -/
theorem coeFn_quantumStatePermutation {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (ψ : QuantumState N M q) :
    quantumStatePermutation σ τ ψ =ᵐ[volume]
      fun X => spinPermutationLinearIsometryEquiv σ (ψ (quantumPermutation σ τ X)) := by
  filter_upwards [l2TargetEquiv_ae volume (spinPermutationLinearIsometryEquiv (q := q) σ)
    (Lp.compMeasurePreserving (quantumPermutation σ τ) (quantumPermutation σ τ).measurePreserving ψ),
    Lp.coeFn_compMeasurePreserving ψ (quantumPermutation σ τ).measurePreserving] with X hX hψ
  change quantumStatePermutation σ τ ψ X = _ at hX
  rw [hX, hψ]
  rfl

@[simp] theorem norm_quantumStatePermutation {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (ψ : QuantumState N M q) :
    ‖quantumStatePermutation σ τ ψ‖ = ‖ψ‖ := (quantumStatePermutation σ τ).norm_map ψ

/-- Fourier transformation commutes exactly with the joint permutation action. -/
theorem fourier_quantumStatePermutation {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (ψ : QuantumState N M q) :
    𝓕 (quantumStatePermutation σ τ ψ) = quantumStatePermutation σ τ (𝓕 ψ) := by
  change 𝓕 ((spinPermutationLinearIsometryEquiv (q := q) σ).toContinuousLinearEquiv.toContinuousLinearMap.compLp
    (Lp.compMeasurePreserving (quantumPermutation σ τ) (quantumPermutation σ τ).measurePreserving ψ)) =
    (spinPermutationLinearIsometryEquiv σ).toContinuousLinearEquiv.toContinuousLinearMap.compLp
      (Lp.compMeasurePreserving (quantumPermutation σ τ) (quantumPermutation σ τ).measurePreserving (𝓕 ψ))
  rw [Fourier.fourier_compLp, Fourier.fourier_compMeasurePreserving]

/-- Joint permutation of a Schwartz trial, with the same position/spin convention. -/
@[expose] noncomputable def quantumSchwartzPermutation {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M))
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    𝓢(QuantumConfiguration N M, SpinAmplitudes N q) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (quantumPermutation σ τ).toContinuousLinearEquiv f).postcompCLM
      (spinPermutationLinearIsometryEquiv σ).toContinuousLinearEquiv.toContinuousLinearMap

/-- The Schwartz action represents the actual L² permutation exactly. -/
theorem quantumSchwartzPermutation_toLp {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M))
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    (quantumSchwartzPermutation σ τ f).toLp 2 volume =
      quantumStatePermutation σ τ (f.toLp 2 volume) := by
  change _ = (spinPermutationLinearIsometryEquiv (q := q) σ).toContinuousLinearEquiv.toContinuousLinearMap.compLp
    (Lp.compMeasurePreserving (quantumPermutation σ τ) (quantumPermutation σ τ).measurePreserving
      (f.toLp 2 volume))
  rw [Fourier.compMeasurePreserving_toLp, Fourier.compLp_toLp]
  rfl

/-- Spin reindexing changes no zero set. -/
theorem tsupport_quantumSchwartzPermutation {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M))
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    tsupport (quantumSchwartzPermutation σ τ f) = quantumPermutation σ τ ⁻¹' tsupport f := by
  change tsupport ((spinPermutationLinearIsometryEquiv (q := q) σ) ∘
    ((f : QuantumConfiguration N M → SpinAmplitudes N q) ∘
      (quantumPermutation σ τ).toHomeomorph)) = _
  rw [tsupport_comp_eq (fun {v} => (spinPermutationLinearIsometryEquiv (q := q) σ).map_eq_zero_iff),
    tsupport_comp_eq_preimage]
  rfl

/-- Compact support survives joint particle-label permutation. -/
theorem isCompact_tsupport_quantumSchwartzPermutation {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M))
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) (hf : IsCompact (tsupport f)) :
    IsCompact (tsupport (quantumSchwartzPermutation σ τ f)) := by
  rw [tsupport_quantumSchwartzPermutation]
  exact (quantumPermutation σ τ).toHomeomorph.isCompact_preimage.mpr hf

private theorem nnnorm_quantumStatePermutation_ae {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (ψ : QuantumState N M q) :
    ∀ᵐ X ∂volume, ‖quantumStatePermutation σ τ ψ X‖₊ = ‖ψ (quantumPermutation σ τ X)‖₊ := by
  filter_upwards [coeFn_quantumStatePermutation σ τ ψ] with X hX
  rw [hX, LinearIsometryEquiv.nnnorm_map]

private theorem permutation_electron_kinetic_change_of_variables {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (φ : QuantumState N M q) :
    (∫⁻ ξ : QuantumConfiguration N M, ENNReal.ofReal ((2 * Real.pi)^2) *
      (‖(quantumPermutation σ τ ξ).fst‖₊ : ℝ≥0∞)^2 *
      (‖φ (quantumPermutation σ τ ξ)‖₊ : ℝ≥0∞)^2) =
    ∫⁻ ξ : QuantumConfiguration N M, ENNReal.ofReal ((2 * Real.pi)^2) *
      (‖ξ.fst‖₊ : ℝ≥0∞)^2 * (‖φ ξ‖₊ : ℝ≥0∞)^2 :=
  (quantumPermutation σ τ).measurePreserving.lintegral_comp_emb
    (quantumPermutation σ τ).toHomeomorph.measurableEmbedding
    (fun ξ : QuantumConfiguration N M => ENNReal.ofReal ((2 * Real.pi)^2) *
      (‖ξ.fst‖₊ : ℝ≥0∞)^2 * (‖φ ξ‖₊ : ℝ≥0∞)^2)

private theorem permutation_nuclear_kinetic_change_of_variables {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (φ : QuantumState N M q) :
    (∫⁻ ξ : QuantumConfiguration N M, ENNReal.ofReal ((2 * Real.pi)^2) *
      (‖(quantumPermutation σ τ ξ).snd‖₊ : ℝ≥0∞)^2 *
      (‖φ (quantumPermutation σ τ ξ)‖₊ : ℝ≥0∞)^2) =
    ∫⁻ ξ : QuantumConfiguration N M, ENNReal.ofReal ((2 * Real.pi)^2) *
      (‖ξ.snd‖₊ : ℝ≥0∞)^2 * (‖φ ξ‖₊ : ℝ≥0∞)^2 :=
  (quantumPermutation σ τ).measurePreserving.lintegral_comp_emb
    (quantumPermutation σ τ).toHomeomorph.measurableEmbedding
    (fun ξ : QuantumConfiguration N M => ENNReal.ofReal ((2 * Real.pi)^2) *
      (‖ξ.snd‖₊ : ℝ≥0∞)^2 * (‖φ ξ‖₊ : ℝ≥0∞)^2)

/-- Joint particle-label permutations preserve the full electronic Fourier kinetic energy. -/
@[simp] theorem quantumElectronKineticEnergy_quantumStatePermutation {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (ψ : QuantumState N M q) :
    quantumElectronKineticEnergy (quantumStatePermutation σ τ ψ) = quantumElectronKineticEnergy ψ := by
  unfold quantumElectronKineticEnergy
  change (∫⁻ ξ : QuantumConfiguration N M, ENNReal.ofReal ((2 * Real.pi)^2) *
    (‖ξ.fst‖₊ : ℝ≥0∞)^2 * (‖(𝓕 (quantumStatePermutation σ τ ψ)) ξ‖₊ : ℝ≥0∞)^2) =
    ∫⁻ ξ : QuantumConfiguration N M, ENNReal.ofReal ((2 * Real.pi)^2) *
      (‖ξ.fst‖₊ : ℝ≥0∞)^2 * (‖(𝓕 ψ) ξ‖₊ : ℝ≥0∞)^2
  rw [fourier_quantumStatePermutation]
  refine Eq.trans (b := ∫⁻ ξ : QuantumConfiguration N M,
    ENNReal.ofReal ((2 * Real.pi)^2) *
      (‖(quantumPermutation σ τ ξ).fst‖₊ : ℝ≥0∞)^2 *
      (‖(𝓕 ψ) (quantumPermutation σ τ ξ)‖₊ : ℝ≥0∞)^2)
    ?_ (permutation_electron_kinetic_change_of_variables σ τ (𝓕 ψ))
  apply lintegral_congr_ae
  filter_upwards [nnnorm_quantumStatePermutation_ae σ τ (𝓕 ψ)] with ξ hξ
  rw [hξ]
  change _ = ENNReal.ofReal ((2 * Real.pi)^2) *
    (‖permutationLinearIsometryEquiv σ ξ.fst‖₊ : ℝ≥0∞)^2 * _
  rw [LinearIsometryEquiv.nnnorm_map]

/-- Joint particle-label permutations preserve the full nuclear Fourier kinetic energy. -/
@[simp] theorem quantumNuclearKineticEnergy_quantumStatePermutation {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (ψ : QuantumState N M q) :
    quantumNuclearKineticEnergy (quantumStatePermutation σ τ ψ) = quantumNuclearKineticEnergy ψ := by
  unfold quantumNuclearKineticEnergy
  change (∫⁻ ξ : QuantumConfiguration N M, ENNReal.ofReal ((2 * Real.pi)^2) *
    (‖ξ.snd‖₊ : ℝ≥0∞)^2 * (‖(𝓕 (quantumStatePermutation σ τ ψ)) ξ‖₊ : ℝ≥0∞)^2) =
    ∫⁻ ξ : QuantumConfiguration N M, ENNReal.ofReal ((2 * Real.pi)^2) *
      (‖ξ.snd‖₊ : ℝ≥0∞)^2 * (‖(𝓕 ψ) ξ‖₊ : ℝ≥0∞)^2
  rw [fourier_quantumStatePermutation]
  refine Eq.trans (b := ∫⁻ ξ : QuantumConfiguration N M,
    ENNReal.ofReal ((2 * Real.pi)^2) *
      (‖(quantumPermutation σ τ ξ).snd‖₊ : ℝ≥0∞)^2 *
      (‖(𝓕 ψ) (quantumPermutation σ τ ξ)‖₊ : ℝ≥0∞)^2)
    ?_ (permutation_nuclear_kinetic_change_of_variables σ τ (𝓕 ψ))
  apply lintegral_congr_ae
  filter_upwards [nnnorm_quantumStatePermutation_ae σ τ (𝓕 ψ)] with ξ hξ
  rw [hξ]
  change _ = ENNReal.ofReal ((2 * Real.pi)^2) *
    (‖permutationLinearIsometryEquiv τ ξ.snd‖₊ : ℝ≥0∞)^2 * _
  rw [LinearIsometryEquiv.nnnorm_map]

/-- Nuclear repulsion with the constant charge is unchanged by nuclear relabeling. -/
theorem nuclearRepulsion_quantumPermutation {N M : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (z : ℕ) (X : QuantumConfiguration N M) :
    nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
      (fun k => particlePosition (quantumPermutation σ τ X).snd k) =
    nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0)) (fun k => particlePosition X.snd k) := by
  rw [nuclearRepulsion_const_eq, nuclearRepulsion_const_eq]
  change (z : ℝ≥0∞)^2 * electronRepulsion (permutePositions τ X.snd) = _
  rw [electronRepulsion_permutePositions]

/-- Constant-charge attraction is unchanged by independent relabeling of both species. -/
theorem attraction_quantumPermutation {N M : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (z : ℕ) (X : QuantumConfiguration N M) :
    attraction (fun _ : Fin M => (z : ℝ≥0))
      (fun k => particlePosition (quantumPermutation σ τ X).snd k)
      (quantumPermutation σ τ X).fst =
    attraction (fun _ : Fin M => (z : ℝ≥0)) (fun k => particlePosition X.snd k) X.fst := by
  change attraction (fun _ : Fin M => (z : ℝ≥0))
    (fun k => particlePosition (permutePositions τ X.snd) k) (permutePositions σ X.fst) = _
  rw [attraction_permutePositions]
  unfold attraction
  simp only [particlePosition_permutePositions]
  apply Finset.sum_congr rfl
  intro i _
  exact Equiv.sum_comp τ (fun k => (z : ℝ≥0∞) * coulombKernel (particlePosition X.fst i)
    (particlePosition X.snd k))

/-- The nonnegative repulsion expectation is unchanged for every joint state. -/
@[simp] theorem quantumRepulsionEnergy_quantumStatePermutation {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (z : ℕ) (ψ : QuantumState N M q) :
    quantumRepulsionEnergy z (quantumStatePermutation σ τ ψ) = quantumRepulsionEnergy z ψ := by
  unfold quantumRepulsionEnergy
  calc
    _ = ∫⁻ X : QuantumConfiguration N M,
      (electronRepulsion (quantumPermutation σ τ X).fst +
        nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
          (fun k => particlePosition (quantumPermutation σ τ X).snd k)) *
      (‖ψ (quantumPermutation σ τ X)‖₊ : ℝ≥0∞)^2 := by
      apply lintegral_congr_ae
      filter_upwards [nnnorm_quantumStatePermutation_ae σ τ ψ] with X hX
      rw [hX, nuclearRepulsion_quantumPermutation]
      change _ = (electronRepulsion (permutePositions σ X.fst) + _) * _
      rw [electronRepulsion_permutePositions]
    _ = _ := (quantumPermutation σ τ).measurePreserving.lintegral_comp_emb
      (quantumPermutation σ τ).toHomeomorph.measurableEmbedding
      (fun X : QuantumConfiguration N M =>
        (electronRepulsion X.fst + nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
          (fun k => particlePosition X.snd k)) * (‖ψ X‖₊ : ℝ≥0∞)^2)

/-- The nonnegative attraction expectation is unchanged for every joint state. -/
@[simp] theorem quantumAttractionEnergy_quantumStatePermutation {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (z : ℕ) (ψ : QuantumState N M q) :
    quantumAttractionEnergy z (quantumStatePermutation σ τ ψ) = quantumAttractionEnergy z ψ := by
  unfold quantumAttractionEnergy
  calc
    _ = ∫⁻ X : QuantumConfiguration N M,
      attraction (fun _ : Fin M => (z : ℝ≥0))
        (fun k => particlePosition (quantumPermutation σ τ X).snd k)
        (quantumPermutation σ τ X).fst * (‖ψ (quantumPermutation σ τ X)‖₊ : ℝ≥0∞)^2 := by
      apply lintegral_congr_ae
      filter_upwards [nnnorm_quantumStatePermutation_ae σ τ ψ] with X hX
      rw [hX, attraction_quantumPermutation]
    _ = _ := (quantumPermutation σ τ).measurePreserving.lintegral_comp_emb
      (quantumPermutation σ τ).toHomeomorph.measurableEmbedding
      (fun X : QuantumConfiguration N M => attraction (fun _ : Fin M => (z : ℝ≥0))
        (fun k => particlePosition X.snd k) X.fst * (‖ψ X‖₊ : ℝ≥0∞)^2)

end LiebThirring
end
