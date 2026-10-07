/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.FormDensity
public import LiebThirring.Kinetic.FourierFactor

/-!
# Permutation invariance of the Fourier graph seminorm

Simultaneous spatial and spin permutations are isometries for mass and for the
radial Fourier graph seminorm. These bounds control antisymmetrization of a
compact smooth approximation.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal SchwartzMap FourierTransform

namespace LiebThirring.Sobolev

/-- Simultaneous permutation as a bounded complex linear map on the state carrier. -/
@[expose] noncomputable def permutationStateCLM {N q : ℕ} (σ : Equiv.Perm (Fin N)) :
    State N q →L[ℂ] State N q :=
  ((spinPermutationLinearIsometryEquiv (q := q) σ).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 volume).comp ((Lp.compMeasurePreservingₗᵢ ℂ (permutationLinearIsometryEquiv σ)
      (permutationLinearIsometryEquiv σ).measurePreserving).toContinuousLinearMap)

/-- A simultaneous permutation has the intended spin-valued representative. -/
theorem simultaneousPermutation_amplitude_ae {N q : ℕ} (σ : Equiv.Perm (Fin N)) (u : State N q) :
    (simultaneousPermutation σ u : Configuration N → SpinAmplitudes N q) =ᵐ[volume]
      (fun x => spinPermutationLinearIsometryEquiv σ (u (permutePositions σ x))) := by
  filter_upwards [simultaneousPermutation_apply_ae σ u] with x hx
  ext s
  exact hx s

/-- Simultaneous permutations preserve the L² norm. -/
theorem norm_simultaneousPermutation {N q : ℕ} (σ : Equiv.Perm (Fin N)) (u : State N q) :
    ‖simultaneousPermutation σ u‖ = ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae (simultaneousPermutation_amplitude_ae σ u)]
  have ha := (Lp.aestronglyMeasurable u).comp_measurePreserving
    (measurePreserving_permutePositions σ)
  calc
    _ = eLpNorm (fun x => u (permutePositions σ x)) 2 volume := by
      exact eLpNorm_congr_norm_ae
        ((spinPermutationLinearIsometryEquiv σ).continuous.comp_aestronglyMeasurable ha) ha
        (Filter.Eventually.of_forall (fun x => (spinPermutationLinearIsometryEquiv σ).norm_map _))
    _ = _ := eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable u)
      (measurePreserving_permutePositions σ)

/-- Simultaneous particle permutations preserve the Fourier kinetic energy. -/
theorem kineticEnergy_simultaneousPermutation {N q : ℕ} (σ : Equiv.Perm (Fin N)) (u : State N q) :
    kineticEnergy (simultaneousPermutation σ u) = kineticEnergy u := by
  unfold kineticEnergy
  change (∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
    (‖(𝓕 (simultaneousPermutation σ u) : State N q) ξ‖₊ : ℝ≥0∞) ^ 2) = _
  rw [fourier_simultaneousPermutation]
  calc
    _ = ∫⁻ ξ : Configuration N, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        (‖permutePositions σ ξ‖₊ : ℝ≥0∞) ^ 2 *
        (‖(𝓕 u : State N q) (permutePositions σ ξ)‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [simultaneousPermutation_amplitude_ae σ (𝓕 u)] with ξ hξ
      rw [hξ]
      have ht : ‖spinPermutationLinearIsometryEquiv σ
          ((𝓕 u : State N q) (permutePositions σ ξ))‖₊ =
          ‖(𝓕 u : State N q) (permutePositions σ ξ)‖₊ :=
        NNReal.coe_injective ((spinPermutationLinearIsometryEquiv σ).norm_map _)
      have hx : ‖permutePositions σ ξ‖₊ = ‖ξ‖₊ :=
        NNReal.coe_injective ((permutationLinearIsometryEquiv σ).norm_map ξ)
      rw [ht, hx]
    _ = _ := (measurePreserving_permutePositions σ).lintegral_comp_emb
      (measurableEmbedding_permutePositions σ)
      (fun ξ : Configuration N => ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        (‖ξ‖₊ : ℝ≥0∞) ^ 2 * (‖(𝓕 u : State N q) ξ‖₊ : ℝ≥0∞) ^ 2)

/-- Simultaneous permutations preserve the radial Fourier graph seminorm. -/
theorem fourierGraphSeminorm_simultaneousPermutation {N q : ℕ} (σ : Equiv.Perm (Fin N))
    (u : State N q) : fourierGraphSeminorm (simultaneousPermutation σ u) =
      fourierGraphSeminorm u := by
  unfold fourierGraphSeminorm
  rw [radialFourier_eLpNorm_eq, radialFourier_eLpNorm_eq, kineticEnergy_simultaneousPermutation]

/-- Scalar multiplication scales the radial Fourier graph seminorm by scalar modulus. -/
theorem fourierGraphSeminorm_smul {N q : ℕ} (c : ℂ) (u : State N q) :
    fourierGraphSeminorm (c • u) = ENNReal.ofReal ‖c‖ * fourierGraphSeminorm u := by
  unfold fourierGraphSeminorm radialFourierMeasure
  rw [FourierTransform.fourier_smul,
    eLpNorm_congr_ae ((withDensity_absolutelyContinuous _ _).ae_eq (Lp.coeFn_smul c (𝓕 u))),
    eLpNorm_const_smul, ofReal_norm]

/-- The radial Fourier graph seminorm is subadditive under finite sums. -/
theorem fourierGraphSeminorm_sum_le {N q : ℕ} {ι : Type*} (s : Finset ι) (u : ι → State N q) :
    fourierGraphSeminorm (∑ i ∈ s, u i) ≤ ∑ i ∈ s, fourierGraphSeminorm (u i) := by
  unfold fourierGraphSeminorm radialFourierMeasure
  have hF : (𝓕 (∑ i ∈ s, u i) : State N q) = ∑ i ∈ s, (𝓕 (u i) : State N q) :=
    map_sum (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)) u s
  rw [hF, eLpNorm_congr_ae ((withDensity_absolutelyContinuous _ _).ae_eq
    (Lp.coeFn_finsetSum s (fun i => (𝓕 (u i) : State N q))))]
  exact eLpNorm_sum_le (by norm_num)

/-- Simultaneous permutation of a Schwartz state. -/
@[expose] noncomputable def permuteSchwartz {N q : ℕ} (σ : Equiv.Perm (Fin N))
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) : 𝓢(Configuration N, SpinAmplitudes N q) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (permutationLinearIsometryEquiv σ).toContinuousLinearEquiv f).postcompCLM
      (spinPermutationLinearIsometryEquiv σ).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem permuteSchwartz_apply {N q : ℕ} (σ : Equiv.Perm (Fin N))
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (x : Configuration N) :
    permuteSchwartz σ f x = spinPermutationLinearIsometryEquiv σ (f (permutePositions σ x)) := by
  rw [permuteSchwartz, SchwartzMap.postcompCLM_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rfl

/-- A Schwartz simultaneous permutation represents the corresponding state permutation. -/
theorem permuteSchwartz_toLp {N q : ℕ} (σ : Equiv.Perm (Fin N))
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    (permuteSchwartz σ f).toLp 2 volume = simultaneousPermutation σ (f.toLp 2 volume) := by
  unfold simultaneousPermutation
  rw [Fourier.compMeasurePreserving_toLp, Fourier.compLp_toLp]
  rfl

/-- Simultaneous permutations preserve spatial compact support. -/
theorem permuteSchwartz_hasCompactSupport {N q : ℕ} (σ : Equiv.Perm (Fin N))
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (hf : HasCompactSupport f) :
    HasCompactSupport (permuteSchwartz σ f) := by
  have h := (hf.comp_homeomorph (permutationLinearIsometryEquiv σ).toHomeomorph).comp_left
    (spinPermutationLinearIsometryEquiv (q := q) σ).map_zero
  exact h

end LiebThirring.Sobolev

end
