/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.ThermoClusters.FourierMotion
public import LiebThirring.Thermodynamic.QuantumElectronKineticEnergy
public import LiebThirring.Thermodynamic.QuantumNuclearKineticEnergy
/-!
# Rigid invariance of both joint Fourier kinetic energies

The electronic and nuclear frequency-block norms are preserved by simultaneous
orthogonal rotation. Translation changes the Fourier transform only by a unit
complex phase. Consequently both energies are invariant for every
correlated L² state, including states of infinite energy and empty sectors.

-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform
namespace LiebThirring

private theorem nnnorm_quantumRotation_symm_fst {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (ξ : QuantumConfiguration N M) :
    ‖((quantumRotation Q).symm ξ).fst‖₊ = ‖ξ.fst‖₊ := by
  change ‖(configurationRotation Q).symm ξ.fst‖₊ = ‖ξ.fst‖₊
  exact (configurationRotation Q).symm.nnnorm_map ξ.fst

private theorem nnnorm_quantumRotation_symm_snd {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (ξ : QuantumConfiguration N M) :
    ‖((quantumRotation Q).symm ξ).snd‖₊ = ‖ξ.snd‖₊ := by
  change ‖(configurationRotation Q).symm ξ.snd‖₊ = ‖ξ.snd‖₊
  exact (configurationRotation Q).symm.nnnorm_map ξ.snd

private theorem lintegral_comp_quantumRotation_symm {N M : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (f : QuantumConfiguration N M → ℝ≥0∞) :
    (∫⁻ ξ, f ((quantumRotation Q).symm ξ)) = ∫⁻ ξ, f ξ :=
  (quantumRotation (N := N) (M := M) Q).symm.measurePreserving.lintegral_comp_emb
    (quantumRotation (N := N) (M := M) Q).symm.toHomeomorph.measurableEmbedding f

private theorem electron_kinetic_change_of_variables {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (φ : QuantumState N M q) :
    (∫⁻ ξ : QuantumConfiguration N M,
      ENNReal.ofReal ((2 * Real.pi)^2) *
        (‖((quantumRotation Q).symm ξ).fst‖₊ : ℝ≥0∞)^2 *
        (‖φ ((quantumRotation Q).symm ξ)‖₊ : ℝ≥0∞)^2) =
    ∫⁻ ξ : QuantumConfiguration N M,
      ENNReal.ofReal ((2 * Real.pi)^2) * (‖ξ.fst‖₊ : ℝ≥0∞)^2 *
        (‖φ ξ‖₊ : ℝ≥0∞)^2 := by
  exact lintegral_comp_quantumRotation_symm (N := N) (M := M) Q
    (fun ξ : QuantumConfiguration N M => ENNReal.ofReal ((2 * Real.pi)^2) *
      (‖ξ.fst‖₊ : ℝ≥0∞)^2 * (‖φ ξ‖₊ : ℝ≥0∞)^2)

private theorem nuclear_kinetic_change_of_variables {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (φ : QuantumState N M q) :
    (∫⁻ ξ : QuantumConfiguration N M,
      ENNReal.ofReal ((2 * Real.pi)^2) *
        (‖((quantumRotation Q).symm ξ).snd‖₊ : ℝ≥0∞)^2 *
        (‖φ ((quantumRotation Q).symm ξ)‖₊ : ℝ≥0∞)^2) =
    ∫⁻ ξ : QuantumConfiguration N M,
      ENNReal.ofReal ((2 * Real.pi)^2) * (‖ξ.snd‖₊ : ℝ≥0∞)^2 *
        (‖φ ξ‖₊ : ℝ≥0∞)^2 := by
  exact lintegral_comp_quantumRotation_symm (N := N) (M := M) Q
    (fun ξ : QuantumConfiguration N M => ENNReal.ofReal ((2 * Real.pi)^2) *
      (‖ξ.snd‖₊ : ℝ≥0∞)^2 * (‖φ ξ‖₊ : ℝ≥0∞)^2)

/-- Simultaneous rigid motion preserves the electronic Fourier kinetic energy,
including the value infinity. -/
theorem quantumElectronKineticEnergy_quantumStateMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumState N M q) :
    quantumElectronKineticEnergy (quantumStateMotion Q c ψ) =
      quantumElectronKineticEnergy ψ := by
  unfold quantumElectronKineticEnergy
  change (∫⁻ ξ : QuantumConfiguration N M,
    ENNReal.ofReal ((2 * Real.pi)^2) * (‖ξ.fst‖₊ : ℝ≥0∞)^2 *
      (‖(𝓕 (quantumStateMotion Q c ψ)) ξ‖₊ : ℝ≥0∞)^2) =
    ∫⁻ ξ : QuantumConfiguration N M,
    ENNReal.ofReal ((2 * Real.pi)^2) * (‖ξ.fst‖₊ : ℝ≥0∞)^2 *
      (‖(𝓕 ψ) ξ‖₊ : ℝ≥0∞)^2
  refine Eq.trans (b := ∫⁻ ξ : QuantumConfiguration N M,
    ENNReal.ofReal ((2 * Real.pi)^2) *
      (‖((quantumRotation Q).symm ξ).fst‖₊ : ℝ≥0∞)^2 *
      (‖(𝓕 ψ) ((quantumRotation Q).symm ξ)‖₊ : ℝ≥0∞)^2)
    ?_ (electron_kinetic_change_of_variables Q (𝓕 ψ))
  apply lintegral_congr_ae
  filter_upwards [nnnorm_fourier_quantumStateMotion_ae Q c ψ] with ξ hξ
  rw [hξ, nnnorm_quantumRotation_symm_fst]

/-- Simultaneous rigid motion preserves the nuclear Fourier kinetic energy,
including the value infinity. -/
theorem quantumNuclearKineticEnergy_quantumStateMotion {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumState N M q) :
    quantumNuclearKineticEnergy (quantumStateMotion Q c ψ) =
      quantumNuclearKineticEnergy ψ := by
  unfold quantumNuclearKineticEnergy
  change (∫⁻ ξ : QuantumConfiguration N M,
    ENNReal.ofReal ((2 * Real.pi)^2) * (‖ξ.snd‖₊ : ℝ≥0∞)^2 *
      (‖(𝓕 (quantumStateMotion Q c ψ)) ξ‖₊ : ℝ≥0∞)^2) =
    ∫⁻ ξ : QuantumConfiguration N M,
    ENNReal.ofReal ((2 * Real.pi)^2) * (‖ξ.snd‖₊ : ℝ≥0∞)^2 *
      (‖(𝓕 ψ) ξ‖₊ : ℝ≥0∞)^2
  refine Eq.trans (b := ∫⁻ ξ : QuantumConfiguration N M,
    ENNReal.ofReal ((2 * Real.pi)^2) *
      (‖((quantumRotation Q).symm ξ).snd‖₊ : ℝ≥0∞)^2 *
      (‖(𝓕 ψ) ((quantumRotation Q).symm ξ)‖₊ : ℝ≥0∞)^2)
    ?_ (nuclear_kinetic_change_of_variables Q (𝓕 ψ))
  apply lintegral_congr_ae
  filter_upwards [nnnorm_fourier_quantumStateMotion_ae Q c ψ] with ξ hξ
  rw [hξ, nnnorm_quantumRotation_symm_snd]

end LiebThirring
end
