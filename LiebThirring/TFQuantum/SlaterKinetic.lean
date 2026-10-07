/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFQuantum.SlaterFourier
public import LiebThirring.TFQuantum.SlaterOneBody
public import LiebThirring.TFQuantum.SlaterCoulombFinite

/-! # The kinetic energy as a Fourier density test

This identity holds on the entire L² carrier, including infinite
kinetic energy. It reduces a Slater kinetic identity to the one-body density
identity and the Fourier covariance of the determinant construction.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal FourierTransform
namespace LiebThirring

/-- The literal kinetic integral is the density test of the Fourier state. -/
theorem kineticEnergy_eq_density_fourier {N q : ℕ} (ψ : State N q) :
    kineticEnergy ψ = ∫⁻ x : Position,
      (ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖x‖₊ : ℝ≥0∞) ^ 2) * density (𝓕 ψ) x := by
  rw [density_testing N q (𝓕 ψ) (fun x => ENNReal.ofReal ((2 * Real.pi) ^ 2) *
    (‖x‖₊ : ℝ≥0∞) ^ 2)
      (measurable_const.mul (measurable_id.nnnorm.coe_nnreal_ennreal.pow_const 2))]
  exact kineticEnergy_eq_sum_particleFourierEnergy ψ

/-- The one-orbital kinetic integral in literal three-dimensional coordinates. -/
theorem kineticEnergy_one_eq_spatial_integral {q : ℕ} (u : State 1 q) :
    kineticEnergy u = ∫⁻ x : Position,
      (ENNReal.ofReal ((2 * Real.pi)^2) * (‖x‖₊ : ℝ≥0∞)^2) *
        (‖(𝓕 u) (oneParticleConfiguration x)‖₊ : ℝ≥0∞)^2 := by
  have hmp : MeasurePreserving (oneParticleConfigurationEquiv : Position → Configuration 1)
      volume volume := oneParticleConfigurationEquiv.measurePreserving
  have hf : Measurable (fun X : Configuration 1 =>
      ENNReal.ofReal ((2 * Real.pi)^2) * (‖X‖₊ : ℝ≥0∞)^2 *
        (‖(𝓕 u) X‖₊ : ℝ≥0∞)^2) :=
    (measurable_const.mul (measurable_id.nnnorm.coe_nnreal_ennreal.pow_const 2)).mul
      (measurable_state_norm_sq (𝓕 u))
  have h := hmp.lintegral_comp hf
  have hn (x : Position) : ‖oneParticleConfiguration x‖₊ = ‖x‖₊ :=
    oneParticleConfigurationEquiv.nnnorm_map x
  change (∫⁻ X : Configuration 1, ENNReal.ofReal ((2 * Real.pi)^2) *
    (‖X‖₊ : ℝ≥0∞)^2 * (‖(𝓕 u) X‖₊ : ℝ≥0∞)^2) = _
  have heval (x : Position) : oneParticleConfigurationEquiv x = oneParticleConfiguration x := rfl
  simpa only [heval, hn] using h.symm

/-- The actual Slater determinant has the sum of the orbital kinetic energies.
The identity also permits infinite kinetic energies. -/
theorem kineticEnergy_slaterState {N q : ℕ} (u : Fin N → State 1 q)
    (hu : Orthonormal ℂ u) :
    kineticEnergy (slaterState u) = ∑ j : Fin N, kineticEnergy (u j) := by
  have hfu : Orthonormal ℂ (fun j => 𝓕 (u j)) :=
    hu.comp_linearIsometryEquiv (Lp.fourierTransformₗᵢ (Configuration 1) (SpinAmplitudes 1 q))
  rw [kineticEnergy_eq_density_fourier, fourier_slaterState,
    density_slaterState_testing _ hfu]
  simp_rw [ofReal_slaterOrbitalDensity, Finset.mul_sum]
  have hm (j : Fin N) : Measurable (fun x : Position =>
      (ENNReal.ofReal ((2 * Real.pi)^2) * (‖x‖₊ : ℝ≥0∞)^2) *
        (‖(𝓕 (u j)) (oneParticleConfiguration x)‖₊ : ℝ≥0∞)^2) :=
    (measurable_const.mul (measurable_id.nnnorm.coe_nnreal_ennreal.pow_const 2)).mul
      (((Lp.stronglyMeasurable (𝓕 (u j))).measurable.comp
        continuous_oneParticleConfiguration.measurable).nnnorm.coe_nnreal_ennreal.pow_const 2)
  rw [lintegral_finsetSum Finset.univ (fun j _ => hm j)]
  exact Finset.sum_congr rfl (fun j _ => (kineticEnergy_one_eq_spatial_integral (u j)).symm)

/-- Every orthonormal finite family of finite-kinetic orbitals gives a finite-kinetic Slater state. -/
theorem kineticEnergy_slaterState_lt_top {N q : ℕ} (u : Fin N → State 1 q)
    (hu : Orthonormal ℂ u) (hT : ∀ j, kineticEnergy (u j) < ⊤) :
    kineticEnergy (slaterState u) < ⊤ := by
  rw [kineticEnergy_slaterState u hu]
  exact ENNReal.sum_lt_top.mpr (fun j _ => hT j)

end LiebThirring
end
