/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoStability.NuclearFibres
public import LiebThirring.Thermodynamic.QuantumElectronKineticEnergy
public import LiebThirring.Thermodynamic.QuantumNuclearKineticEnergy
public import LiebThirring.Defs.KineticEnergy

/-! # Exact disintegration of joint electronic kinetic energy

The equality is extended-valued and holds before imposing
finite energy, antisymmetry, nuclear statistics, or a spatial support condition.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal FourierTransform

namespace LiebThirring.ThermoStability

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

theorem quantumElectronKineticEnergy_eq_fibre_lintegral {N M q : ℕ}
    (ψ : QuantumState N M q) :
    quantumElectronKineticEnergy ψ = ∫⁻ R : Configuration M,
      kineticEnergy (electronFibreField ψ R) := by
  let w : Configuration N → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2
  have hw : Measurable w :=
    measurable_const.mul (measurable_id.nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hfull := lintegral_weight_electronFibreField (𝓕 ψ)
    (fun X : QuantumConfiguration N M => w X.fst)
    (hw.comp (continuous_fst.comp (WithLp.prod_continuous_ofLp ..)).measurable)
  have hswap := blockSwapCurrying_weighted_norm_sq (nuclearFibreField (𝓕 ψ)) w hw
  rw [blockSwap_nuclearFibreField (𝓕 ψ)] at hswap
  have hslice := blockSwapCurrying_fourier_weighted_norm_sq (nuclearFibreField ψ) w hw
  rw [blockSwap_nuclearFibreField ψ] at hslice
  change quantumElectronKineticEnergy ψ = ∫⁻ R : Configuration M, ∫⁻ ξ : Configuration N,
    w ξ * ‖electronFibreField (𝓕 ψ) R ξ‖ₑ ^ 2 at hfull
  calc
    quantumElectronKineticEnergy ψ = ∫⁻ ξ : Configuration N,
        w ξ * ‖nuclearFibreField (𝓕 ψ) ξ‖ₑ ^ 2 := hfull.trans hswap
    _ = ∫⁻ ξ : Configuration N, w ξ *
        ‖(𝓕 (nuclearFibreField ψ) : Lp (Lp (SpinAmplitudes N q) 2
          (volume : Measure (Configuration M))) 2 volume) ξ‖ₑ ^ 2 := by
      rw [nuclearFibreField_fourier]
      exact blockTargetIsometry_weighted_norm_sq
        (Lp.fourierTransformₗᵢ (Configuration M) (SpinAmplitudes N q)) _ w
    _ = ∫⁻ R : Configuration M, kineticEnergy (electronFibreField ψ R) := hslice.symm

/-- The corresponding nuclear-block identity retains the full electronic spin target. -/
theorem quantumNuclearKineticEnergy_eq_fibre_lintegral {N M q : ℕ}
    (ψ : QuantumState N M q) :
    quantumNuclearKineticEnergy ψ = ∫⁻ x : Configuration N, ∫⁻ η : Configuration M,
      ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖η‖₊ : ℝ≥0∞) ^ 2 *
        (‖(Lp.fourierTransformₗᵢ (Configuration M) (SpinAmplitudes N q)
          (nuclearFibreField ψ x)) η‖₊ : ℝ≥0∞) ^ 2 := by
  let w : Configuration M → ℝ≥0∞ := fun η =>
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖η‖₊ : ℝ≥0∞) ^ 2
  have hw : Measurable w :=
    measurable_const.mul (measurable_id.nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hfull := lintegral_weight_electronFibreField (𝓕 ψ)
    (fun X : QuantumConfiguration N M => w X.snd)
    (hw.comp (continuous_snd.comp (WithLp.prod_continuous_ofLp ..)).measurable)
  have hmass : quantumNuclearKineticEnergy ψ = ∫⁻ η : Configuration M,
      w η * ‖electronFibreField (𝓕 ψ) η‖ₑ ^ 2 := by
    refine hfull.trans ?_
    apply lintegral_congr
    intro η
    change (∫⁻ x : Configuration N, w η * ‖electronFibreField (𝓕 ψ) η x‖ₑ ^ 2) = _
    rw [lintegral_const_mul (w η) ((Lp.stronglyMeasurable
      (electronFibreField (𝓕 ψ) η)).enorm.pow_const 2), lintegral_l2_enorm_sq]
  have hslice := blockSwapCurrying_fourier_weighted_norm_sq (electronFibreField ψ) w hw
  rw [blockSwap_electronFibreField ψ] at hslice
  rw [hmass, electronFibreField_fourier, Fourier.fourier_compLp]
  exact (blockTargetIsometry_weighted_norm_sq
    (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q))
      (𝓕 (electronFibreField ψ)) w).trans hslice.symm

end LiebThirring.ThermoStability

end
