/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoStability.KineticFibres
public import LiebThirring.ThermoStability.CoulombFibres

/-! # Measurability and finite-energy electronic fibres -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal FourierTransform

namespace LiebThirring.ThermoStability

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

theorem aemeasurable_field_weighted_norm_sq {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    [SecondCountableTopology (Lp E 2 ν)]
    (u : Lp (Lp E 2 ν) 2 μ) (w : α × β → ℝ≥0∞) (hw : Measurable w) :
    AEMeasurable (fun x => ∫⁻ y, w (x, y) * ‖u x y‖ₑ ^ 2 ∂ν) μ := by
  let f := (l2CurryLinearIsometryEquiv (E := E) (μ := μ) (ν := ν)).symm u
  have hc : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, u x y = f (x, y) := by
    have h := l2Curry_ae f
    rw [show l2Curry f = u from
      (l2CurryLinearIsometryEquiv (E := E) (μ := μ) (ν := ν)).apply_symm_apply u] at h
    exact h
  have hm : Measurable (fun x => ∫⁻ y, w (x, y) * ‖f (x, y)‖ₑ ^ 2 ∂ν) :=
    (hw.mul ((Lp.stronglyMeasurable f).enorm.pow_const 2)).lintegral_prod_right'
  apply hm.aemeasurable.congr
  filter_upwards [hc] with x hx
  exact lintegral_congr_ae (hx.mono fun y hy => congrArg (fun a : E => w (x, y) * ‖a‖ₑ ^ 2) hy.symm)

theorem aemeasurable_electronFibre_kineticEnergy {N M q : ℕ}
    (ψ : QuantumState N M q) :
    AEMeasurable (fun R : Configuration M => kineticEnergy (electronFibreField ψ R)) volume := by
  let F := (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)).toContinuousLinearEquiv.toContinuousLinearMap
  let u := F.compLp (electronFibreField ψ)
  have h := aemeasurable_field_weighted_norm_sq u
    (fun a : Configuration M × Configuration N =>
      ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖a.2‖₊ : ℝ≥0∞) ^ 2)
    (measurable_const.mul (measurable_snd.nnnorm.coe_nnreal_ennreal.pow_const 2))
  apply h.congr
  filter_upwards [F.coeFn_compLp (electronFibreField ψ)] with R hR
  change (∫⁻ ξ : Configuration N, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
    (‖ξ‖₊ : ℝ≥0∞) ^ 2 * ‖u R ξ‖ₑ ^ 2) = kineticEnergy (electronFibreField ψ R)
  rw [show u R = 𝓕 (electronFibreField ψ R) from hR]
  rfl

theorem kineticEnergy_electronFibre_lt_top_ae {N M q : ℕ}
    (ψ : QuantumState N M q) (hψ : quantumElectronKineticEnergy ψ < ⊤) :
    ∀ᵐ R : Configuration M, kineticEnergy (electronFibreField ψ R) < ⊤ := by
  apply ae_lt_top' (aemeasurable_electronFibre_kineticEnergy ψ)
  rw [← quantumElectronKineticEnergy_eq_fibre_lintegral]
  exact hψ.ne

end LiebThirring.ThermoStability

end
