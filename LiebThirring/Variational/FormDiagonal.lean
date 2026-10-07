/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormPairBounds
public import LiebThirring.Variational.EnergyForm
public import LiebThirring.Variational.RealEnergy

/-! # Integrability and diagonal of the energy form

Form polarization: each literal integral is absolutely integrable and the diagonal agrees
with the unnormalized real energy. All extended expectations are finite.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring
open Assembly

/-- The real Fourier kinetic weight is the finite extended weight's real value. -/
theorem formKineticWeight_toReal {N : ℕ} (ξ : Configuration N) :
    (ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2).toReal =
      (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm]

/-- Absolute integrability of the Fourier kinetic integrand. -/
theorem integrable_energyForm_kinetic {N q : ℕ} (φ ψ : FormDomain N q) :
    Integrable (fun ξ : Configuration N =>
      (((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * inner ℂ
        ((Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) (φ : State N q)) ξ)
        ((Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) (ψ : State N q)) ξ)) := by
  have hp : Measurable (fun ξ : Configuration N =>
      ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2) :=
    measurable_const.mul (measurable_id.nnnorm.coe_nnreal_ennreal.pow_const 2)
  simpa only [formKineticWeight_toReal] using
    (integrable_weight_inner hp.aemeasurable
      (Lp.aestronglyMeasurable (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)
        (φ : State N q)))
      (Lp.aestronglyMeasurable (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)
        (ψ : State N q))) φ.property.2 ψ.property.2)

/-- Absolute integrability of the repulsive potential integrand. -/
theorem integrable_energyForm_repulsion {N q : ℕ} (φ ψ : FormDomain N q) :
    Integrable (fun X : Configuration N =>
      ((electronRepulsion X).toReal : ℂ) *
        inner ℂ ((φ : State N q) X) ((ψ : State N q) X)) :=
  integrable_weight_inner measurable_electronRepulsion.aemeasurable
    (Lp.aestronglyMeasurable (φ : State N q)) (Lp.aestronglyMeasurable (ψ : State N q))
    (lintegral_electronRepulsion_lt_top (φ : State N q) φ.property.2)
    (lintegral_electronRepulsion_lt_top (ψ : State N q) ψ.property.2)

/-- Absolute integrability of the attractive potential integrand. -/
theorem integrable_energyForm_attraction {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (φ ψ : FormDomain N q) :
    Integrable (fun X : Configuration N =>
      ((attraction z R X).toReal : ℂ) *
        inner ℂ ((φ : State N q) X) ((ψ : State N q) X)) :=
  integrable_weight_inner (measurable_attraction z R).aemeasurable
    (Lp.aestronglyMeasurable (φ : State N q)) (Lp.aestronglyMeasurable (ψ : State N q))
    (lintegral_attraction_lt_top z R (φ : State N q) φ.property.2)
    (lintegral_attraction_lt_top z R (ψ : State N q) ψ.property.2)

/-- Absolute integrability of the literal signed Coulomb potential integrand. -/
theorem integrable_energyForm_potential {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (φ ψ : FormDomain N q) :
    Integrable (fun X : Configuration N =>
      (((electronRepulsion X).toReal - (attraction z R X).toReal : ℝ) : ℂ) *
        inner ℂ ((φ : State N q) X) ((ψ : State N q) X)) := by
  apply ((integrable_energyForm_repulsion φ ψ).sub
    (integrable_energyForm_attraction z R φ ψ)).congr
  apply Filter.Eventually.of_forall
  intro X
  dsimp only [Pi.sub_apply]
  rw [Complex.ofReal_sub, sub_mul]

/-- The diagonal kinetic integral is the finite Fourier kinetic energy. -/
theorem integral_energyForm_kinetic_self {N q : ℕ} (ψ : FormDomain N q) :
    (∫ ξ : Configuration N, (((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * inner ℂ
      ((Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) (ψ : State N q)) ξ)
      ((Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) (ψ : State N q)) ξ)) =
      ((kineticEnergy (ψ : State N q)).toReal : ℂ) := by
  have hp : Measurable (fun ξ : Configuration N =>
      ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2) :=
    measurable_const.mul (measurable_id.nnnorm.coe_nnreal_ennreal.pow_const 2)
  simpa only [formKineticWeight_toReal, kineticEnergy, mul_assoc] using
    (integral_weight_inner_self hp.aemeasurable
      (Lp.aestronglyMeasurable (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)
        (ψ : State N q))) ψ.property.2)

/-- Exact diagonal identity for the literal complex form and real energy. -/
theorem energyForm_self {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (ψ : FormDomain N q) :
    energyForm z R hR ψ ψ = (realEnergy z R hR ψ : ℂ) := by
  unfold energyForm realEnergy
  rw [integral_energyForm_kinetic_self]
  simp_rw [Complex.ofReal_sub, sub_mul]
  rw [integral_sub (integrable_energyForm_repulsion ψ ψ)
    (integrable_energyForm_attraction z R ψ ψ),
    integral_weight_inner_self measurable_electronRepulsion.aemeasurable
      (Lp.aestronglyMeasurable (ψ : State N q))
      (lintegral_electronRepulsion_lt_top (ψ : State N q) ψ.property.2),
    integral_weight_inner_self (measurable_attraction z R).aemeasurable
      (Lp.aestronglyMeasurable (ψ : State N q))
      (lintegral_attraction_lt_top z R (ψ : State N q) ψ.property.2),
    inner_self_eq_norm_sq_to_K]
  push_cast
  abel

end LiebThirring
end
