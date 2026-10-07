/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormDiagonal
public import LiebThirring.Sobolev.WeakBilinear
public import LiebThirring.Sobolev.WeakEnergy

/-!
# The symmetry-free form used in the spectator identity

Spectator disintegration uses a one-coordinate multiplier, which
need not preserve antisymmetry. The literal form below has the same integrals
as the form. Its integrability and weak-gradient representation require
only finite kinetic energy, and never require symmetry of the first argument.
-/

public section
open MeasureTheory
open scoped FourierTransform ENNReal NNReal

namespace LiebThirring

/-- The literal molecular quadratic form on the full state space. Its
finite-energy restriction is the symmetry-free form needed for spectator disintegration. -/
@[expose] noncomputable def fullEnergyForm {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (φ ψ : State N q) : ℂ :=
  (∫ ξ : Configuration N, (((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
    inner ℂ ((𝓕 φ) ξ) ((𝓕 ψ) ξ)) +
  (∫ X : Configuration N,
    (((electronRepulsion X).toReal - (attraction z R X).toReal : ℝ) : ℂ) *
      inner ℂ (φ X) (ψ X)) +
  ((nuclearRepulsion z R).toReal : ℂ) * inner ℂ φ ψ

/-- The literal unnormalized real energy without a symmetry restriction. -/
@[expose] noncomputable def fullRealEnergy {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ψ : State N q) : ℝ :=
  (kineticEnergy ψ).toReal +
  (∫⁻ X : Configuration N, electronRepulsion X * ‖ψ X‖ₑ ^ 2).toReal +
  (nuclearRepulsion z R).toReal * ‖ψ‖ ^ 2 -
  (∫⁻ X : Configuration N, attraction z R X * ‖ψ X‖ₑ ^ 2).toReal

/-- Restriction agrees with the exact real energy. -/
theorem fullRealEnergy_eq_realEnergy {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (ψ : FormDomain N q) :
    fullRealEnergy z R (ψ : State N q) = realEnergy z R hR ψ := rfl

/-- Absolute integrability of the repulsive pairing on the full finite-energy domain. -/
theorem integrable_fullEnergyForm_repulsion {N q : ℕ} (φ ψ : State N q)
    (hφ : kineticEnergy φ < ⊤) (hψ : kineticEnergy ψ < ⊤) :
    Integrable (fun X : Configuration N =>
      ((electronRepulsion X).toReal : ℂ) * inner ℂ (φ X) (ψ X)) :=
  integrable_weight_inner Assembly.measurable_electronRepulsion.aemeasurable
    (Lp.aestronglyMeasurable φ) (Lp.aestronglyMeasurable ψ)
    (lintegral_electronRepulsion_lt_top φ hφ) (lintegral_electronRepulsion_lt_top ψ hψ)

/-- Absolute integrability of the attractive pairing on the full finite-energy domain. -/
theorem integrable_fullEnergyForm_attraction {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (φ ψ : State N q)
    (hφ : kineticEnergy φ < ⊤) (hψ : kineticEnergy ψ < ⊤) :
    Integrable (fun X : Configuration N =>
      ((attraction z R X).toReal : ℂ) * inner ℂ (φ X) (ψ X)) :=
  integrable_weight_inner (measurable_attraction z R).aemeasurable
    (Lp.aestronglyMeasurable φ) (Lp.aestronglyMeasurable ψ)
    (lintegral_attraction_lt_top z R φ hφ) (lintegral_attraction_lt_top z R ψ hψ)

/-- The signed potential pairing is absolutely integrable before any subtraction. -/
theorem integrable_fullEnergyForm_potential {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (φ ψ : State N q)
    (hφ : kineticEnergy φ < ⊤) (hψ : kineticEnergy ψ < ⊤) :
    Integrable (fun X : Configuration N =>
      (((electronRepulsion X).toReal - (attraction z R X).toReal : ℝ) : ℂ) *
        inner ℂ (φ X) (ψ X)) := by
  apply ((integrable_fullEnergyForm_repulsion φ ψ hφ hψ).sub
    (integrable_fullEnergyForm_attraction z R φ ψ hφ hψ)).congr
  filter_upwards [] with X
  dsimp only [Pi.sub_apply]
  rw [Complex.ofReal_sub, sub_mul]

/-- All three literal terms are meaningful on the full finite-energy domain. -/
theorem integrable_fullEnergyForm_kinetic {N q : ℕ} (φ ψ : State N q)
    (hφ : kineticEnergy φ < ⊤) (hψ : kineticEnergy ψ < ⊤) :
    Integrable (fun ξ : Configuration N =>
      (((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * inner ℂ ((𝓕 φ) ξ) ((𝓕 ψ) ξ)) := by
  obtain ⟨dφ, hdφ⟩ := Sobolev.exists_weakDerivatives_of_kineticEnergy_lt_top φ hφ
  obtain ⟨dψ, hdψ⟩ := Sobolev.exists_weakDerivatives_of_kineticEnergy_lt_top ψ hψ
  exact Sobolev.integrable_fourier_inner_of_weakDerivatives ψ φ dψ dφ hdψ hdφ

/-- The symmetry-free form has the physical weak-gradient representation. -/
theorem fullEnergyForm_eq_weakDerivatives {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (φ ψ : State N q)
    (dφ dψ : (Fin N × Fin 3) → State N q)
    (hφ : ∀ a, Sobolev.HasWeakDerivative a φ (dφ a))
    (hψ : ∀ a, Sobolev.HasWeakDerivative a ψ (dψ a)) :
    fullEnergyForm z R φ ψ =
      (∑ a : Fin N × Fin 3, inner ℂ (dφ a) (dψ a)) +
      (∫ X : Configuration N,
        (((electronRepulsion X).toReal - (attraction z R X).toReal : ℝ) : ℂ) *
          inner ℂ (φ X) (ψ X)) +
      ((nuclearRepulsion z R).toReal : ℂ) * inner ℂ φ ψ := by
  unfold fullEnergyForm
  rw [Sobolev.integral_fourier_inner_eq_sum_weakDerivatives ψ φ dψ dφ hψ hφ]

end LiebThirring
end
