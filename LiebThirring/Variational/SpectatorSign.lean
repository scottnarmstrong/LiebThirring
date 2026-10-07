/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SpectatorVariational
public import LiebThirring.Variational.SpectatorForm
public import LiebThirring.Variational.SlicesSubsetForm

/-! # Variational positivity for the actual residual particle slices -/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.Variational

/-- The variational spectator inequality applies to the actual residual slices, including zero
spin sectors. For `q = 0` the spin sum is empty. -/
theorem residual_spectator_defect_nonneg_ae {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : FormDomain N q)
    (Z : ℝ≥0) (E : ℝ) (hE : E ≤ (atomicGroundStateEnergy k q Z).toReal) :
    ∀ᵐ x : Position, 0 ≤ ∑ s : Fin q,
      (fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (residualParticleSlice i e (u : State N q) x s) -
        E * ‖residualParticleSlice i e (u : State N q) x s‖ ^ 2) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst q
    simp
  filter_upwards [residualParticleFormSlice_ae i e (u : State N q) u.property.1
    u.property.2] with x hx
  apply Finset.sum_nonneg
  intro s _
  rw [← hx s, fullRealEnergy_eq_realEnergy _ _ atomicPositionInjective]
  exact atomic_spectator_defect_nonneg q hq k Z E hE
    (residualParticleFormSlice i e (u : State N q) x s)

/-- The middle term of the selected-coordinate identity is nonnegative at every energy below
its residual variational threshold. -/
theorem integral_residual_spectator_defect_nonneg {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : FormDomain N q)
    (Z : ℝ≥0) (E : ℝ) (hE : E ≤ (atomicGroundStateEnergy k q Z).toReal)
    (b : Position → ℝ) (hb0 : ∀ x, 0 ≤ b x) :
    0 ≤ ∫ x : Position, b x * ∑ s : Fin q,
      (fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (residualParticleSlice i e (u : State N q) x s) -
        E * ‖residualParticleSlice i e (u : State N q) x s‖ ^ 2) := by
  apply integral_nonneg_of_ae
  filter_upwards [residual_spectator_defect_nonneg_ae i e u Z E hE] with x hx
  exact mul_nonneg (hb0 x) hx

end LiebThirring.Variational
end
