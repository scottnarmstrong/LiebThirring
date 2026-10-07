/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SpectatorEnergy
public import LiebThirring.Variational.SpectatorExpectations
public import LiebThirring.Variational.SpectatorCoulomb
public import LiebThirring.Variational.SlicesSubsetForm
public import LiebThirring.Variational.SpectatorVariational

/-! # Atomic real-energy disintegration through residual particle slices -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.Variational

open Sobolev

/-- Weighted residual atomic real energies are absolutely integrable. -/
theorem integrable_weighted_residual_fullRealEnergy {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (Z : ℝ≥0)
    (u : FormDomain (N + 1) q) (g : (Fin (N + 1) × Fin 3) → State (N + 1) q)
    (hg : ∀ a, HasWeakDerivative a (u : State (N + 1) q) (g a))
    (b : Position → ℝ) (hb : Measurable b) (hb0 : ∀ x, 0 ≤ b x)
    (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) :
    Integrable (fun x : Position => b x * ∑ s : Fin q,
      fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (residualParticleSlice i e (u : State (N + 1) q) x s)) := by
  have hkin := integrable_weighted_residual_kineticEnergy i e (u : State (N + 1) q)
    g hg b hb hb0 B (fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hb0 x)] using hB x)
  have hrep := integrable_weighted_residual_expectation i e (u : State (N + 1) q)
    electronRepulsion Assembly.measurable_electronRepulsion
    (lintegral_residual_repulsion_lt_top i e u) b hb hb0 B hB
  have hattr := integrable_weighted_residual_expectation i e (u : State (N + 1) q)
    (attraction (fun _ : Fin 1 => Z) (fun _ => 0))
    (measurable_attraction _ _) (lintegral_residual_attraction_lt_top i e Z u)
    b hb hb0 B hB
  have hnuc : nuclearRepulsion (fun _ : Fin 1 => Z) (fun _ => (0 : Position)) = 0 := by
    simp [nuclearRepulsion]
  apply (hkin.add hrep).sub hattr |>.congr
  filter_upwards [] with x
  unfold fullRealEnergy
  rw [hnuc]
  simp only [ENNReal.toReal_zero, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, add_zero, mul_add, mul_sub,
    Finset.mul_sum, Pi.add_apply, Pi.sub_apply]

/-- Exact weighted disintegration of the atomic real energy of residual slices. -/
theorem integral_weighted_residual_fullRealEnergy {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (Z : ℝ≥0)
    (u : FormDomain (N + 1) q) (g : (Fin (N + 1) × Fin 3) → State (N + 1) q)
    (hg : ∀ a, HasWeakDerivative a (u : State (N + 1) q) (g a))
    (b : Position → ℝ) (hb : Measurable b) (hb0 : ∀ x, 0 ≤ b x)
    (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) :
    (∫ x : Position, b x * ∑ s : Fin q,
      fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (residualParticleSlice i e (u : State (N + 1) q) x s)) =
      (∫ x : Position, b x * ∑ s : Fin q,
        (kineticEnergy (residualParticleSlice i e (u : State (N + 1) q) x s)).toReal) +
      ∫ X : Configuration (N + 1), b (particlePosition X i) *
        ((electronRepulsion (residualProjection i e X)).toReal -
          (attraction (fun _ : Fin 1 => Z) (fun _ => 0)
            (residualProjection i e X)).toReal) * ‖(u : State (N + 1) q) X‖ ^ 2 := by
  have hkin := integrable_weighted_residual_kineticEnergy i e (u : State (N + 1) q)
    g hg b hb hb0 B (fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hb0 x)] using hB x)
  have hrep := integrable_weighted_residual_expectation i e (u : State (N + 1) q)
    electronRepulsion Assembly.measurable_electronRepulsion
    (lintegral_residual_repulsion_lt_top i e u) b hb hb0 B hB
  have hattr := integrable_weighted_residual_expectation i e (u : State (N + 1) q)
    (attraction (fun _ : Fin 1 => Z) (fun _ => 0)) (measurable_attraction _ _)
    (lintegral_residual_attraction_lt_top i e Z u) b hb hb0 B hB
  have hnuc : nuclearRepulsion (fun _ : Fin 1 => Z) (fun _ => (0 : Position)) = 0 := by
    simp [nuclearRepulsion]
  rw [show (fun x : Position => b x * ∑ s : Fin q,
      fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (residualParticleSlice i e (u : State (N + 1) q) x s)) =
      (fun x => b x * ∑ s : Fin q,
        (kineticEnergy (residualParticleSlice i e (u : State (N + 1) q) x s)).toReal) +
      (fun x => b x * ∑ s : Fin q,
        (∫⁻ y, electronRepulsion y *
          ‖residualParticleSlice i e (u : State (N + 1) q) x s y‖ₑ ^ 2).toReal) -
      (fun x => b x * ∑ s : Fin q,
        (∫⁻ y, attraction (fun _ : Fin 1 => Z) (fun _ => 0) y *
          ‖residualParticleSlice i e (u : State (N + 1) q) x s y‖ₑ ^ 2).toReal) by
        funext x
        unfold fullRealEnergy
        rw [hnuc]
        simp only [ENNReal.toReal_zero, zero_mul, Finset.sum_sub_distrib,
          Finset.sum_add_distrib, add_zero, mul_add, mul_sub,
          Finset.mul_sum]
        simp only [Pi.add_apply, Pi.sub_apply]]
  change (∫ x : Position,
    (b x * ∑ s : Fin q,
      (kineticEnergy (residualParticleSlice i e (u : State (N + 1) q) x s)).toReal) +
      (b x * ∑ s : Fin q, (∫⁻ y, electronRepulsion y *
        ‖residualParticleSlice i e (u : State (N + 1) q) x s y‖ₑ ^ 2).toReal) -
      (b x * ∑ s : Fin q, (∫⁻ y,
        attraction (fun _ : Fin 1 => Z) (fun _ => 0) y *
          ‖residualParticleSlice i e (u : State (N + 1) q) x s y‖ₑ ^ 2).toReal)) = _
  have hkinrep : Integrable (fun x : Position =>
      (b x * ∑ s : Fin q,
        (kineticEnergy (residualParticleSlice i e (u : State (N + 1) q) x s)).toReal) +
      (b x * ∑ s : Fin q, (∫⁻ y, electronRepulsion y *
        ‖residualParticleSlice i e (u : State (N + 1) q) x s y‖ₑ ^ 2).toReal)) :=
    hkin.add hrep
  rw [integral_sub hkinrep hattr, integral_add hkin hrep,
    integral_weighted_residual_expectation i e (u : State (N + 1) q)
      electronRepulsion Assembly.measurable_electronRepulsion
      (lintegral_residual_repulsion_lt_top i e u) b hb hb0 B hB,
    integral_weighted_residual_expectation i e (u : State (N + 1) q)
      (attraction (fun _ : Fin 1 => Z) (fun _ => 0)) (measurable_attraction _ _)
      (lintegral_residual_attraction_lt_top i e Z u) b hb hb0 B hB]
  have hrepFull : Integrable (fun X : Configuration (N + 1) =>
      b (particlePosition X i) * (electronRepulsion (residualProjection i e X)).toReal *
        ‖(u : State (N + 1) q) X‖ ^ 2) := by
    have h := LiebThirring.integrable_weight_norm_sq
      (((hb.comp (measurable_particlePosition i)).ennreal_ofReal.mul
        (Assembly.measurable_electronRepulsion.comp (measurable_residualProjection i e))).aemeasurable)
      (Lp.aestronglyMeasurable (u : State (N + 1) q))
      (lintegral_weighted_residual_repulsion_lt_top i e u b B hB)
    apply h.congr
    filter_upwards [] with X
    simp only [Pi.mul_apply, Function.comp_apply, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (hb0 _)]
  have hattrFull : Integrable (fun X : Configuration (N + 1) =>
      b (particlePosition X i) *
        (attraction (fun _ : Fin 1 => Z) (fun _ => 0)
          (residualProjection i e X)).toReal * ‖(u : State (N + 1) q) X‖ ^ 2) := by
    have h := LiebThirring.integrable_weight_norm_sq
      (((hb.comp (measurable_particlePosition i)).ennreal_ofReal.mul
        ((measurable_attraction (fun _ : Fin 1 => Z) (fun _ => 0)).comp
          (measurable_residualProjection i e))).aemeasurable)
      (Lp.aestronglyMeasurable (u : State (N + 1) q))
      (lintegral_weighted_residual_attraction_lt_top i e Z u b B hB)
    apply h.congr
    filter_upwards [] with X
    simp only [Pi.mul_apply, Function.comp_apply, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (hb0 _)]
  calc
    _ = (∫ x : Position, b x * ∑ s : Fin q,
          (kineticEnergy (residualParticleSlice i e (u : State (N + 1) q) x s)).toReal) +
        ((∫ X : Configuration (N + 1), b (particlePosition X i) *
          (electronRepulsion (residualProjection i e X)).toReal *
            ‖(u : State (N + 1) q) X‖ ^ 2) -
        ∫ X : Configuration (N + 1), b (particlePosition X i) *
          (attraction (fun _ : Fin 1 => Z) (fun _ => 0)
            (residualProjection i e X)).toReal * ‖(u : State (N + 1) q) X‖ ^ 2) := by ring
    _ = _ := by
      rw [← integral_sub hrepFull hattrFull]
      apply congrArg (fun r : ℝ => (∫ x : Position, b x * ∑ s : Fin q,
        (kineticEnergy (residualParticleSlice i e (u : State (N + 1) q) x s)).toReal) + r)
      apply integral_congr_ae
      filter_upwards [] with X
      ring

end LiebThirring.Variational

end
