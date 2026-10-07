/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SlicesWeakRegularity
public import LiebThirring.Variational.SpectatorKinetic

/-! # Selected and residual kinetic-energy disintegration -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal FourierTransform

namespace LiebThirring.Variational

open Sobolev

/-- Pointwise residual kinetic energy is the sum of the squared residual weak derivatives. -/
theorem residualParticleSlice_kineticEnergy_toReal_ae {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) (hg : ∀ a, HasWeakDerivative a u (g a)) :
    ∀ᵐ x : Position, ∀ s : Fin q,
      (kineticEnergy (residualParticleSlice i e u x s)).toReal =
        ∑ a : Fin k × Fin 3,
          ‖residualParticleSlice i e (g ((e a.1).val, a.2)) x s‖ ^ 2 := by
  filter_upwards [hasWeakDerivative_residualParticleSlice_ae i e u g hg] with x hx
  intro s
  exact kineticEnergy_toReal_eq_sum_weakDerivative_norm_sq _ _ (hx s)

/-- The sum of residual kinetic energies is integrable in the selected position. -/
theorem integrable_residualParticleSlice_kineticEnergy_toReal {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) (hg : ∀ a, HasWeakDerivative a u (g a)) :
    Integrable (fun x : Position => ∑ s : Fin q,
      (kineticEnergy (residualParticleSlice i e u x s)).toReal) := by
  have hnorm (j : Fin k) (a : Fin 3) : Integrable (fun x : Position =>
      ∑ s : Fin q, ‖residualParticleSlice i e (g ((e j).val, a)) x s‖ ^ 2) := by
    have hfin : (∫⁻ X : Configuration N,
        (1 : ℝ≥0∞) * ‖g ((e j).val, a) X‖ₑ ^ 2) < ⊤ := by
      simp only [one_mul, lintegral_l2_enorm_sq]
      exact ENNReal.pow_lt_top ENNReal.coe_lt_top
    have hraw := integrable_spectator_reindex_real i e (g ((e j).val, a))
      (fun _ => 1) measurable_const hfin
    apply hraw.congr
    filter_upwards [] with x
    simp only [ENNReal.toReal_one, one_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [integral_state_norm_sq]
  have hsum : Integrable (fun x : Position => ∑ j : Fin k, ∑ a : Fin 3,
      ∑ s : Fin q, ‖residualParticleSlice i e (g ((e j).val, a)) x s‖ ^ 2) :=
    integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun a _ => hnorm j a))
  apply hsum.congr
  filter_upwards [residualParticleSlice_kineticEnergy_toReal_ae i e u g hg] with x hx
  simp_rw [hx]
  simp_rw [Fintype.sum_prod_type]
  calc
    (∑ j : Fin k, ∑ a : Fin 3, ∑ s : Fin q,
        ‖residualParticleSlice i e (g ((e j).val, a)) x s‖ ^ 2) =
        ∑ j : Fin k, ∑ s : Fin q, ∑ a : Fin 3,
          ‖residualParticleSlice i e (g ((e j).val, a)) x s‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

/-- A bounded measurable selected-coordinate weight preserves residual kinetic integrability. -/
theorem integrable_mul_residualParticleSlice_kineticEnergy_toReal {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) (hg : ∀ a, HasWeakDerivative a u (g a))
    (b : Position → ℝ) (hb : Measurable b) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) :
    Integrable (fun x : Position => b x * ∑ s : Fin q,
      (kineticEnergy (residualParticleSlice i e u x s)).toReal) := by
  exact (integrable_residualParticleSlice_kineticEnergy_toReal i e u g hg).bdd_mul
    hb.aestronglyMeasurable (Filter.Eventually.of_forall hB)

/-- Bounded measurable weights may be inserted into the residual kinetic disintegration. -/
theorem integral_mul_residualParticleSlice_kineticEnergy_toReal {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) (hg : ∀ a, HasWeakDerivative a u (g a))
    (b : Position → ℝ) :
    (∫ x : Position, b x * ∑ s : Fin q,
      (kineticEnergy (residualParticleSlice i e u x s)).toReal) =
      ∫ x : Position, b x * ∑ s : Fin q, ∑ j : Fin k, ∑ a : Fin 3,
        ‖residualParticleSlice i e (g ((e j).val, a)) x s‖ ^ 2 := by
  apply integral_congr_ae
  filter_upwards [residualParticleSlice_kineticEnergy_toReal_ae i e u g hg] with x hx
  congr 1
  simp_rw [hx, Fintype.sum_prod_type]

/-- A nonnegative bounded measurable weight gives an integrable residual kinetic-energy field. -/
theorem integrable_weighted_residual_kineticEnergy {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) (hg : ∀ a, HasWeakDerivative a u (g a))
    (b : Position → ℝ) (hb : Measurable b) (hb0 : ∀ x, 0 ≤ b x)
    (B : ℝ) (hB : ∀ x, b x ≤ B) :
    Integrable (fun x : Position => b x * ∑ s : Fin q,
      (kineticEnergy (residualParticleSlice i e u x s)).toReal) := by
  apply integrable_mul_residualParticleSlice_kineticEnergy_toReal i e u g hg b hb B
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (hb0 x)]
  exact hB x

end LiebThirring.Variational

end
