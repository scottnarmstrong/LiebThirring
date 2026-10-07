/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SpectatorPairing
public import LiebThirring.Variational.SpectatorSliceEnergy
public import LiebThirring.Variational.SpectatorCoulombSplit
public import LiebThirring.Variational.SpectatorSign

/-! # The atomic selected-coordinate identity

This is argument spectator disintegration, with the real-part correction estimate. The form is evaluated on the full
finite-energy domain because multiplication in one particle coordinate need not preserve
antisymmetry. Every residual spin sector is retained, including vacuum residual states.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.Variational
open Sobolev

/-- The literal residual energy defect is the difference of two absolutely integrable fields. -/
theorem integral_residual_spectator_defect {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (Z : ℝ≥0)
    (u : FormDomain (N + 1) q) (g : (Fin (N + 1) × Fin 3) → State (N + 1) q)
    (hg : ∀ c, HasWeakDerivative c (u : State (N + 1) q) (g c))
    (b : Position → ℝ) (hb : Measurable b) (hb0 : ∀ x, 0 ≤ b x)
    (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) (E : ℝ) :
    (∫ x : Position, b x * ∑ s : Fin q,
      (fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (residualParticleSlice i e (u : State (N + 1) q) x s) -
        E * ‖residualParticleSlice i e (u : State (N + 1) q) x s‖ ^ 2)) =
    (∫ x : Position, b x * ∑ s : Fin q,
      fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (residualParticleSlice i e (u : State (N + 1) q) x s)) -
      E * ∫ x : Position, b x * ∑ s : Fin q,
        ‖residualParticleSlice i e (u : State (N + 1) q) x s‖ ^ 2 := by
  have hfn : (fun x : Position => b x * ∑ s : Fin q,
      (fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (residualParticleSlice i e (u : State (N + 1) q) x s) -
        E * ‖residualParticleSlice i e (u : State (N + 1) q) x s‖ ^ 2)) =
      (fun x => (b x * ∑ s : Fin q,
        fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
          (residualParticleSlice i e (u : State (N + 1) q) x s)) -
        E * (b x * ∑ s : Fin q,
          ‖residualParticleSlice i e (u : State (N + 1) q) x s‖ ^ 2)) := by
    funext x
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hfn, integral_sub
    (integrable_weighted_residual_fullRealEnergy i e Z u g hg b hb hb0 B hB)
    ((integrable_weighted_residual_mass i e (u : State (N + 1) q) b hb hb0 B hB).const_mul E),
    integral_const_mul]

/-- The real part of the full atomic cross form is the selected derivative term, the weighted
residual form defect, and the selected Coulomb interactions. -/
theorem selected_coordinate_identity_of_weakDerivatives {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (Z : ℝ≥0)
    (u : FormDomain (N + 1) q)
    (g G : (Fin (N + 1) × Fin 3) → State (N + 1) q)
    (hg : ∀ c, HasWeakDerivative c (u : State (N + 1) q) (g c))
    (b : Position → ℝ) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) (hb0 : ∀ x, 0 ≤ b x)
    (C : ℝ≥0) (hb : LipschitzWith C b)
    (hG : ∀ c, HasWeakDerivative c
      (lipschitzBoundedSMul (fun X : Configuration (N + 1) => b (particlePosition X i)) B
        (fun X => hB (particlePosition X i)) (lipschitzWith_selected_multiplier i b C hb)
        (u : State (N + 1) q)) (G c)) (E : ℝ) :
    (fullEnergyForm (fun _ : Fin 1 => Z) (fun _ => 0)
      (lipschitzBoundedSMul (fun X : Configuration (N + 1) => b (particlePosition X i)) B
        (fun X => hB (particlePosition X i)) (lipschitzWith_selected_multiplier i b C hb)
        (u : State (N + 1) q)) (u : State (N + 1) q) -
      (E : ℂ) * inner ℂ
        (lipschitzBoundedSMul (fun X : Configuration (N + 1) => b (particlePosition X i)) B
          (fun X => hB (particlePosition X i)) (lipschitzWith_selected_multiplier i b C hb)
          (u : State (N + 1) q)) (u : State (N + 1) q)).re =
      (∑ a : Fin 3, inner ℂ (G (i, a)) (g (i, a))).re +
      (∫ x : Position, b x * ∑ s : Fin q,
        (fullRealEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
          (residualParticleSlice i e (u : State (N + 1) q) x s) -
          E * ‖residualParticleSlice i e (u : State (N + 1) q) x s‖ ^ 2)) +
      ∫ X : Configuration (N + 1), b (particlePosition X i) *
        ((selectedRepulsionKernel i e X).toReal -
          ((Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0).toReal) *
            ‖(u : State (N + 1) q) X‖ ^ 2 := by
  rw [re_fullEnergyForm_selected_multiplier Z i (u : State (N + 1) q) u.property.2
    g G hg b B hB C hb hG E,
    re_sum_inner_weakDerivatives_selected_multiplier i e (u : State (N + 1) q)
      g G hg b B hB hb0 C hb hG,
    ← integral_mul_residualParticleSlice_kineticEnergy_toReal i e (u : State (N + 1) q) g hg b,
    integral_full_weighted_potential_split i e Z u b hb.continuous.measurable hb0 B hB,
    re_inner_lipschitzBoundedSMul_eq_residual_norm i e (u : State (N + 1) q) b B hB hb0 C hb,
    integral_residual_spectator_defect i e Z u g hg b hb.continuous.measurable hb0 B hB E,
    integral_weighted_residual_fullRealEnergy i e Z u g hg b hb.continuous.measurable hb0 B hB]
  ring

end LiebThirring.Variational
end
