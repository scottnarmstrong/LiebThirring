/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.WeightedH1
public import LiebThirring.Ionization.WeightedSumForm
public import LiebThirring.Ionization.PairInequalityNuclear
public import LiebThirring.Variational.SpectatorIdentity

/-! # Selected repulsion is bounded by the weak defect and the nuclear cost -/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring
open Sobolev Variational

/-- spectator disintegration and weighted H¹ positivity bound the selected repulsion at the escape threshold.
The selected weighted state need not be antisymmetric. -/
theorem integral_ionization_selected_repulsion_le_defect {N q : ℕ}
    (ε : ℝ) (hε : 0 < ε) (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (Z : ℝ≥0)
    (E : ℝ) (hE : E ≤ (atomicGroundStateEnergy N q Z).toReal)
    (u : FormDomain (N + 1) q) :
    (∫ X : Configuration (N + 1), ionizationWeight ε ‖particlePosition X i‖ *
      (selectedRepulsionKernel i e X).toReal * ‖(u : State (N + 1) q) X‖ ^ 2) ≤
      (fullEnergyForm (fun _ : Fin 1 => Z) (fun _ => 0)
        (ionizationParticleState ε hε i (u : State (N + 1) q))
        (u : State (N + 1) q) -
        (E : ℂ) * inner ℂ (ionizationParticleState ε hε i (u : State (N + 1) q))
          (u : State (N + 1) q)).re + (Z : ℝ) * ‖(u : State (N + 1) q)‖ ^ 2 := by
  let b : Position → ℝ := fun x => ionizationWeight ε ‖x‖
  have hb0 (x : Position) : 0 ≤ b x := ionizationWeight_nonneg hε.le (norm_nonneg _)
  have hB (x : Position) : ‖b x‖ ≤ ε⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hb0 x)]
    exact ionizationWeight_le_inv hε (norm_nonneg _)
  have hb : LipschitzWith 1 b := lipschitzWith_ionizationWeight hε.le
  obtain ⟨g, hg⟩ := exists_weakDerivatives_of_kineticEnergy_lt_top
    (u : State (N + 1) q) u.property.2
  let G := fun a => lipschitzProductDerivative (fun X => b (particlePosition X i))
    ε⁻¹ (fun _X => hB _) 1 (lipschitzWith_selected_multiplier i b 1 hb)
    a (u : State (N + 1) q) (g a)
  have hG := hasWeakDerivative_lipschitz_product (u : State (N + 1) q) g hg
    (fun X => b (particlePosition X i)) ε⁻¹ (fun _X => hB _) 1
    (lipschitzWith_selected_multiplier i b 1 hb)
  have hid := selected_coordinate_identity_of_weakDerivatives i e Z u g G hg b ε⁻¹
    hB hb0 1 hb hG E
  have hk : 0 ≤ (∑ a : Fin 3, inner ℂ (G (i, a)) (g (i, a))).re :=
    re_sum_inner_selected_ionization_weakDerivatives_nonneg hε.le i
      (u : State (N + 1) q) g hg ε⁻¹ hB
  have hs := integral_residual_spectator_defect_nonneg i e u Z E hE b hb0
  have hr : Integrable (fun X : Configuration (N + 1) => b (particlePosition X i) *
      (selectedRepulsionKernel i e X).toReal * ‖(u : State (N + 1) q) X‖ ^ 2) := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hb0 _)] using
      integrable_weighted_selected_repulsion i e u b hb.continuous.measurable ε⁻¹ hB
  have hn := integrable_ionization_nuclear_density i Z hε.le (u : State (N + 1) q)
  have hsplit : (∫ X : Configuration (N + 1), b (particlePosition X i) *
      ((selectedRepulsionKernel i e X).toReal -
        ((Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0).toReal) *
          ‖(u : State (N + 1) q) X‖ ^ 2) =
      (∫ X : Configuration (N + 1), b (particlePosition X i) *
        (selectedRepulsionKernel i e X).toReal * ‖(u : State (N + 1) q) X‖ ^ 2) -
      ∫ X : Configuration (N + 1), b (particlePosition X i) *
        ((Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0).toReal *
          ‖(u : State (N + 1) q) X‖ ^ 2 := by
    rw [← integral_sub hr hn]
    apply integral_congr_ae
    filter_upwards with X
    ring
  rw [hsplit] at hid
  have hnle := integral_ionization_nuclear_density_le i Z hε.le (u : State (N + 1) q)
  change _ ≤ (fullEnergyForm (fun _ : Fin 1 => Z) (fun _ => 0)
    (lipschitzBoundedSMul (fun X => b (particlePosition X i)) ε⁻¹ (fun _X => hB _)
      (lipschitzWith_selected_multiplier i b 1 hb) (u : State (N + 1) q))
    (u : State (N + 1) q) - (E : ℂ) * inner ℂ
    (lipschitzBoundedSMul (fun X => b (particlePosition X i)) ε⁻¹ (fun _X => hB _)
      (lipschitzWith_selected_multiplier i b 1 hb) (u : State (N + 1) q))
    (u : State (N + 1) q)).re + (Z : ℝ) * ‖(u : State (N + 1) q)‖ ^ 2
  dsimp only [b] at hid hs ⊢
  linarith only [hid, hk, hs, hnle]

end LiebThirring
end
