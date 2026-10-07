/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SpectatorReindex

/-! # Weighted expectations of actual residual states

The identities first establish absolute integrability and then pass from literal densities to
finite ENNReal expectations. No normalization or symmetry is needed.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.Variational

/-- Almost everywhere, the weighted literal integral is the weighted expectation of the slice. -/
theorem weighted_residual_expectation_ae {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (p : Configuration k → ℝ≥0∞) (hp : Measurable p)
    (hfin : (∫⁻ X : Configuration N, p (residualProjection i e X) * ‖u X‖ₑ ^ 2) < ⊤)
    (b : Position → ℝ) (hb0 : ∀ x, 0 ≤ b x) :
    (fun x : Position => ∑ s : Fin q, ∫ y : Configuration k,
      (ENNReal.ofReal (b x) * p y).toReal * ‖residualParticleSlice i e u x s y‖ ^ 2) =ᵐ[volume]
    (fun x => b x * ∑ s : Fin q,
      (∫⁻ y : Configuration k, p y * ‖residualParticleSlice i e u x s y‖ₑ ^ 2).toReal) := by
  filter_upwards [spectator_reindex_expectation_lt_top_ae i e u p hp hfin] with x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hb0 x), mul_assoc]
  rw [integral_const_mul]
  congr 1
  exact LiebThirring.integral_weight_norm_sq (p := p)
    (f := fun y => residualParticleSlice i e u x s y) hp.aemeasurable
    (Lp.aestronglyMeasurable _) (hx s)

/-- Bounded weights preserve absolute integrability of the summed slice expectations. -/
theorem integrable_weighted_residual_expectation {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (p : Configuration k → ℝ≥0∞) (hp : Measurable p)
    (hfin : (∫⁻ X : Configuration N, p (residualProjection i e X) * ‖u X‖ₑ ^ 2) < ⊤)
    (b : Position → ℝ) (hb : Measurable b) (hb0 : ∀ x, 0 ≤ b x)
    (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) :
    Integrable (fun x : Position => b x * ∑ s : Fin q,
      (∫⁻ y : Configuration k, p y * ‖residualParticleSlice i e u x s y‖ₑ ^ 2).toReal) := by
  have hw := LiebThirring.lintegral_bounded_weight_lt_top
    (fun X : Configuration N => b (particlePosition X i)) B
    (fun X => hB (particlePosition X i)) (fun X => p (residualProjection i e X))
    (fun X => u X) hfin
  have hi := integrable_spectator_reindex_joint_real i e u
    (fun z => ENNReal.ofReal (b z.1) * p z.2)
    ((hb.comp measurable_fst).ennreal_ofReal.mul (hp.comp measurable_snd))
    (by simpa only [mul_assoc] using hw)
  exact hi.congr (weighted_residual_expectation_ae i e u p hp hfin b hb0)

/-- Exact real disintegration of bounded weighted residual expectations. -/
theorem integral_weighted_residual_expectation {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (p : Configuration k → ℝ≥0∞) (hp : Measurable p)
    (hfin : (∫⁻ X : Configuration N, p (residualProjection i e X) * ‖u X‖ₑ ^ 2) < ⊤)
    (b : Position → ℝ) (hb : Measurable b) (hb0 : ∀ x, 0 ≤ b x)
    (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) :
    (∫ x : Position, b x * ∑ s : Fin q,
      (∫⁻ y : Configuration k, p y * ‖residualParticleSlice i e u x s y‖ₑ ^ 2).toReal) =
    ∫ X : Configuration N, b (particlePosition X i) *
      (p (residualProjection i e X)).toReal * ‖u X‖ ^ 2 := by
  have hw := LiebThirring.lintegral_bounded_weight_lt_top
    (fun X : Configuration N => b (particlePosition X i)) B
    (fun X => hB (particlePosition X i)) (fun X => p (residualProjection i e X))
    (fun X => u X) hfin
  have hd := integral_spectator_reindex_joint_real i e u
    (fun z => ENNReal.ofReal (b z.1) * p z.2)
    ((hb.comp measurable_fst).ennreal_ofReal.mul (hp.comp measurable_snd))
    (by simpa only [mul_assoc] using hw)
  rw [integral_congr_ae (weighted_residual_expectation_ae i e u p hp hfin b hb0)] at hd
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hb0 _)] using hd.symm

/-- The spin-summed residual L² mass is integrable against bounded nonnegative weights. -/
theorem integrable_weighted_residual_mass {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (b : Position → ℝ) (hb : Measurable b) (hb0 : ∀ x, 0 ≤ b x)
    (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) :
    Integrable (fun x : Position => b x * ∑ s : Fin q, ‖residualParticleSlice i e u x s‖ ^ 2) := by
  have hfin : (∫⁻ X : Configuration N, (1 : ℝ≥0∞) * ‖u X‖ₑ ^ 2) < ⊤ := by
    simp only [one_mul, lintegral_l2_enorm_sq]
    exact ENNReal.pow_lt_top ENNReal.coe_lt_top
  have hi := integrable_weighted_residual_expectation i e u (fun _ => 1) measurable_const
    hfin b hb hb0 B hB
  simp only [one_mul] at hi
  simp only [lintegral_l2_enorm_sq] at hi
  simpa only [ENNReal.toReal_pow, enorm_eq_nnnorm,
    ENNReal.coe_toReal, NNReal.coe_pow, coe_nnnorm] using hi

end LiebThirring.Variational
end
