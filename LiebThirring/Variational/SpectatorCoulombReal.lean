/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SpectatorCoulomb

/-!
# Real disintegration of weighted residual Coulomb expectations

These lemmas convert the separately finite nonnegative residual expectations to literal real
integrals. They are kept separate so that later signed identities subtract only integrable terms.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring.Variational

open LiebThirring.Assembly

/-- The full weighted residual-repulsion density is integrable. -/
theorem integrable_weighted_residual_repulsion {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (u : FormDomain (N + 1) q)
    (b : Position → ℝ) (hb : Measurable b) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) :
    Integrable (fun X : Configuration (N + 1) =>
      (ENNReal.ofReal (b (particlePosition X i)) *
        electronRepulsion (residualProjection i e X)).toReal * ‖(u : State (N + 1) q) X‖ ^ 2) := by
  apply LiebThirring.integrable_weight_norm_sq
  · exact ((hb.comp (measurable_particlePosition i)).ennreal_ofReal.mul
      (measurable_electronRepulsion.comp (measurable_residualProjection i e))).aemeasurable
  · exact Lp.aestronglyMeasurable (u : State (N + 1) q)
  · simpa only [mul_assoc, enorm_eq_nnnorm] using lintegral_weighted_residual_repulsion_lt_top i e u b B hB

/-- The full weighted residual-attraction density is integrable. -/
theorem integrable_weighted_residual_attraction {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (Z : ℝ≥0)
    (u : FormDomain (N + 1) q) (b : Position → ℝ) (hb : Measurable b)
    (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) :
    Integrable (fun X : Configuration (N + 1) =>
      (ENNReal.ofReal (b (particlePosition X i)) *
        attraction (fun _ : Fin 1 => Z) (fun _ => 0) (residualProjection i e X)).toReal *
          ‖(u : State (N + 1) q) X‖ ^ 2) := by
  apply LiebThirring.integrable_weight_norm_sq
  · exact ((hb.comp (measurable_particlePosition i)).ennreal_ofReal.mul
      ((measurable_attraction (fun _ : Fin 1 => Z) (fun _ => 0)).comp
        (measurable_residualProjection i e))).aemeasurable
  · exact Lp.aestronglyMeasurable (u : State (N + 1) q)
  · simpa only [mul_assoc, enorm_eq_nnnorm] using lintegral_weighted_residual_attraction_lt_top i e Z u b B hB

/-- The full weighted selected-attraction density is integrable. -/
theorem integrable_weighted_selected_attraction {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (Z : ℝ≥0)
    (u : FormDomain (N + 1) q) (b : Position → ℝ) (hb : Measurable b)
    (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) :
    Integrable (fun X : Configuration (N + 1) =>
      (ENNReal.ofReal (b (particlePosition X i)) *
        ((Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0)).toReal *
          ‖(u : State (N + 1) q) X‖ ^ 2) := by
  apply LiebThirring.integrable_weight_norm_sq
  · exact ((hb.comp (measurable_particlePosition i)).ennreal_ofReal.mul
      (measurable_const.mul (measurable_coulombKernel.comp
        ((measurable_particlePosition i).prodMk measurable_const)))).aemeasurable
  · exact Lp.aestronglyMeasurable (u : State (N + 1) q)
  · simpa only [mul_assoc, enorm_eq_nnnorm] using lintegral_weighted_selected_attraction_lt_top i e Z u b B hB

/-- The full weighted selected-repulsion density is integrable. -/
theorem integrable_weighted_selected_repulsion {N q : ℕ} (i : Fin (N + 1))
    (e : Fin N ≃ {j : Fin (N + 1) // j ≠ i}) (u : FormDomain (N + 1) q)
    (b : Position → ℝ) (hb : Measurable b) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) :
    Integrable (fun X : Configuration (N + 1) =>
      (ENNReal.ofReal (b (particlePosition X i)) * selectedRepulsionKernel i e X).toReal *
        ‖(u : State (N + 1) q) X‖ ^ 2) := by
  apply LiebThirring.integrable_weight_norm_sq
  · exact ((hb.comp (measurable_particlePosition i)).ennreal_ofReal.mul
      (measurable_selectedRepulsionKernel i e)).aemeasurable
  · exact Lp.aestronglyMeasurable (u : State (N + 1) q)
  · simpa only [selectedRepulsionKernel, mul_assoc, enorm_eq_nnnorm] using
      lintegral_weighted_selected_repulsion_lt_top i e u b B hB

end LiebThirring.Variational

end
