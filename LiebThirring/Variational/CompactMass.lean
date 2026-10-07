/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Configuration
import LiebThirring.Variational.FormIntegral
import LiebThirring.Kinetic.DensityBasic

/-! # Real L² mass integrals on the state carrier -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- The squared state norm is its literal real mass integral. -/
theorem integral_state_norm_sq {N q : ℕ} (u : State N q) :
    (∫ x : Configuration N, ‖u x‖ ^ 2) = ‖u‖ ^ 2 := by
  have hfin : (∫⁻ x : Configuration N, (1 : ℝ≥0∞) * (‖u x‖₊ : ℝ≥0∞) ^ 2) < ⊤ := by
    simp only [one_mul, lintegral_state_norm_sq]
    finiteness
  simpa only [ENNReal.toReal_one, one_mul, lintegral_state_norm_sq,
    ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm] using
    integral_weight_norm_sq aemeasurable_const (Lp.aestronglyMeasurable u) hfin

/-- The real mass integrand of every state is absolutely integrable. -/
theorem integrable_state_norm_sq {N q : ℕ} (u : State N q) :
    Integrable (fun x : Configuration N => ‖u x‖ ^ 2) := by
  have hfin : (∫⁻ x : Configuration N, (1 : ℝ≥0∞) * (‖u x‖₊ : ℝ≥0∞) ^ 2) < ⊤ := by
    simp only [one_mul, lintegral_state_norm_sq]
    finiteness
  simpa only [ENNReal.toReal_one, one_mul] using
    integrable_weight_norm_sq aemeasurable_const (Lp.aestronglyMeasurable u) hfin

end LiebThirring

end
