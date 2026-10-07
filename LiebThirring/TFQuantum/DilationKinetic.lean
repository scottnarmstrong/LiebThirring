/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.TFQuantum.DilationFourier
public import LiebThirring.TFQuantum.DilationState
/-! # Kinetic dilation on electronic states

The Fourier kinetic energy scales by the square of the spatial dilation.
All identities hold on the whole state carrier in extended nonnegative form.
direct proof calculation.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal FourierTransform
namespace LiebThirring
namespace Dilation

theorem kineticWeight_smul {N : ℕ} (r : ℝ) (hr : 0 < r) (ξ : Configuration N) :
    ENNReal.ofReal ((2*Real.pi)^2) * (‖r • ξ‖₊ : ℝ≥0∞)^2 =
      ENNReal.ofReal (r^2) *
        (ENNReal.ofReal ((2*Real.pi)^2) * (‖ξ‖₊ : ℝ≥0∞)^2) := by
  have hn : (‖r • ξ‖₊ : ℝ≥0∞) = ENNReal.ofReal r * (‖ξ‖₊ : ℝ≥0∞) := by
    rw [← enorm_eq_nnnorm, ← ofReal_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr, ENNReal.ofReal_mul hr.le, ofReal_norm, enorm_eq_nnnorm]
  rw [hn, mul_pow, ENNReal.ofReal_pow hr.le]
  ring
end Dilation

theorem kineticEnergy_stateDilationEquiv {N q : ℕ} (r : ℝ) (hr : 0 < r) (ψ : State N q) :
    kineticEnergy (stateDilationEquiv r hr ψ) = ENNReal.ofReal (r^2) * kineticEnergy ψ := by
  unfold kineticEnergy
  let w : Configuration N → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal ((2*Real.pi)^2) * (‖ξ‖₊ : ℝ≥0∞)^2
  change (∫⁻ ξ, w ξ * ‖𝓕 (Dilation.applyL2 r hr ψ) ξ‖ₑ^2) =
    ENNReal.ofReal (r^2) * ∫⁻ ξ, w ξ * ‖𝓕 ψ ξ‖ₑ^2
  rw [Dilation.fourier_applyL2,
    Dilation.lintegral_weight_applyL2 r⁻¹ (inv_pos.mpr hr) (𝓕 ψ) w]
  simp only [inv_inv]
  calc
    _ = ∫⁻ ξ, ENNReal.ofReal (r^2) * (w ξ * ‖𝓕 ψ ξ‖ₑ^2) := by
      apply lintegral_congr
      intro ξ
      rw [show w (r • ξ) = ENNReal.ofReal (r^2) * w ξ from Dilation.kineticWeight_smul r hr ξ,
        mul_assoc]
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
end LiebThirring
end
