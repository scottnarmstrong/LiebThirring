/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Fourier.Schwartz
import LiebThirring.Kinetic.CurryingProductBasic

/-! # Schwartz mass identities on both orbital and configuration carriers -/

public section

open MeasureTheory
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Pointwise Schwartz mass equals the norm of its L² class, on either carrier. -/
theorem escape_schwartz_lintegral_mass (f : 𝓢(V, H)) :
    (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2) =
      (‖f.toLp 2 (volume : Measure V)‖₊ : ℝ≥0∞) ^ 2 := by
  calc
    _ = ∫⁻ x, (‖(f.toLp 2 (volume : Measure V)) x‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [f.coeFn_toLp 2 (volume : Measure V)] with x hx
      rw [hx]
    _ = _ := lintegral_l2_enorm_sq _

/-- The real integral has the same squared-norm normalization. -/
theorem escape_schwartz_integral_mass (f : 𝓢(V, H)) :
    (∫ x, ‖f x‖ ^ 2) = ‖f.toLp 2 (volume : Measure V)‖ ^ 2 := by
  have he := escape_schwartz_lintegral_mass f
  rw [Fourier.lintegral_norm_sq_eq_ofReal_integral] at he
  have hr := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun x => sq_nonneg ‖f x‖)),
    ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm] using hr

/-- Unit L² norm implies unit extended mass for a Schwartz amplitude. -/
theorem escape_schwartz_lintegral_mass_one (f : 𝓢(V, H))
    (hf : ‖f.toLp 2 (volume : Measure V)‖ = 1) :
    (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2) = 1 := by
  rw [escape_schwartz_lintegral_mass]
  have hn : ‖f.toLp 2 (volume : Measure V)‖₊ = 1 := NNReal.coe_injective hf
  rw [hn, ENNReal.coe_one, one_pow]

end LiebThirring

end
