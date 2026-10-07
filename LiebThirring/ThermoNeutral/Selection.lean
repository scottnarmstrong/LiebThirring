/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Average

/-! # Selection below a zero mean -/

public section

open MeasureTheory

namespace LiebThirring.ThermoNeutral

/-- A zero-mean integrable real random variable has a nonpositive value. -/
theorem exists_nonpos_of_integral_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Integrable X μ) (hmean : ∫ q, X q ∂μ = 0) :
    ∃ q, X q ≤ 0 := by
  simpa only [hmean] using exists_le_integral hX

end LiebThirring.ThermoNeutral

end
