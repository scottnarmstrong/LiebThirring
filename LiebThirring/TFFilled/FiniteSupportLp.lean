/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Lower-exponent estimates on a fixed finite support

This file records the finite-volume Hölder estimate used to turn `L²`
convergence of density errors with fixed support into convergence in every
`Lᵖ`, `1 ≤ p ≤ 2`.  It also gives small conversion lemmas between the
pointwise-function seminorms and the norm of the associated `Lp` element.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace LiebThirring.TFFilled

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]

omit [MeasurableSpace α] in
theorem indicator_eq_of_zero_off {S : Set α} {f : α → E}
    (hf : ∀ x ∉ S, f x = 0) : S.indicator f = f := by
  classical
  ext x
  by_cases hx : x ∈ S
  · exact indicator_of_mem hx f
  · rw [indicator_of_notMem hx, hf x hx]

/-- An `L²` function supported on a finite-measure set belongs to every
lower-exponent `Lᵖ`. -/
theorem memLp_of_two_of_zero_off {μ : Measure α} {S : Set α}
    (hS : MeasurableSet S) (hSμ : μ S ≠ ∞) {f : α → E}
    (hsupp : ∀ x ∉ S, f x = 0) (hf : MemLp f 2 μ)
    {p : ℝ≥0∞} (hp : p ≤ 2) : MemLp f p μ := by
  let : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hSμ
  rw [← indicator_eq_of_zero_off hsupp, memLp_indicator_iff_restrict hS]
  exact (hf.restrict S).mono_exponent hp

/-- A convenient form of `lpNorm_one_eq_integral_norm` for real-valued
functions. -/
theorem lpNorm_one_eq_integral_abs {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    lpNorm f 1 μ = ∫ x, |f x| ∂μ := by
  rw [lpNorm_one_eq_integral_norm hf]
  simp only [Real.norm_eq_abs]

end LiebThirring.TFFilled

end
