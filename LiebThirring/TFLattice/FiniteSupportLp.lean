/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Lower-exponent convergence on a fixed support of finite volume

This is the finite-volume Hölder step in Lieb–Simon (1977) III.14, pp. 69–71 (filled-density convergence).
The explicit `MemLp` assertions prevent the default real norm value outside Lp
from being mistaken for convergence.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LiebThirring.TFLattice

theorem indicator_eq_of_zero_off {α : Type*} [MeasurableSpace α]
    {S : Set α} {f : α → ℝ} (hs : ∀ x ∉ S, f x = 0) : S.indicator f = f := by
  classical
  ext x
  by_cases hx : x ∈ S
  · exact indicator_of_mem hx f
  · rw [indicator_of_notMem hx, hs x hx]

theorem lpNorm_eq_restrict_of_zero_off {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {S : Set α} (hS : MeasurableSet S) {f : α → ℝ}
    (hs : ∀ x ∉ S, f x = 0) (p : ℝ≥0∞) :
    lpNorm f p μ = lpNorm f p (μ.restrict S) := by
  nth_rw 1 [← indicator_eq_of_zero_off hs]
  unfold lpNorm
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hS]

theorem memLp_of_two_of_zero_off {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {S : Set α} (hS : MeasurableSet S) (hvol : μ S ≠ ∞)
    {f : α → ℝ} (hs : ∀ x ∉ S, f x = 0) (hf : MemLp f 2 μ)
    {p : ℝ≥0∞} (hp : p ≤ 2) : MemLp f p μ := by
  let : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hvol
  rw [← indicator_eq_of_zero_off hs, memLp_indicator_iff_restrict hS]
  exact (hf.restrict S).mono_exponent hp

theorem lpNorm_le_two_of_zero_off {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {S : Set α} (hS : MeasurableSet S) (hvol : μ S ≠ ∞)
    {f : α → ℝ} (hs : ∀ x ∉ S, f x = 0) (hf : MemLp f 2 μ)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    lpNorm f p μ ≤ lpNorm f 2 μ * (μ S).toReal ^ (1 / p.toReal - 1 / 2 : ℝ) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hp1)
  have hpT : p ≠ ∞ := ne_of_lt (hp2.trans_lt (by norm_num))
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hpT
  have hpR2 : p.toReal ≤ 2 := by
    simpa using ENNReal.toReal_mono (by simp : (2 : ℝ≥0∞) ≠ ∞) hp2
  have hexp : 0 ≤ 1 / p.toReal - 1 / 2 := by
    have hi := one_div_le_one_div_of_le hpR hpR2
    linarith
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp2 (hf.restrict S).aestronglyMeasurable
  have hfinite : eLpNorm f 2 (μ.restrict S) *
      (μ.restrict S) univ ^ (1 / p.toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ∞ := by
    apply ENNReal.mul_ne_top (hf.restrict S).eLpNorm_ne_top
    apply ENNReal.rpow_ne_top_of_nonneg (by simpa using hexp)
    simpa using hvol
  have hreal := ENNReal.toReal_mono hfinite hcompare
  rw [lpNorm_eq_restrict_of_zero_off hS hs p, lpNorm_eq_restrict_of_zero_off hS hs 2]
  simpa [lpNorm, ENNReal.toReal_mul, ENNReal.toReal_rpow] using hreal

/-- Fixed finite support transports actual L² convergence to every exponent
between 1 and 2, in particular 1 and 5/3. -/
theorem tendsto_lpNorm_of_two_of_zero_off {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {S : Set α} (hS : MeasurableSet S) (hvol : μ S ≠ ∞)
    {ι : Type*} {l : Filter ι} {f : ι → α → ℝ}
    (hs : ∀ j x, x ∉ S → f j x = 0) (hf : ∀ j, MemLp (f j) 2 μ)
    (ht : Tendsto (fun j => lpNorm (f j) 2 μ) l (𝓝 0))
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    Tendsto (fun j => lpNorm (f j) p μ) l (𝓝 0) := by
  have hbound := ht.mul_const ((μ S).toReal ^ (1 / p.toReal - 1 / 2 : ℝ))
  simp only [zero_mul] at hbound
  apply squeeze_zero' (Eventually.of_forall fun _ => lpNorm_nonneg)
    (Eventually.of_forall fun j => lpNorm_le_two_of_zero_off hS hvol (hs j) (hf j) hp1 hp2)
    hbound

end LiebThirring.TFLattice

end
