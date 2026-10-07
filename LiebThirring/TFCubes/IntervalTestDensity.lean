/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.LocalWeakGraph
public import LiebThirring.TFCubes.OneDimensionalModes
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Compact smooth interval tests for sine modes

This file constructs explicit compactly supported smooth cutoffs of the normalized Dirichlet
modes. The cutoff has a positive margin from each endpoint and is identically one away from two
shrinking boundary layers. These are the test functions needed for the interval weak-derivative
coefficient identity.
-/

@[expose] public section

open Set
open scoped ContDiff Topology

namespace LiebThirring.TFCubes

/-- Width of each inner transition layer. -/
noncomputable def intervalCutoffWidth (ℓ : {ℓ : ℝ // 0 < ℓ}) (k : ℕ) : ℝ :=
  ℓ.val / (4 * (k + 1 : ℝ))

theorem intervalCutoffWidth_pos (ℓ : {ℓ : ℝ // 0 < ℓ}) (k : ℕ) :
    0 < intervalCutoffWidth ℓ k := by
  unfold intervalCutoffWidth
  exact div_pos ℓ.property (mul_pos (by norm_num) (by positivity))

/-- A smooth cutoff supported a positive distance inside `(0, ℓ)`. -/
noncomputable def intervalInteriorCutoff (ℓ : {ℓ : ℝ // 0 < ℓ}) (k : ℕ) (x : ℝ) : ℝ :=
  Real.smoothTransition ((x - intervalCutoffWidth ℓ k) / intervalCutoffWidth ℓ k) *
    Real.smoothTransition ((ℓ.val - intervalCutoffWidth ℓ k - x) /
      intervalCutoffWidth ℓ k)

theorem contDiff_intervalInteriorCutoff (ℓ : {ℓ : ℝ // 0 < ℓ}) (k : ℕ) :
    ContDiff ℝ ∞ (intervalInteriorCutoff ℓ k) := by
  unfold intervalInteriorCutoff
  apply ContDiff.mul
  · exact Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const _)
  · exact Real.smoothTransition.contDiff.comp
      (((contDiff_const.sub contDiff_const).sub contDiff_id).div_const _)

theorem intervalInteriorCutoff_eq_zero_of_le_width (ℓ : {ℓ : ℝ // 0 < ℓ}) (k : ℕ)
    {x : ℝ} (hx : x ≤ intervalCutoffWidth ℓ k) : intervalInteriorCutoff ℓ k x = 0 := by
  simp only [intervalInteriorCutoff,
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hx) (intervalCutoffWidth_pos ℓ k).le), zero_mul]

theorem intervalInteriorCutoff_eq_zero_of_length_sub_width_le
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (k : ℕ) {x : ℝ}
    (hx : ℓ.val - intervalCutoffWidth ℓ k ≤ x) : intervalInteriorCutoff ℓ k x = 0 := by
  have hnum : ℓ.val - intervalCutoffWidth ℓ k - x ≤ 0 := by linarith
  rw [intervalInteriorCutoff,
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg hnum (intervalCutoffWidth_pos ℓ k).le), mul_zero]

theorem tsupport_intervalInteriorCutoff_subset (ℓ : {ℓ : ℝ // 0 < ℓ}) (k : ℕ) :
    tsupport (intervalInteriorCutoff ℓ k) ⊆
      Icc (intervalCutoffWidth ℓ k) (ℓ.val - intervalCutoffWidth ℓ k) := by
  rw [tsupport]
  apply closure_minimal _ isClosed_Icc
  intro x hx
  rw [Function.mem_support, Ne] at hx
  simp only [mem_Icc]
  constructor
  · exact not_lt.mp fun h ↦ hx (intervalInteriorCutoff_eq_zero_of_le_width ℓ k h.le)
  · exact not_lt.mp fun h ↦
      hx (intervalInteriorCutoff_eq_zero_of_length_sub_width_le ℓ k h.le)

theorem tsupport_intervalInteriorCutoff_subset_Ioo (ℓ : {ℓ : ℝ // 0 < ℓ}) (k : ℕ) :
    tsupport (intervalInteriorCutoff ℓ k) ⊆ Ioo 0 ℓ.val := by
  refine (tsupport_intervalInteriorCutoff_subset ℓ k).trans ?_
  intro x hx
  rw [mem_Icc] at hx
  exact ⟨(intervalCutoffWidth_pos ℓ k).trans_le hx.1,
    lt_of_le_of_lt hx.2 (sub_lt_self ℓ.val (intervalCutoffWidth_pos ℓ k))⟩

theorem hasCompactSupport_intervalInteriorCutoff (ℓ : {ℓ : ℝ // 0 < ℓ}) (k : ℕ) :
    HasCompactSupport (intervalInteriorCutoff ℓ k) :=
  HasCompactSupport.intro isCompact_Icc (fun x hx ↦ by
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact intervalInteriorCutoff_eq_zero_of_le_width ℓ k hx.le
    · exact intervalInteriorCutoff_eq_zero_of_length_sub_width_le ℓ k hx.le)

theorem intervalInteriorCutoff_eq_one (ℓ : {ℓ : ℝ // 0 < ℓ}) (k : ℕ) {x : ℝ}
    (hx₀ : 2 * intervalCutoffWidth ℓ k ≤ x)
    (hxℓ : x ≤ ℓ.val - 2 * intervalCutoffWidth ℓ k) :
    intervalInteriorCutoff ℓ k x = 1 := by
  unfold intervalInteriorCutoff
  have hleft : 1 ≤ (x - intervalCutoffWidth ℓ k) / intervalCutoffWidth ℓ k := by
    apply (le_div_iff₀ (intervalCutoffWidth_pos ℓ k)).2
    linarith
  have hright : 1 ≤ (ℓ.val - intervalCutoffWidth ℓ k - x) /
      intervalCutoffWidth ℓ k := by
    apply (le_div_iff₀ (intervalCutoffWidth_pos ℓ k)).2
    linarith
  rw [Real.smoothTransition.one_of_one_le hleft,
    Real.smoothTransition.one_of_one_le hright, one_mul]

/-- The compact smooth approximation to the `n`-th normalized sine mode. -/
noncomputable def compactDirichletMode (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) (k : ℕ)
    (x : ℝ) : ℂ :=
  intervalInteriorCutoff ℓ k x * dirichletIntervalMode ℓ n x

theorem contDiff_compactDirichletMode (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) (k : ℕ) :
    ContDiff ℝ ∞ (compactDirichletMode ℓ n k) := by
  have hmode : ContDiff ℝ ∞ (dirichletIntervalMode ℓ n) := by
    unfold dirichletIntervalMode
    fun_prop
  unfold compactDirichletMode
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_intervalInteriorCutoff ℓ k)).mul
    (Complex.ofRealCLM.contDiff.comp hmode)

theorem tsupport_compactDirichletMode_subset_Ioo
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) (k : ℕ) :
    tsupport (compactDirichletMode ℓ n k) ⊆ Ioo 0 ℓ.val := by
  have hclosed : tsupport (compactDirichletMode ℓ n k) ⊆
      Icc (intervalCutoffWidth ℓ k) (ℓ.val - intervalCutoffWidth ℓ k) := by
    rw [tsupport]
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have hxcut : intervalInteriorCutoff ℓ k x ≠ 0 := by
      intro hzero
      apply hx
      simp [compactDirichletMode, hzero]
    exact tsupport_intervalInteriorCutoff_subset ℓ k (subset_tsupport _ hxcut)
  refine hclosed.trans ?_
  intro x hx
  exact ⟨(intervalCutoffWidth_pos ℓ k).trans_le hx.1,
    lt_of_le_of_lt hx.2 (sub_lt_self ℓ.val (intervalCutoffWidth_pos ℓ k))⟩

theorem hasCompactSupport_compactDirichletMode
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) (k : ℕ) :
    HasCompactSupport (compactDirichletMode ℓ n k) :=
  (hasCompactSupport_intervalInteriorCutoff ℓ k).mono (by
    intro x hx
    rw [Function.mem_support, Ne]
    intro hzero
    apply hx
    simp [compactDirichletMode, hzero])

end LiebThirring.TFCubes

end
