/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic

/-!
# Uniform derivative bounds for the interval cutoff profile

Argument cube spectral theory cutoff input: the literal smooth transition is constant outside
`[0, 1]`, so its derivative has compact support and a global finite bound.
-/

public section

open Set Filter Function
open scoped Topology

namespace LiebThirring.TFCubes

theorem deriv_smoothTransition_eq_zero_of_neg {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  rw [heq.deriv_eq, deriv_const]

theorem deriv_smoothTransition_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  rw [heq.deriv_eq, deriv_const]

theorem tsupport_deriv_smoothTransition_subset :
    tsupport (deriv Real.smoothTransition) ⊆ Icc (0 : ℝ) 1 := by
  rw [tsupport]
  apply closure_minimal _ isClosed_Icc
  intro x hx
  rw [mem_support] at hx
  constructor
  · by_contra h
    exact hx (deriv_smoothTransition_eq_zero_of_neg (lt_of_not_ge h))
  · by_contra h
    exact hx (deriv_smoothTransition_eq_zero_of_one_lt (lt_of_not_ge h))

theorem hasCompactSupport_deriv_smoothTransition :
    HasCompactSupport (deriv Real.smoothTransition) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure tsupport_deriv_smoothTransition_subset

theorem exists_pos_bound_deriv_smoothTransition :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, ‖deriv Real.smoothTransition x‖ ≤ M := by
  have hc : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  obtain ⟨M, hM⟩ := hasCompactSupport_deriv_smoothTransition.exists_bound_of_continuous
    hc.continuous_deriv_one
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x ↦ ?_⟩
  exact (hM x).trans (le_max_left _ _)

end LiebThirring.TFCubes

end
