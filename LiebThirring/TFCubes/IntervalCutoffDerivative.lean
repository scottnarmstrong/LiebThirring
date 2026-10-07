/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.IntervalTestDensity
import Mathlib.Tactic

/-! # Classical derivatives of compact sine tests

These are the literal chain and product rules for the physical compact tests.
-/

public section
open Set
open scoped ContDiff
namespace LiebThirring.TFCubes

theorem deriv_intervalInteriorCutoff (ℓ : {ℓ : ℝ // 0 < ℓ}) (k : ℕ) (x : ℝ) :
    deriv (intervalInteriorCutoff ℓ k) x =
      deriv Real.smoothTransition
          ((x - intervalCutoffWidth ℓ k) / intervalCutoffWidth ℓ k) /
          intervalCutoffWidth ℓ k *
        Real.smoothTransition
          ((ℓ.val - intervalCutoffWidth ℓ k - x) / intervalCutoffWidth ℓ k) -
      Real.smoothTransition
          ((x - intervalCutoffWidth ℓ k) / intervalCutoffWidth ℓ k) *
        (deriv Real.smoothTransition
          ((ℓ.val - intervalCutoffWidth ℓ k - x) / intervalCutoffWidth ℓ k) /
          intervalCutoffWidth ℓ k) := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hl := ((hs.differentiable (by simp))
    ((x - intervalCutoffWidth ℓ k) / intervalCutoffWidth ℓ k)).hasDerivAt.comp x
    (((hasDerivAt_id x).sub_const (intervalCutoffWidth ℓ k)).div_const
      (intervalCutoffWidth ℓ k))
  have hr := ((hs.differentiable (by simp))
    ((ℓ.val - intervalCutoffWidth ℓ k - x) / intervalCutoffWidth ℓ k)).hasDerivAt.comp x
    (((hasDerivAt_const x (ℓ.val - intervalCutoffWidth ℓ k)).sub
      (hasDerivAt_id x)).div_const (intervalCutoffWidth ℓ k))
  have hm := (hl.mul hr).deriv
  dsimp only [Function.comp_def, id_eq, Pi.sub_apply, Pi.mul_apply] at hm
  have heq :
      ((fun y : ℝ ↦ Real.smoothTransition
        ((y - intervalCutoffWidth ℓ k) / intervalCutoffWidth ℓ k)) *
        fun y : ℝ ↦ Real.smoothTransition
          ((ℓ.val - intervalCutoffWidth ℓ k - y) / intervalCutoffWidth ℓ k)) =
      (fun y : ℝ ↦ Real.smoothTransition
        ((y - intervalCutoffWidth ℓ k) / intervalCutoffWidth ℓ k) *
        Real.smoothTransition
          ((ℓ.val - intervalCutoffWidth ℓ k - y) / intervalCutoffWidth ℓ k)) := by
    funext y
    rw [Pi.mul_apply]
  rw [heq] at hm
  unfold intervalInteriorCutoff
  rw [hm]
  ring

theorem fderiv_compactDirichletMode_apply_one
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) (k : ℕ) (x : ℝ) :
    fderiv ℝ (compactDirichletMode ℓ n k) x 1 =
      (deriv (intervalInteriorCutoff ℓ k) x * dirichletIntervalMode ℓ n x +
        intervalInteriorCutoff ℓ k x * deriv (dirichletIntervalMode ℓ n) x : ℝ) := by
  have hcut := (contDiff_intervalInteriorCutoff ℓ k).differentiable (by simp)
  have hmode := (hasDerivAt_dirichletIntervalMode ℓ n x).differentiableAt
  have hd := ((hcut x).hasDerivAt.mul hmode.hasDerivAt).ofReal_comp
  have he : compactDirichletMode ℓ n k =
      fun y ↦ ((intervalInteriorCutoff ℓ k y * dirichletIntervalMode ℓ n y : ℝ) : ℂ) := by
    funext y
    exact (Complex.ofReal_mul _ _).symm
  rw [he, fderiv_apply_one_eq_deriv]
  exact hd.deriv

end LiebThirring.TFCubes
end
