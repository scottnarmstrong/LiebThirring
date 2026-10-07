/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.WeightedRadial

/-!
# Integration by parts for the punctured smooth core

Argument weighted positivity first uses compact smooth functions whose support avoids zero.
These lemmas handle coefficients singular only at zero without assuming any
integrability or integration-by-parts identity as a source-theorem premise.
-/

public section
open MeasureTheory
open scoped RealInnerProductSpace
namespace LiebThirring

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Both radial fields in weighted positivity are smooth on punctured space. -/
theorem contDiffAt_ionizationField {ε : ℝ} (hε : 0 ≤ ε) {x : Position}
    (hx : x ≠ 0) (v : Position) :
    ContDiffAt ℝ 1 (fun y : Position => ionizationFieldCoeff ε ‖y‖ * inner ℝ y v) x := by
  have hn := contDiffAt_norm ℝ (n := (1 : WithTop ℕ∞)) hx
  have hd : 0 < 1 + ε * ‖x‖ :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hε (norm_nonneg x))
  exact (contDiffAt_const.div (hn.mul (contDiffAt_const.add (contDiffAt_const.mul hn)))
    (mul_ne_zero (norm_ne_zero_iff.mpr hx) hd.ne')).mul
    ((innerSL ℝ v).contDiff.contDiffAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y => real_inner_comm v y)))

theorem contDiffAt_ionizationGrad {ε : ℝ} (hε : 0 ≤ ε) {x : Position}
    (hx : x ≠ 0) (v : Position) :
    ContDiffAt ℝ 1 (fun y : Position => ionizationGradCoeff ε ‖y‖ * inner ℝ y v) x := by
  have hn := contDiffAt_norm ℝ (n := (1 : WithTop ℕ∞)) hx
  have hd : 0 < 1 + ε * ‖x‖ :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hε (norm_nonneg x))
  exact (contDiffAt_const.div (hn.mul ((contDiffAt_const.add (contDiffAt_const.mul hn)).pow 2))
    (mul_ne_zero (norm_ne_zero_iff.mpr hx) (pow_ne_zero 2 hd.ne'))).mul
    ((innerSL ℝ v).contDiff.contDiffAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y => real_inner_comm v y)))

end LiebThirring
end
