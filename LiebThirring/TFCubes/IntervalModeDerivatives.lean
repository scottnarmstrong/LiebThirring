/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.IntervalModesL2

/-!
# Actual sine derivatives in physical L²

The derivative of a normalized sine mode is its physical frequency times the normalized
positive cosine mode. These identities concern classical derivatives and their L² classes.
-/

public section

open MeasureTheory Set

namespace LiebThirring.TFCubes

theorem fderiv_dirichletIntervalMode_ofReal (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) (x : ℝ) :
    fderiv ℝ (fun y ↦ (dirichletIntervalMode ℓ n y : ℂ)) x 1 =
      (intervalFrequency ℓ n : ℂ) * (neumannIntervalMode ℓ (n : ℕ) x : ℂ) := by
  rw [fderiv_apply_one_eq_deriv,
    (hasDerivAt_dirichletIntervalMode ℓ n x).ofReal_comp.deriv]
  have hn : (n : ℕ) ≠ 0 := n.property.ne'
  simp only [neumannIntervalMode, neumannIntervalCoefficient, ite_eq_right hn,
    Complex.ofReal_mul]
  ring

end LiebThirring.TFCubes

end
