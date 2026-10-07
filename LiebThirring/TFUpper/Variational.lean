/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.NearMinimizers
public import LiebThirring.TFUpper.Approximate

/-! # TF near-minimizers and the exact integral particle-number scale

These are the variational and scaling ingredients for full-potential upper bound. The exact-mass
infimum is approximated without a minimizer or neutrality premise.
The sequence `α_j = N_j / ν` matches the molecular limit.
-/

public section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace LiebThirring.TFUpper

/-- The honest TF infimum admits real exact-mass near-minimizers, including
above neutrality. Its endpoint finiteness is proved by the functional library. -/
theorem exists_exact_mass_tfFunctional_lt {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : TFDensity, tfMass ρ = (ν : ℝ) ∧
      tfFunctional a z R ρ < (tfEnergy a ν z R).toReal + ε := by
  exact TFFunctional.exists_tfDensity_near_tfEnergy a ν z R ε hε

theorem particleNumber_eq_scale_mul_mass (ν : ℝ≥0) (hν : 0 < ν) (N : ℕ) :
    (N : ℝ) = (((N : ℝ≥0) / ν : ℝ≥0) : ℝ) * (ν : ℝ) := by
  rw [NNReal.coe_div, NNReal.coe_natCast, div_mul_cancel₀ _
    (show (ν : ℝ) ≠ 0 from (show 0 < (ν : ℝ) from hν).ne')]

theorem eventually_chargeScale_pos (ν : ℝ≥0) (hν : 0 < ν)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    ∀ᶠ j in atTop, 0 < (N j : ℝ≥0) / ν := by
  filter_upwards [hN.eventually (eventually_ge_atTop 1)] with j hj
  apply div_pos _ hν
  exact_mod_cast (show 0 < N j from lt_of_lt_of_le Nat.zero_lt_one hj)

end LiebThirring.TFUpper
end
