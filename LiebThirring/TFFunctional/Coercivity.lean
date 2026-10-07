/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.Functional
public import LiebThirring.TFFunctional.Young
public import LiebThirring.TFFunctional.DensityBasic

/-! # Abstract Thomas--Fermi coercivity -/

public section

open MeasureTheory
open scoped NNReal

namespace LiebThirring.TFFunctional

/-- The explicit constant produced when a `K^(3/5)` attraction bound is
absorbed into half of the kinetic term. -/
@[expose] noncomputable def youngCoercivityConstant (a A : ℝ) : ℝ :=
  (2 / 5 : ℝ) * (A * ((5 / 6 : ℝ) * a) ^ (-(3 : ℝ) / 5)) ^ ((5 : ℝ) / 2)

theorem youngCoercivityConstant_nonneg {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A) :
    0 ≤ youngCoercivityConstant a A := by
  unfold youngCoercivityConstant
  exact mul_nonneg (by norm_num)
    (Real.rpow_nonneg (mul_nonneg hA
      (Real.rpow_nonneg (mul_nonneg (by norm_num) ha.le) _)) _)

/-- A quantitative attraction estimate and nonnegative direct energy imply
the lower bound used in the TF compactness argument. This helper deliberately
keeps the analytic attraction estimate explicit. -/
theorem tfFunctional_lower_bound_of_attraction_le {M : ℕ}
    (a : {a : ℝ // 0 < a}) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ρ : TFDensity) (A B : ℝ)
    (hK : 0 ≤ ∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3))
    (hA : 0 ≤ A)
    (hV : (∫ x : Position, tfNuclearPotential z R x * ρ.val x) ≤
      A * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) ^ ((3 : ℝ) / 5) + B)
    (hD : 0 ≤ tfCoulombEnergy ρ ρ) :
    a.val / 2 * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) -
        (youngCoercivityConstant a.val A + B) ≤ tfFunctional a z R ρ := by
  have hy := mul_rpow_three_fifths_le a.val A
    (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) a.property hA hK
  unfold tfFunctional youngCoercivityConstant
  linarith

/-- Uniform version on a positive coefficient interval: the constant uses
only the lower endpoint, while half of the actual kinetic coefficient remains. -/
theorem tfFunctional_lower_bound_uniform_of_attraction_le {M : ℕ}
    (a : {a : ℝ // 0 < a}) (amin : ℝ) (hamin : 0 < amin) (hmina : amin ≤ a.val)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ : TFDensity) (A B : ℝ)
    (hK : 0 ≤ ∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3))
    (hA : 0 ≤ A)
    (hV : (∫ x : Position, tfNuclearPotential z R x * ρ.val x) ≤
      A * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) ^ ((3 : ℝ) / 5) + B)
    (hD : 0 ≤ tfCoulombEnergy ρ ρ) :
    a.val / 2 * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) -
        (youngCoercivityConstant amin A + B) ≤ tfFunctional a z R ρ := by
  have hy := mul_rpow_three_fifths_le amin A
    (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) hamin hA hK
  unfold tfFunctional youngCoercivityConstant
  have hcoef : a.val / 2 ≤ a.val - amin / 2 := by linarith
  have hkin := mul_le_mul_of_nonneg_right hcoef hK
  linarith

/-- Exact dependence of the functional on its kinetic coefficient. -/
theorem tfFunctional_sub_tfFunctional {M : ℕ}
    (a b : {a : ℝ // 0 < a}) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ρ : TFDensity) :
    tfFunctional a z R ρ - tfFunctional b z R ρ =
      (a.val - b.val) * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) := by
  unfold tfFunctional
  ring

end LiebThirring.TFFunctional

end
