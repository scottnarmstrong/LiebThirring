/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCore.Duality
public import LiebThirring.Assembly.CutoffRadial
import LiebThirring.Assembly.Young

/-! # Nuclear cores paid by a kinetic fraction

Argument nuclear-core estimate (direct proof). Assign η/M of kinetic energy to each
one-nucleus core. This proves the stated overlap-safe error without a
separation assumption on the nuclear positions. The case M = 0 is included.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.TFCore

/-- Sum of Coulomb poles restricted to radius r, with their extended values. -/
@[expose] noncomputable def nuclearCores {M : ℕ}
    (a : Fin M → ℝ≥0) (R : Fin M → Position) (r : ℝ) (x : Position) : ℝ≥0∞ :=
  ∑ k : Fin M, Assembly.nucleusCutoff (a k : ℝ) r (R k) x

/-- Overlap-safe coefficient, independent of the state, geometry and large-charge scale. -/
@[expose] noncomputable def coreErrorConstant (q : ℕ) {M : ℕ} (z : Fin M → ℝ≥0) : ℝ :=
  8 * Real.pi * youngConstant * (kineticCoefficient q) ^ (-(3 : ℝ) / 2) *
    (M : ℝ) ^ ((3 : ℝ) / 2) * ∑ k : Fin M, (z k : ℝ) ^ ((5 : ℝ) / 2)

theorem coreErrorConstant_nonneg (q : ℕ) {M : ℕ} (z : Fin M → ℝ≥0) :
    0 ≤ coreErrorConstant q z := by
  unfold coreErrorConstant youngConstant kineticCoefficient
  positivity

private theorem allocated_cost_eq (q M : ℕ) (hM : 0 < M) (η r : ℝ)
    (hη : 0 < η) (a : Fin M → ℝ≥0) :
    ∑ k : Fin M,
      (youngConstant * ((η / M) * kineticCoefficient q) ^ (-(3 : ℝ) / 2)) *
        (8 * Real.pi * (a k : ℝ) ^ ((5 : ℝ) / 2) * Real.sqrt r) =
      coreErrorConstant q a * η ^ (-(3 : ℝ) / 2) * Real.sqrt r := by
  have hM' : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  rw [Real.mul_rpow (div_pos hη hM').le (by
    unfold kineticCoefficient
    positivity), Real.div_rpow hη.le hM'.le]
  have hm : (M : ℝ) ^ (-(3 : ℝ) / 2) = ((M : ℝ) ^ ((3 : ℝ) / 2))⁻¹ :=
    by rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring, Real.rpow_neg hM'.le]
  rw [hm, div_inv_eq_mul]
  simp only [coreErrorConstant]
  rw [← Finset.mul_sum]
  calc
    _ = (youngConstant * (η ^ (-(3 : ℝ) / 2) * (M : ℝ) ^ ((3 : ℝ) / 2) *
        kineticCoefficient q ^ (-(3 : ℝ) / 2))) *
        (8 * Real.pi * Real.sqrt r * ∑ k : Fin M, (a k : ℝ) ^ ((5 : ℝ) / 2)) := by
      congr 1
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by ring

/-- Extended nuclear-core estimate for arbitrary charges and radius. No nuclear separation is needed. -/
theorem lintegral_nuclearCores_density_le (q : ℕ) (hq : 1 ≤ q)
    (N M : ℕ) (ψ : State N q) (hanti : antisymmetric ψ) (hnorm : ‖ψ‖ = 1)
    (η r : ℝ) (hη : 0 < η) (hr : 0 < r)
    (a : Fin M → ℝ≥0) (R : Fin M → Position) :
    (∫⁻ x : Position, nuclearCores a R r x * density ψ x) ≤
      ENNReal.ofReal η * kineticEnergy ψ +
        ENNReal.ofReal (coreErrorConstant q a * η ^ (-(3 : ℝ) / 2) * Real.sqrt r) := by
  by_cases hM : M = 0
  · subst M
    simp only [nuclearCores, Finset.univ_eq_empty, Finset.sum_empty, zero_mul,
      lintegral_zero]
    exact zero_le
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  have hM' : 0 < (M : ℝ) := Nat.cast_pos.mpr hMpos
  have hηM : 0 < η / M := div_pos hη hM'
  have he : (∫⁻ x : Position, nuclearCores a R r x * density ψ x) =
      ∑ k : Fin M, ∫⁻ x : Position,
        Assembly.nucleusCutoff (a k : ℝ) r (R k) x * density ψ x := by
    simp only [nuclearCores, Finset.sum_mul]
    exact lintegral_finsetSum _ (fun k _ =>
      (Assembly.measurable_nucleusCutoff _ _ _).mul (measurable_density ψ))
  rw [he]
  calc
    _ ≤ ∑ k : Fin M, (ENNReal.ofReal (η / M) * kineticEnergy ψ +
        ENNReal.ofReal (youngConstant * ((η / M) * kineticCoefficient q) ^ (-(3 : ℝ) / 2)) *
          ENNReal.ofReal (8 * Real.pi * (a k : ℝ) ^ ((5 : ℝ) / 2) * Real.sqrt r)) := by
      apply Finset.sum_le_sum
      intro k _
      have hk := lintegral_potential_density_le q hq N ψ hanti hnorm (η / M) hηM
        (Assembly.nucleusCutoff (a k : ℝ) r (R k))
      have hi := Assembly.lintegral_nucleusCutoff_rpow (a k : ℝ) r (a k).property hr (R k)
      exact hk.trans (add_le_add le_rfl (mul_le_mul_right hi.le _))
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← mul_assoc]
      have hηeq : (M : ℝ≥0∞) * ENNReal.ofReal (η / M) = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_mul hM'.le,
          mul_div_cancel₀ η hM'.ne']
      rw [hηeq]
      apply congrArg (fun t : ℝ≥0∞ => ENNReal.ofReal η * kineticEnergy ψ + t)
      have hc : 0 ≤ youngConstant * ((η / M) * kineticCoefficient q) ^ (-(3 : ℝ) / 2) :=
        (Assembly.young_screening_coefficient_pos _
          (mul_pos hηM (kineticCoefficient_pos q hq))).le
      simp_rw [← ENNReal.ofReal_mul hc]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by
        exact mul_nonneg hc (by positivity))]
      exact congrArg ENNReal.ofReal (allocated_cost_eq q M hMpos η r hη a)

end LiebThirring.TFCore
end
