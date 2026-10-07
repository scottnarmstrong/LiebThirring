/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.ScalingEnergy

/-! # Molecular Thomas--Fermi scaling -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- Exact molecular TF scaling, in the normalization of the theorem. -/
theorem tfEnergy_scaling_library {M : ℕ} (a : {a : ℝ // 0 < a})
    (ν : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (α : {α : ℝ≥0 // 0 < α}) :
    tfEnergy a (α.val * ν) (fun k => α.val * z k)
      (fun k => ((α.val : ℝ) ^ (-(1 : ℝ) / 3)) • R k) =
    (((α.val : ℝ) ^ ((7 : ℝ) / 3) : ℝ) : EReal) * tfEnergy a ν z R := by
  let β : ℝ := (α.val : ℝ) ^ ((1 : ℝ) / 3)
  have hα : 0 < (α.val : ℝ) := by exact_mod_cast α.property
  have hβ : 0 < β := Real.rpow_pos_of_pos hα _
  have hcube : β ^ 3 = (α.val : ℝ) := by
    dsimp [β]
    convert Real.rpow_inv_natCast_pow hα.le (n := 3) (by norm_num) using 1
    all_goals norm_num
  have hnn : (Real.toNNReal β) ^ 3 = α.val := by
    ext
    simp only [NNReal.coe_pow, Real.coe_toNNReal β hβ.le, hcube]
  have hinv : β⁻¹ = (α.val : ℝ) ^ (-(1 : ℝ) / 3) := by
    dsimp [β]
    have he : (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) := by ring
    rw [he]
    rw [Real.rpow_neg hα.le]
  have hseven : β ^ 7 = (α.val : ℝ) ^ ((7 : ℝ) / 3) := by
    dsimp [β]
    rw [← Real.rpow_mul_natCast hα.le]
    congr 1
    norm_num
  have hsevenE : (β : EReal) ^ 7 =
      (((α.val : ℝ) ^ ((7 : ℝ) / 3) : ℝ) : EReal) := by
    rw [← EReal.coe_pow, hseven]
  simpa only [hnn, hinv, hsevenE] using
    tfEnergy_dilation a ν z R β hβ

end LiebThirring

end
