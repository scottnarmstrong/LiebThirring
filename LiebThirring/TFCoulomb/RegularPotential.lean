/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.NuclearPotential

/-!
# Capped nuclear potentials

This module defines the continuous Coulomb potential obtained by capping every
nuclear singularity at radius `δ`, and proves its elementary global bounds.
-/

@[expose] public section

open scoped BigOperators NNReal

namespace LiebThirring

/-- The positive nuclear potential with every Coulomb singularity capped at radius `δ`. -/
noncomputable def tfCappedNuclearPotential {M : ℕ} (δ : ℝ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (x : Position) : ℝ :=
  ∑ k : Fin M, (z k : ℝ) / max δ ‖x - R k‖

/-- The capped nuclear potential is nonnegative when the cutoff is positive. -/
theorem tfCappedNuclearPotential_nonneg {M : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (x : Position) :
    0 ≤ tfCappedNuclearPotential δ z R x := by
  unfold tfCappedNuclearPotential
  exact Finset.sum_nonneg fun k _ ↦ div_nonneg (z k).coe_nonneg
    (le_trans hδ.le (le_max_left δ ‖x - R k‖))

/-- The total nuclear charge divided by `δ` bounds the capped potential. -/
theorem tfCappedNuclearPotential_le {M : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (x : Position) :
    tfCappedNuclearPotential δ z R x ≤ (∑ k : Fin M, (z k : ℝ)) / δ := by
  unfold tfCappedNuclearPotential
  rw [Finset.sum_div]
  exact Finset.sum_le_sum fun k _ ↦ div_le_div_of_nonneg_left (z k).coe_nonneg hδ
    (le_max_left δ ‖x - R k‖)

theorem capped_inv_abs_sub_le {δ a b : ℝ} (hδ : 0 < δ) :
    |(max δ a)⁻¹ - (max δ b)⁻¹| ≤ |a - b| / δ ^ 2 := by
  have hA : 0 < max δ a := hδ.trans_le (le_max_left _ _)
  have hB : 0 < max δ b := hδ.trans_le (le_max_left _ _)
  rw [inv_sub_inv hA.ne' hB.ne', abs_div, abs_mul]
  rw [abs_of_pos hA, abs_of_pos hB]
  have hmax : |max δ b - max δ a| ≤ |b - a| := by
    simpa only [max_comm] using abs_max_sub_max_le_abs b a δ
  have hden : δ ^ 2 ≤ max δ a * max δ b := by
    nlinarith only [le_max_left δ a, le_max_left δ b, hδ]
  rw [div_le_div_iff₀ (mul_pos hA hB) (sq_pos_of_pos hδ)]
  calc
    |max δ b - max δ a| * δ ^ 2 ≤ |a - b| * δ ^ 2 :=
      mul_le_mul_of_nonneg_right (by simpa only [abs_sub_comm] using hmax) (sq_nonneg δ)
    _ ≤ |a - b| * (max δ a * max δ b) :=
      mul_le_mul_of_nonneg_left hden (abs_nonneg _)

theorem capped_inverse_distance_abs_sub_le (δ : ℝ) (hδ : 0 < δ) (R x y : Position) :
    |(max δ ‖x - R‖)⁻¹ - (max δ ‖y - R‖)⁻¹| ≤ dist x y / δ ^ 2 := by
  refine (capped_inv_abs_sub_le hδ).trans ?_
  exact div_le_div_of_nonneg_right
    (by simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using
      abs_norm_sub_norm_le (x - R) (y - R)) (sq_nonneg δ)

/-- Global Lipschitz estimate for the capped nuclear potential. -/
theorem abs_tfCappedNuclearPotential_sub_le {M : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (x y : Position) :
    |tfCappedNuclearPotential δ z R x - tfCappedNuclearPotential δ z R y| ≤
      ((∑ k : Fin M, (z k : ℝ)) / δ ^ 2) * dist x y := by
  unfold tfCappedNuclearPotential
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ k : Fin M, ((z k : ℝ) / max δ ‖x - R k‖ -
        (z k : ℝ) / max δ ‖y - R k‖)| ≤
        ∑ k : Fin M, |(z k : ℝ) / max δ ‖x - R k‖ -
          (z k : ℝ) / max δ ‖y - R k‖| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin M, (z k : ℝ) * (dist x y / δ ^ 2) := by
      exact Finset.sum_le_sum fun k _ ↦ by
        rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, abs_mul,
          abs_of_nonneg (z k).coe_nonneg]
        exact mul_le_mul_of_nonneg_left
          (capped_inverse_distance_abs_sub_le δ hδ (R k) x y) (z k).coe_nonneg
    _ = ((∑ k : Fin M, (z k : ℝ)) / δ ^ 2) * dist x y := by
      rw [← Finset.sum_mul]
      ring

/-- The capped nuclear potential is continuous for every positive cutoff. -/
theorem continuous_tfCappedNuclearPotential {M : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    Continuous (tfCappedNuclearPotential δ z R) := by
  unfold tfCappedNuclearPotential
  apply continuous_finsetSum
  intro k _
  apply continuous_const.div₀ (by fun_prop)
  intro x
  exact ne_of_gt (hδ.trans_le (le_max_left δ ‖x - R k‖))

end LiebThirring

end
