/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Coulomb

/-!
# Geometry of a remote orbital

A ball of radius `L` centered at distance `R + 4L`
is separated from the old radius-`R` ball by at least `3L`.
The mixed Coulomb costs are bounded before integration.
-/

public section

open MeasureTheory WithLp Set
open scoped ENNReal NNReal

namespace LiebThirring

/-- The center on the first spatial axis prescribed by the escape construction. -/
@[expose] def escapeCenter (R L : ℝ) : Position :=
  PiLp.single 2 0 (R + 4 * L)

theorem norm_escapeCenter {R L : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) :
    ‖escapeCenter R L‖ = R + 4 * L := by
  rw [escapeCenter, PiLp.norm_single, Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg hR (mul_nonneg (by norm_num) hL))]

/-- Separation of the old and remote balls with the exact factor three. -/
theorem escape_remote_distance {R L : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    {x y : Position} (hx : ‖x‖ ≤ R) (hy : ‖y - escapeCenter R L‖ ≤ L) :
    3 * L ≤ ‖x - y‖ := by
  have ha := norm_add_le (escapeCenter R L - y) (y - x)
  have hb := norm_add_le (escapeCenter R L - x) x
  rw [sub_add_sub_cancel] at ha
  rw [sub_add_cancel, norm_escapeCenter hR hL] at hb
  rw [norm_sub_rev (escapeCenter R L) y, norm_sub_rev y x] at ha
  linarith only [ha, hb, hx, hy]

/-- One mixed pair costs at most the reciprocal separation. -/
theorem escape_coulombKernel_le {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    {x y : Position} (hx : ‖x‖ ≤ R) (hy : ‖y - escapeCenter R L‖ ≤ L) :
    coulombKernel x y ≤ (ENNReal.ofReal (3 * L))⁻¹ := by
  apply ENNReal.inv_le_inv.mpr
  exact ENNReal.ofReal_le_ofReal (escape_remote_distance hR hL.le hx hy)

/-- Summing the `n` mixed pairs retains the exact pair count. -/
theorem escape_mixed_repulsion_le {n : ℕ} {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (x : Fin n → Position) {y : Position} (hx : ∀ i, ‖x i‖ ≤ R)
    (hy : ‖y - escapeCenter R L‖ ≤ L) :
    (∑ i, coulombKernel (x i) y) ≤ (n : ℝ≥0∞) * (ENNReal.ofReal (3 * L))⁻¹ := by
  calc
    _ ≤ ∑ _ : Fin n, (ENNReal.ofReal (3 * L))⁻¹ :=
      Finset.sum_le_sum (fun i _ => escape_coulombKernel_le hR hL (hx i) hy)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Compact many-particle support lies in a common radius for every electron. -/
theorem escape_exists_support_radius {H : Type*} {n : ℕ}
    [NormedAddCommGroup H] (f : Configuration n → H)
    (hf : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ tsupport f, ∀ i : Fin n, ‖particlePosition x i‖ ≤ R := by
  obtain ⟨R, hR, hb⟩ := hf.isBounded.exists_pos_norm_le
  refine ⟨R, hR, ?_⟩
  intro x hx i
  have hp : ‖particlePosition x i‖ ≤ ‖x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.real_norm_sq_eq, particlePosition]
    rw [Fintype.sum_prod_type]
    exact Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun a _ => sq_nonneg (x (j, a))))
      (Finset.mem_univ i)
  exact hp.trans (hb x hx)

end LiebThirring

end
