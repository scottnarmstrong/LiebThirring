/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.BathtubComparison
public import LiebThirring.TFLattice.BallCellComparison

/-!
# Sharp q-fold lattice squared-moment comparison

The octant unit cells sandwich the sharp radial moment. Spin copies are
counted by multiplicity, not by disjoint physical cells. Source:
Lieb–Simon (1977) III.13, pp. 67–69 (sharp eigenvalue sums).
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace LiebThirring.TFLattice

theorem occupationCells_neumannBallModes_eq {q : ℕ} (t : ℝ≥0) {x : Position}
    (hx : x ∈ spatialBallCells t) : occupationCells (neumannBallModes q t) x = q := by
  classical
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
  rw [occupationCells_eq_card]
  have he : (neumannBallModes q t).filter (fun p => x ∈ latticeCell 1 (unitCellLabel p.1)) =
      {k} ×ˢ (Finset.univ : Finset (Fin q)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_univ, and_true]
    constructor
    · intro hp
      have he : unitCellLabel p.1 = unitCellLabel k := by
        by_contra hne
        exact Set.disjoint_left.mp
          (latticeCell_disjoint (by norm_num : (0 : ℝ) < 1) hne) hp.2 hxz
      exact unitCellLabel_injective he
    · intro hp
      constructor
      · rw [neumannBallModes_eq_product]
        exact Finset.mem_product.mpr ⟨hp ▸ hk, Finset.mem_univ _⟩
      · simpa only [hp] using hxz
  rw [he, Finset.card_product]
  simp

theorem occupationCells_neumannBallModes_zero {q : ℕ} (t : ℝ≥0) {x : Position}
    (hx : x ∉ spatialBallCells t) : occupationCells (neumannBallModes q t) x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro p hp
  apply indicator_of_notMem
  intro hc
  have hk : p.1 ∈ spatialBall t := by
    rw [neumannBallModes_eq_product] at hp
    exact (Finset.mem_product.mp hp).1
  exact hx (mem_iUnion₂.mpr ⟨unitCellLabel p.1, Finset.mem_image.mpr ⟨p.1, hk, rfl⟩, hc⟩)

theorem sum_squaredRadius_neumannBallModes_bounds (q : ℕ) (t : ℝ≥0) :
    (q : ℝ) * (Real.pi / 10 * (t : ℝ) ^ 5) -
        (2 * Real.sqrt 3 * (t : ℝ) + 3) * (neumannBallModes q t).card ≤
      (∑ p ∈ neumannBallModes q t, (squaredRadius p.1 : ℝ)) ∧
    (∑ p ∈ neumannBallModes q t, (squaredRadius p.1 : ℝ)) ≤
      (q : ℝ) * (Real.pi / 10 * ((t : ℝ) + Real.sqrt 3) ^ 5) := by
  have hf := integrable_norm_sq_mul_occupationCells (neumannBallModes q t)
  have hl := integrable_norm_sq_mul_octantBall_const (t : ℝ) q
  have hu := integrable_norm_sq_mul_octantBall_const ((t : ℝ) + Real.sqrt 3) q
  have hlow : (q : ℝ) * (Real.pi / 10 * (t : ℝ) ^ 5) ≤
      ∫ x, ‖x‖ ^ 2 * occupationCells (neumannBallModes q t) x := by
    apply (integral_norm_sq_mul_octantBall_const t.property (q : ℝ)).symm.trans_le
    apply integral_mono hl hf
    intro x
    dsimp only
    by_cases hx : x ∈ octantBall (t : ℝ)
    · rw [indicator_of_mem hx, occupationCells_neumannBallModes_eq t
        (octant_ball_subset_spatialBallCells t hx)]
    · rw [indicator_of_notMem hx, mul_zero]
      exact mul_nonneg (sq_nonneg _) (occupationCells_nonneg _ _)
  have hupp : (∫ x, ‖x‖ ^ 2 * occupationCells (neumannBallModes q t) x) ≤
      (q : ℝ) * (Real.pi / 10 * ((t : ℝ) + Real.sqrt 3) ^ 5) := by
    apply LE.le.trans_eq _ (integral_norm_sq_mul_octantBall_const
      (add_nonneg t.property (Real.sqrt_nonneg 3)) (q : ℝ))
    apply integral_mono hf hu
    intro x
    dsimp only
    by_cases hx : x ∈ octantBall ((t : ℝ) + Real.sqrt 3)
    · rw [indicator_of_mem hx]
      exact mul_le_mul_of_nonneg_left (occupationCells_le _ _) (sq_nonneg _)
    · rw [indicator_of_notMem hx, occupationCells_neumannBallModes_zero t
        (fun hc => hx (spatialBallCells_subset_octant_ball t hc)), mul_zero]
  have hb := integral_norm_sq_mul_occupationCells_bounds (neumannBallModes q t)
    (fun p hp => (mem_spatialBall_iff_norm t p.1).mp
      ((Finset.mem_product.mp ((neumannBallModes_eq_product q t) ▸ hp)).1))
  constructor
  · linarith only [hlow, hb.2]
  · exact hb.1.trans hupp

end LiebThirring.TFLattice

end
