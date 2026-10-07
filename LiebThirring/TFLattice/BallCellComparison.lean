/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.SpatialBall
public import LiebThirring.TFLattice.OctantBall

/-!
# Sharp positive-octant unit-cell comparison

The Neumann unit cells contain the octant ball at the site radius and are
contained in the octant ball with radius increased by √3. Exact volume gives
the leading coefficient π/6, with a quadratic boundary error. Source:
Lieb–Simon (1977) III.13, pp. 67–69 (sharp eigenvalue sums).
-/

public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace LiebThirring.TFLattice

theorem spatialBallCells_subset_octant_ball (t : ℝ≥0) :
    spatialBallCells t ⊆ {x : Position | (∀ i, 0 ≤ x i) ∧ ‖x‖ ≤ (t : ℝ) + Real.sqrt 3} := by
  intro x hx
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
  constructor
  · intro i
    have hlo := (hxz i).1
    change 1 * ((k i : ℤ) : ℝ) ≤ x i at hlo
    exact (by positivity : (0 : ℝ) ≤ 1 * ((k i : ℤ) : ℝ)).trans hlo
  · have hc := (mem_spatialBall_iff_norm t k).mp hk
    have hd := dist_le_lattice_diameter (by norm_num : (0 : ℝ) ≤ 1)
      (latticeCell_subset_closedCell 1 _ hxz)
      (latticeCorner_mem_closedCell (by norm_num : (0 : ℝ) ≤ 1) (unitCellLabel k))
    have ht := norm_le_norm_add_norm_sub' x (latticeCorner 1 (unitCellLabel k))
    rw [dist_eq_norm] at hd
    norm_num at hd
    linarith

theorem octant_ball_subset_spatialBallCells (t : ℝ≥0) :
    {x : Position | (∀ i, 0 ≤ x i) ∧ ‖x‖ ≤ (t : ℝ)} ⊆ spatialBallCells t := by
  intro x hx
  let k : Fin 3 → ℕ := fun i => ⌊x i⌋₊
  have hcell : x ∈ latticeCell 1 (unitCellLabel k) := by
    intro i
    change 1 * ((⌊x i⌋₊ : ℤ) : ℝ) ≤ x i ∧ x i < 1 * (((⌊x i⌋₊ : ℤ) : ℝ) + 1)
    simpa only [Int.cast_natCast, one_mul] using
      And.intro (Nat.floor_le (hx.1 i)) (Nat.lt_floor_add_one (x i))
  have hsq : ‖latticeCorner 1 (unitCellLabel k)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_unitCellCorner_sq, EuclideanSpace.real_norm_sq_eq]
    simp only [squaredRadius, Nat.cast_sum, Nat.cast_pow]
    apply Finset.sum_le_sum
    intro i _
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (hx.1 i)) 2
  have hn : ‖latticeCorner 1 (unitCellLabel k)‖ ≤ (t : ℝ) :=
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq).trans hx.2
  have hk := (mem_spatialBall_iff_norm t k).mpr hn
  exact mem_iUnion₂.mpr ⟨unitCellLabel k, Finset.mem_image.mpr ⟨k, hk, rfl⟩, hcell⟩

/-- Exact leading constant with a uniform boundary displacement. -/
theorem card_spatialBall_bounds (t : ℝ≥0) :
    Real.pi / 6 * (t : ℝ) ^ 3 ≤ (spatialBall t).card ∧
      ((spatialBall t).card : ℝ) ≤ Real.pi / 6 * ((t : ℝ) + Real.sqrt 3) ^ 3 := by
  have hfinite (r : ℝ) : volume {x : Position | (∀ i, 0 ≤ x i) ∧ ‖x‖ ≤ r} ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_mono (show
      {x : Position | (∀ i, 0 ≤ x i) ∧ ‖x‖ ≤ r} ⊆ closedBall 0 r from
        fun x hx => by simpa only [mem_closedBall, dist_zero_right] using hx.2))
    exact (isCompact_closedBall (0 : Position) r).measure_lt_top
  have hcells : volume (spatialBallCells t) ≠ ∞ :=
    ne_of_lt ((measure_mono (spatialBallCells_subset_octant_ball t)).trans_lt
      (lt_top_iff_ne_top.mpr (hfinite _)))
  constructor
  · have he := measureReal_mono (octant_ball_subset_spatialBallCells t) hcells
    rw [volume_real_spatialBallCells] at he
    exact (volume_real_octant_norm_le t.property).symm.trans_le he
  · have he := measureReal_mono (spatialBallCells_subset_octant_ball t) (hfinite _)
    rw [volume_real_spatialBallCells] at he
    exact he.trans_eq (volume_real_octant_norm_le (add_nonneg t.property (Real.sqrt_nonneg 3)))

theorem card_neumannBallModes_volume_bounds (q : ℕ) (t : ℝ≥0) :
    (q : ℝ) * (Real.pi / 6) * (t : ℝ) ^ 3 ≤ (neumannBallModes q t).card ∧
      ((neumannBallModes q t).card : ℝ) ≤
        (q : ℝ) * (Real.pi / 6) * ((t : ℝ) + Real.sqrt 3) ^ 3 := by
  rw [card_neumannBallModes_eq_mul]
  push_cast
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (card_spatialBall_bounds t).1
      (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (card_spatialBall_bounds t).2
      (Nat.cast_nonneg q : (0 : ℝ) ≤ q)

end LiebThirring.TFLattice

end
