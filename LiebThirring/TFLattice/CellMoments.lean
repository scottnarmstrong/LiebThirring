/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.SpatialBall

/-!
# Comparing the squared radius at a site with its unit-cell moment

Positive lattice cells preserve coordinatewise order. Their Euclidean
radius differs from the lower corner radius by at most √3. Source:
Lieb–Simon (1977) III.13, pp. 67–69 (sharp eigenvalue sums).
-/

public section

open MeasureTheory Set Metric Filter

namespace LiebThirring.TFLattice

theorem unitCell_norm_le (z : LatticeIndex) {x : Position}
    (hx : x ∈ latticeCell 1 z) : ‖x‖ ≤ ‖latticeCorner 1 z‖ + Real.sqrt 3 := by
  have hd := dist_le_lattice_diameter (by norm_num : (0 : ℝ) ≤ 1)
    (latticeCell_subset_closedCell 1 z hx)
    (latticeCorner_mem_closedCell (by norm_num : (0 : ℝ) ≤ 1) z)
  have ht := norm_le_norm_add_norm_sub' x (latticeCorner 1 z)
  rw [dist_eq_norm] at hd
  norm_num at hd
  linarith

theorem integrableOn_unitCell_norm_sq (z : LatticeIndex) :
    IntegrableOn (fun x : Position => ‖x‖ ^ 2) (latticeCell 1 z) := by
  have hc : Continuous (fun x : Position => ‖x‖ ^ 2) := continuous_norm.pow 2
  apply (hc.continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Position) (‖latticeCorner 1 z‖ + Real.sqrt 3))).mono_set
  intro x hx
  simpa only [mem_closedBall, dist_zero_right] using unitCell_norm_le z hx

theorem volume_real_unitCell (z : LatticeIndex) : volume.real (latticeCell 1 z) = 1 := by
  rw [Measure.real, volume_latticeCell (by norm_num : (0 : ℝ) ≤ 1)]
  norm_num

theorem integrableOn_unitCell_const (z : LatticeIndex) (c : ℝ) :
    IntegrableOn (fun _ : Position => c) (latticeCell 1 z) := by
  exact integrableOn_const (by
    rw [volume_latticeCell (by norm_num : (0 : ℝ) ≤ 1)]
    exact ENNReal.ofReal_ne_top) (by exact enorm_ne_top)

theorem integral_unitCell_const (z : LatticeIndex) (c : ℝ) :
    (∫ _ in latticeCell 1 z, c) = c := by
  rw [setIntegral_const, volume_real_unitCell, one_smul]

theorem unitCell_squared_radius_le (k : Fin 3 → ℕ) {x : Position}
    (hx : x ∈ latticeCell 1 (unitCellLabel k)) : (squaredRadius k : ℝ) ≤ ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [squaredRadius, Nat.cast_sum, Nat.cast_pow]
  apply Finset.sum_le_sum
  intro i _
  have hi : (k i : ℝ) ≤ x i := by simpa [latticeCell, unitCellLabel] using (hx i).1
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) hi 2

theorem unitCell_norm_sq_le {t : ℝ} (k : Fin 3 → ℕ)
    (hk : ‖latticeCorner 1 (unitCellLabel k)‖ ≤ t) {x : Position}
    (hx : x ∈ latticeCell 1 (unitCellLabel k)) :
    ‖x‖ ^ 2 ≤ (squaredRadius k : ℝ) + 2 * Real.sqrt 3 * t + 3 := by
  have hn := unitCell_norm_le (unitCellLabel k) hx
  have hsq := pow_le_pow_left₀ (norm_nonneg x) hn 2
  have hroot := Real.sqrt_nonneg (3 : ℝ)
  have he := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hmul := mul_le_mul_of_nonneg_left hk (show 0 ≤ 2 * Real.sqrt 3 by positivity)
  rw [← norm_unitCellCorner_sq]
  nlinarith only [hsq, he, hmul]

theorem integral_unitCell_norm_sq_bounds {t : ℝ} (k : Fin 3 → ℕ)
    (hk : ‖latticeCorner 1 (unitCellLabel k)‖ ≤ t) :
    (squaredRadius k : ℝ) ≤ (∫ x in latticeCell 1 (unitCellLabel k), ‖x‖ ^ 2) ∧
    (∫ x in latticeCell 1 (unitCellLabel k), ‖x‖ ^ 2) ≤
      (squaredRadius k : ℝ) + 2 * Real.sqrt 3 * t + 3 := by
  constructor
  · rw [← integral_unitCell_const (unitCellLabel k) (squaredRadius k : ℝ)]
    exact setIntegral_mono_on (integrableOn_unitCell_const _ _) (integrableOn_unitCell_norm_sq _)
      (measurableSet_latticeCell 1 _) (fun x hx => unitCell_squared_radius_le k hx)
  · rw [← integral_unitCell_const (unitCellLabel k) ((squaredRadius k : ℝ) + 2 * Real.sqrt 3 * t + 3)]
    exact setIntegral_mono_on (integrableOn_unitCell_norm_sq _) (integrableOn_unitCell_const _ _)
      (measurableSet_latticeCell 1 _) (fun x hx => unitCell_norm_sq_le k hk hx)

end LiebThirring.TFLattice

end
