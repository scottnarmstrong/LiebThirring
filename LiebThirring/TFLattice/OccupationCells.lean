/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.CellMoments

/-!
# Unit-cell density of a finite occupation

Each spin mode puts unit mass on its positive unit cell. The multiplicity
never exceeds q. This supplies the continuous comparison used in the sharp
first-n lower bound. Source: Lieb–Simon (1977) III.13, pp. 67–69 (sharp eigenvalue sums).
-/

@[expose] public section

open MeasureTheory Set
open scoped Classical

namespace LiebThirring.TFLattice

noncomputable def occupationCells {q : ℕ} (s : Finset (ModeIndex q)) : Position → ℝ :=
  fun x => ∑ p ∈ s, (latticeCell 1 (unitCellLabel p.1)).indicator (fun _ => 1) x

theorem occupationCells_eq_card {q : ℕ} (s : Finset (ModeIndex q)) (x : Position) :
    occupationCells s x = ((s.filter fun p : ModeIndex q => x ∈ latticeCell 1 (unitCellLabel p.1)).card : ℝ) := by
  classical
  simp only [occupationCells, Finset.sum_filter, indicator_apply, Finset.card_eq_sum_ones,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem occupationCells_nonneg {q : ℕ} (s : Finset (ModeIndex q)) (x : Position) :
    0 ≤ occupationCells s x := by
  rw [occupationCells_eq_card]
  exact Nat.cast_nonneg _

theorem occupationCells_le {q : ℕ} (s : Finset (ModeIndex q)) (x : Position) :
    occupationCells s x ≤ q := by
  classical
  rw [occupationCells_eq_card]
  apply Nat.cast_le.mpr
  calc
    _ ≤ (Finset.univ : Finset (Fin q)).card := by
      apply Finset.card_le_card_of_injOn (f := Prod.snd)
      · intro p hp
        exact Finset.mem_univ _
      · intro p hp r hr hpr
        have hp' := (Finset.mem_filter.mp hp).2
        have hr' := (Finset.mem_filter.mp hr).2
        have he : unitCellLabel p.1 = unitCellLabel r.1 := by
          by_contra hne
          exact Set.disjoint_left.mp
            (latticeCell_disjoint (by norm_num : (0 : ℝ) < 1) hne) hp' hr'
        exact Prod.ext (unitCellLabel_injective he) hpr
    _ = q := by simp

theorem occupationCells_zero_of_not_octant {q : ℕ} (s : Finset (ModeIndex q))
    {x : Position} (hx : ¬∀ i, 0 ≤ x i) : occupationCells s x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro p hp
  apply indicator_of_notMem
  intro hc
  apply hx
  intro i
  exact (show (0 : ℝ) ≤ (p.1 i : ℝ) from Nat.cast_nonneg _).trans
    (by simpa [latticeCell, unitCellLabel] using (hc i).1)

theorem integrable_occupationCells {q : ℕ} (s : Finset (ModeIndex q)) :
    Integrable (occupationCells s) := by
  apply integrable_finsetSum
  intro p hp
  exact (integrableOn_unitCell_const (unitCellLabel p.1) 1).integrable_indicator
    (measurableSet_latticeCell 1 _)

theorem integral_occupationCells {q : ℕ} (s : Finset (ModeIndex q)) :
    (∫ x, occupationCells s x) = s.card := by
  change (∫ x, ∑ p ∈ s, (latticeCell 1 (unitCellLabel p.1)).indicator (fun _ => (1 : ℝ)) x) = _
  rw [integral_finsetSum _ (fun p _ =>
    (integrableOn_unitCell_const (unitCellLabel p.1) 1).integrable_indicator
      (measurableSet_latticeCell 1 _))]
  simp only [integral_indicator (measurableSet_latticeCell 1 _), integral_unitCell_const,
    Finset.sum_const, nsmul_eq_mul, mul_one]

theorem norm_sq_mul_occupationCells {q : ℕ} (s : Finset (ModeIndex q)) :
    (fun x => ‖x‖ ^ 2 * occupationCells s x) =
      fun x => ∑ p ∈ s, (latticeCell 1 (unitCellLabel p.1)).indicator (fun x => ‖x‖ ^ 2) x := by
  classical
  ext x
  simp only [occupationCells, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hx : x ∈ latticeCell 1 (unitCellLabel p.1) <;> simp [hx]

theorem integrable_norm_sq_mul_occupationCells {q : ℕ} (s : Finset (ModeIndex q)) :
    Integrable (fun x => ‖x‖ ^ 2 * occupationCells s x) := by
  rw [norm_sq_mul_occupationCells]
  apply integrable_finsetSum
  intro p hp
  exact (integrableOn_unitCell_norm_sq (unitCellLabel p.1)).integrable_indicator
    (measurableSet_latticeCell 1 _)

theorem integral_norm_sq_mul_occupationCells_bounds {q : ℕ} (s : Finset (ModeIndex q))
    {t : ℝ} (ht : ∀ p ∈ s, ‖latticeCorner 1 (unitCellLabel p.1)‖ ≤ t) :
    (∑ p ∈ s, (squaredRadius p.1 : ℝ)) ≤ (∫ x, ‖x‖ ^ 2 * occupationCells s x) ∧
    (∫ x, ‖x‖ ^ 2 * occupationCells s x) ≤
      (∑ p ∈ s, (squaredRadius p.1 : ℝ)) + (2 * Real.sqrt 3 * t + 3) * s.card := by
  rw [norm_sq_mul_occupationCells, integral_finsetSum _ (fun p _ =>
    (integrableOn_unitCell_norm_sq (unitCellLabel p.1)).integrable_indicator
      (measurableSet_latticeCell 1 _))]
  simp only [integral_indicator (measurableSet_latticeCell 1 _)]
  constructor
  · exact Finset.sum_le_sum fun p hp => (integral_unitCell_norm_sq_bounds p.1 (ht p hp)).1
  · calc
      _ ≤ ∑ p ∈ s, ((squaredRadius p.1 : ℝ) + (2 * Real.sqrt 3 * t + 3)) :=
        Finset.sum_le_sum fun p hp => by simpa only [add_assoc] using (integral_unitCell_norm_sq_bounds p.1 (ht p hp)).2
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const]; simp only [nsmul_eq_mul]; ring

end LiebThirring.TFLattice

end
