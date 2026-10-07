/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.BallModes
public import LiebThirring.Packing.LatticeCounting

/-!
# Spatial lattice balls and spin multiplicity

Separate the geometric unit-cell count from the q-fold spin count. The spin
copies have identical spatial cells and are counted algebraically, rather than
as a disjoint union in physical space. Source: Lieb–Simon III.13, pp. 67–69.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal

namespace LiebThirring.TFLattice

noncomputable def spatialBall (t : ℝ≥0) : Finset (Fin 3 → ℕ) :=
  (neumannBallModes 1 t).image Prod.fst

theorem mem_spatialBall (t : ℝ≥0) (k : Fin 3 → ℕ) :
    k ∈ spatialBall t ↔ (squaredRadius k : ℝ) ≤ (t : ℝ) ^ 2 := by
  classical
  constructor
  · intro hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    exact (mem_neumannBallModes (q := 1) (t := t) (p := p)).mp hp
  · intro hk
    exact Finset.mem_image.mpr ⟨(k, 0), (mem_neumannBallModes (q := 1) (t := t)).mpr hk, rfl⟩

theorem neumannBallModes_eq_product (q : ℕ) (t : ℝ≥0) :
    neumannBallModes q t = spatialBall t ×ˢ Finset.univ := by
  classical
  ext p
  simp only [Finset.mem_product, Finset.mem_univ, and_true, mem_neumannBallModes,
    mem_spatialBall]

theorem card_neumannBallModes_eq_mul (q : ℕ) (t : ℝ≥0) :
    (neumannBallModes q t).card = q * (spatialBall t).card := by
  rw [neumannBallModes_eq_product, Finset.card_product]
  simp [mul_comm]

def unitCellLabel (k : Fin 3 → ℕ) : LatticeIndex := fun i => (k i : ℤ)

theorem unitCellLabel_injective : Function.Injective unitCellLabel := by
  intro k l he
  funext i
  have hi : (k i : ℤ) = l i := congrFun he i
  exact_mod_cast hi

noncomputable def spatialBallLabels (t : ℝ≥0) : Finset LatticeIndex :=
  (spatialBall t).image unitCellLabel

theorem card_spatialBallLabels (t : ℝ≥0) :
    (spatialBallLabels t).card = (spatialBall t).card :=
  Finset.card_image_of_injective _ unitCellLabel_injective

noncomputable def spatialBallCells (t : ℝ≥0) : Set Position :=
  latticeCovered 1 (spatialBallLabels t)

theorem volume_real_spatialBallCells (t : ℝ≥0) :
    volume.real (spatialBallCells t) = (spatialBall t).card := by
  rw [spatialBallCells, volume_real_latticeCovered (by norm_num), card_spatialBallLabels]
  norm_num

theorem norm_unitCellCorner_sq (k : Fin 3 → ℕ) :
    ‖latticeCorner 1 (unitCellLabel k)‖ ^ 2 = (squaredRadius k : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [latticeCorner, unitCellLabel, PiLp.toLp_apply, one_mul, Int.cast_natCast,
    squaredRadius, Nat.cast_sum, Nat.cast_pow]

theorem mem_spatialBall_iff_norm (t : ℝ≥0) (k : Fin 3 → ℕ) :
    k ∈ spatialBall t ↔ ‖latticeCorner 1 (unitCellLabel k)‖ ≤ (t : ℝ) := by
  rw [mem_spatialBall, ← norm_unitCellCorner_sq]
  exact sq_le_sq₀ (norm_nonneg _) t.property

end LiebThirring.TFLattice

end
