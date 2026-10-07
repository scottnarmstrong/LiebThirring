/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Configuration

/-!
# Cubic lattice geometry in the physical Euclidean space

The half-open cells form an exact partition. The closed cells are used when
selecting cubes strictly inside a region. This avoids any appeal to a choice of
representative on lattice faces. Lieb–Lebowitz (1972) Lemma 3.1, p. 333.
-/

public section

open Set MeasureTheory Metric

namespace LiebThirring

noncomputable section

/-- Integer labels of a three-dimensional cubic lattice. -/
abbrev LatticeIndex := Fin 3 → ℤ

/-- Lower corner of the cell with integer label `z`. -/
@[expose] def latticeCorner (ℓ : ℝ) (z : LatticeIndex) : Position :=
  WithLp.toLp 2 (fun i => ℓ * (z i : ℝ))

/-- Centre of the cell with integer label `z`. -/
@[expose] def latticeCenter (ℓ : ℝ) (z : LatticeIndex) : Position :=
  WithLp.toLp 2 (fun i => ℓ * ((z i : ℝ) + 1 / 2))

/-- The half-open cell used for counting and exact volume partitions. -/
@[expose] def latticeCell (ℓ : ℝ) (z : LatticeIndex) : Set Position :=
  {x | ∀ i, ℓ * (z i : ℝ) ≤ x i ∧ x i < ℓ * ((z i : ℝ) + 1)}

/-- The closed cube used for eligibility. -/
@[expose] def latticeClosedCell (ℓ : ℝ) (z : LatticeIndex) : Set Position :=
  {x | ∀ i, ℓ * (z i : ℝ) ≤ x i ∧ x i ≤ ℓ * ((z i : ℝ) + 1)}

/-- Unique half-open cell label of a point at a positive lattice spacing. -/
@[expose] noncomputable def latticeLabel (ℓ : ℝ) (x : Position) : LatticeIndex :=
  fun i => ⌊x i / ℓ⌋

theorem latticeCell_subset_closedCell (ℓ : ℝ) (z : LatticeIndex) :
    latticeCell ℓ z ⊆ latticeClosedCell ℓ z := by
  intro x hx i
  exact ⟨(hx i).1, (hx i).2.le⟩

theorem latticeCorner_mem_closedCell {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (z : LatticeIndex) :
    latticeCorner ℓ z ∈ latticeClosedCell ℓ z := by
  intro i
  change ℓ * (z i : ℝ) ≤ ℓ * (z i : ℝ) ∧
    ℓ * (z i : ℝ) ≤ ℓ * ((z i : ℝ) + 1)
  constructor
  · exact le_rfl
  · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hℓ

theorem mem_latticeCell_label {ℓ : ℝ} (hℓ : 0 < ℓ) (x : Position) :
    x ∈ latticeCell ℓ (latticeLabel ℓ x) := by
  intro i
  change ℓ * (⌊x i / ℓ⌋ : ℝ) ≤ x i ∧ x i < ℓ * ((⌊x i / ℓ⌋ : ℝ) + 1)
  constructor
  · simpa only [mul_comm] using (le_div_iff₀ hℓ).mp (Int.floor_le (x i / ℓ))
  · simpa only [mul_comm] using (div_lt_iff₀ hℓ).mp (Int.lt_floor_add_one (x i / ℓ))

theorem latticeLabel_eq_of_mem {ℓ : ℝ} (hℓ : 0 < ℓ) {z : LatticeIndex}
    {x : Position} (hx : x ∈ latticeCell ℓ z) : latticeLabel ℓ x = z := by
  funext i
  apply Int.floor_eq_iff.mpr
  constructor
  · exact (le_div_iff₀ hℓ).mpr (by simpa only [mul_comm] using (hx i).1)
  · exact (div_lt_iff₀ hℓ).mpr (by simpa only [mul_comm] using (hx i).2)

theorem latticeCell_disjoint {ℓ : ℝ} (hℓ : 0 < ℓ) {z w : LatticeIndex}
    (hzw : z ≠ w) : Disjoint (latticeCell ℓ z) (latticeCell ℓ w) := by
  apply disjoint_left.mpr
  intro x hx hz
  exact hzw ((latticeLabel_eq_of_mem hℓ hx).symm.trans (latticeLabel_eq_of_mem hℓ hz))

theorem iUnion_latticeCell {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (⋃ z : LatticeIndex, latticeCell ℓ z) = univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨latticeLabel ℓ x, mem_latticeCell_label hℓ x⟩

theorem measurableSet_latticeCell (ℓ : ℝ) (z : LatticeIndex) :
    MeasurableSet (latticeCell ℓ z) := by
  have heq : latticeCell ℓ z = (⋂ i, {x : Position | ℓ * (z i : ℝ) ≤ x i ∧
    x i < ℓ * ((z i : ℝ) + 1)})
  := by ext x; simp only [latticeCell, mem_iInter, mem_ofPred_eq]
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_Ico.preimage (by fun_prop : Measurable (fun x : Position => x i)))

theorem measurableSet_latticeClosedCell (ℓ : ℝ) (z : LatticeIndex) :
    MeasurableSet (latticeClosedCell ℓ z) := by
  have heq : latticeClosedCell ℓ z = (⋂ i, {x : Position | ℓ * (z i : ℝ) ≤ x i ∧
    x i ≤ ℓ * ((z i : ℝ) + 1)})
  := by ext x; simp only [latticeClosedCell, mem_iInter, mem_ofPred_eq]
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_Icc.preimage (by fun_prop : Measurable (fun x : Position => x i)))

/-- The volume of every half-open lattice cell is exactly `ℓ³`. -/
theorem volume_latticeCell {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (z : LatticeIndex) :
    volume (latticeCell ℓ z) = ENNReal.ofReal (ℓ ^ 3) := by
  have hpre : latticeCell ℓ z = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹'
      (pi univ fun i => Ico (ℓ * (z i : ℝ)) (ℓ * ((z i : ℝ) + 1))) := by
    ext x
    simp only [latticeCell, mem_ofPred_eq, mem_preimage, mem_pi, mem_univ, forall_const,
      mem_Ico]
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding,
    Real.volume_pi_Ico]
  have hs : ∀ i : Fin 3, ℓ * ((z i : ℝ) + 1) - ℓ * (z i : ℝ) = ℓ := by
    intro i
    ring
  simp only [hs, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow hℓ 3).symm

/-- Euclidean diameter control retains the sharp cube constant `√3`. -/
theorem dist_le_lattice_diameter {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {z : LatticeIndex}
    {x y : Position} (hx : x ∈ latticeClosedCell ℓ z)
    (hy : y ∈ latticeClosedCell ℓ z) : dist x y ≤ Real.sqrt 3 * ℓ := by
  have hc : ∀ i : Fin 3, |x i - y i| ≤ ℓ := by
    intro i
    apply abs_le.mpr
    constructor <;> linarith only [(hx i).1, (hx i).2, (hy i).1, (hy i).2]
  have hsq : dist x y ^ 2 ≤ 3 * ℓ ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      ∑ i : Fin 3, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin 3, ℓ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [Real.dist_eq]
        exact pow_le_pow_left₀ (abs_nonneg _) (hc i) 2
      _ = 3 * ℓ ^ 2 := by simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hp := Real.sqrt_nonneg (3 : ℝ)
  apply (sq_le_sq₀ dist_nonneg (mul_nonneg hp hℓ)).mp
  calc
    dist x y ^ 2 ≤ 3 * ℓ ^ 2 := hsq
    _ = (Real.sqrt 3 * ℓ) ^ 2 := by rw [mul_pow, hs]

/-- The inscribed open ball lies inside its own half-open lattice cell. -/
theorem ball_latticeCenter_subset_cell (ℓ : ℝ) (z : LatticeIndex) :
    ball (latticeCenter ℓ z) (ℓ / 2) ⊆ latticeCell ℓ z := by
  intro x hx i
  have hcoord := PiLp.norm_apply_le (x - latticeCenter ℓ z) i
  have habs : |x i - ℓ * ((z i : ℝ) + 1 / 2)| < ℓ / 2 := by
    change |(x - latticeCenter ℓ z) i| < ℓ / 2
    rw [← Real.norm_eq_abs]
    exact hcoord.trans_lt (by simpa only [mem_ball, dist_eq_norm] using hx)
  rcases abs_lt.mp habs with ⟨hlo, hhi⟩
  constructor <;> linarith only [hlo, hhi]

end

end LiebThirring

end
