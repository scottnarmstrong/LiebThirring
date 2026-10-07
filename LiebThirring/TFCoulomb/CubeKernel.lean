/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.LatticeGeometry
public import LiebThirring.Defs.Coulomb

/-! # The boxwise Coulomb kernel

Lieb–Simon (1977) III.12 (60b), pp. 66--67. The supremum uses closed cubes.
All pairs, including the diagonal, are retained.
-/

public section

open Set Metric
open scoped ENNReal

namespace LiebThirring.TFCoulomb

/-- Distances between two closed lattice cubes. -/
@[expose] def cubeDistances (ℓ : ℝ) (β γ : LatticeIndex) : Set ℝ :=
  {r | ∃ x ∈ latticeClosedCell ℓ β, ∃ y ∈ latticeClosedCell ℓ γ, r = dist x y}

/-- Maximum separation, literally the supremum in boxwise Coulomb comparison. -/
@[expose] noncomputable def cubeMaxDistance (ℓ : ℝ) (β γ : LatticeIndex) : ℝ :=
  sSup (cubeDistances ℓ β γ)

/-- Inverse maximum separation, including pairs in a single cube. -/
@[expose] noncomputable def cubeWeight (ℓ : ℝ) (β γ : LatticeIndex) : ℝ :=
  (cubeMaxDistance ℓ β γ)⁻¹

/-- Upper corner of a closed lattice cube. -/
@[expose] def latticeUpperCorner (ℓ : ℝ) (β : LatticeIndex) : Position :=
  WithLp.toLp 2 (fun i => ℓ * ((β i : ℝ) + 1))

theorem latticeUpperCorner_mem {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (β : LatticeIndex) :
    latticeUpperCorner ℓ β ∈ latticeClosedCell ℓ β := by
  intro i
  change ℓ * (β i : ℝ) ≤ ℓ * ((β i : ℝ) + 1) ∧ _ ≤ _
  exact ⟨mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hℓ, le_rfl⟩

theorem dist_latticeCorner_upperCorner {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (β : LatticeIndex) :
    dist (latticeCorner ℓ β) (latticeUpperCorner ℓ β) = Real.sqrt 3 * ℓ := by
  have hsq : dist (latticeCorner ℓ β) (latticeUpperCorner ℓ β) ^ 2 = 3 * ℓ ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    have hc (i : Fin 3) : dist (latticeCorner ℓ β i) (latticeUpperCorner ℓ β i) ^ 2 = ℓ ^ 2 := by
      rw [Real.dist_eq, sq_abs]
      change (ℓ * (β i : ℝ) - ℓ * ((β i : ℝ) + 1)) ^ 2 = ℓ ^ 2
      ring
    simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat]
  apply (sq_eq_sq₀ dist_nonneg (mul_nonneg (Real.sqrt_nonneg 3) hℓ)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  exact hsq

theorem cubeDistances_nonempty {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (β γ : LatticeIndex) :
    (cubeDistances ℓ β γ).Nonempty :=
  ⟨_, latticeCorner ℓ β, latticeCorner_mem_closedCell hℓ β,
    latticeCorner ℓ γ, latticeCorner_mem_closedCell hℓ γ, rfl⟩

theorem cubeDistances_bddAbove {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (β γ : LatticeIndex) :
    BddAbove (cubeDistances ℓ β γ) := by
  refine ⟨dist (latticeCorner ℓ β) (latticeCorner ℓ γ) + 2 * (Real.sqrt 3 * ℓ), ?_⟩
  rintro r ⟨x, hx, y, hy, rfl⟩
  have hx' := dist_le_lattice_diameter hℓ hx (latticeCorner_mem_closedCell hℓ β)
  have hy' := dist_le_lattice_diameter hℓ (latticeCorner_mem_closedCell hℓ γ) hy
  have ht := dist_triangle4 x (latticeCorner ℓ β) (latticeCorner ℓ γ) y
  linarith only [hx', hy', ht]

theorem dist_le_cubeMaxDistance {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {β γ : LatticeIndex}
    {x y : Position} (hx : x ∈ latticeClosedCell ℓ β) (hy : y ∈ latticeClosedCell ℓ γ) :
    dist x y ≤ cubeMaxDistance ℓ β γ :=
  le_csSup (cubeDistances_bddAbove hℓ β γ) ⟨x, hx, y, hy, rfl⟩

theorem cubeMaxDistance_le_dist_add {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {β γ : LatticeIndex}
    {x y : Position} (hx : x ∈ latticeClosedCell ℓ β) (hy : y ∈ latticeClosedCell ℓ γ) :
    cubeMaxDistance ℓ β γ ≤ dist x y + 2 * (Real.sqrt 3 * ℓ) := by
  apply csSup_le (cubeDistances_nonempty hℓ β γ)
  rintro r ⟨u, hu, v, hv, rfl⟩
  have hu' := dist_le_lattice_diameter hℓ hu hx
  have hv' := dist_le_lattice_diameter hℓ hy hv
  have ht := dist_triangle4 u x y v
  linarith only [hu', hv', ht]

theorem cubeMaxDistance_self {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (β : LatticeIndex) :
    cubeMaxDistance ℓ β β = Real.sqrt 3 * ℓ := by
  apply le_antisymm
  · apply csSup_le (cubeDistances_nonempty hℓ β β)
    rintro r ⟨x, hx, y, hy, rfl⟩
    exact dist_le_lattice_diameter hℓ hx hy
  · rw [← dist_latticeCorner_upperCorner hℓ β]
    exact dist_le_cubeMaxDistance hℓ (latticeCorner_mem_closedCell hℓ β)
      (latticeUpperCorner_mem hℓ β)

theorem cubeMaxDistance_pos {ℓ : ℝ} (hℓ : 0 < ℓ) (β γ : LatticeIndex) :
    0 < cubeMaxDistance ℓ β γ := by
  have ha := dist_le_cubeMaxDistance hℓ.le (latticeCorner_mem_closedCell hℓ.le β)
    (latticeCorner_mem_closedCell hℓ.le γ)
  have hb := dist_le_cubeMaxDistance hℓ.le (latticeCorner_mem_closedCell hℓ.le β)
    (latticeUpperCorner_mem hℓ.le γ)
  have ht := dist_triangle (latticeCorner ℓ γ) (latticeCorner ℓ β) (latticeUpperCorner ℓ γ)
  rw [dist_latticeCorner_upperCorner hℓ.le γ, dist_comm (latticeCorner ℓ γ)] at ht
  have hp := mul_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)) hℓ
  linarith only [ha, hb, ht, hp]

theorem cubeMaxDistance_comm (ℓ : ℝ) (β γ : LatticeIndex) :
    cubeMaxDistance ℓ β γ = cubeMaxDistance ℓ γ β := by
  unfold cubeMaxDistance
  congr 1
  ext r
  constructor <;> rintro ⟨x, hx, y, hy, hr⟩
  · exact ⟨y, hy, x, hx, hr.trans (dist_comm x y)⟩
  · exact ⟨y, hy, x, hx, hr.trans (dist_comm x y)⟩

theorem cubeWeight_pos {ℓ : ℝ} (hℓ : 0 < ℓ) (β γ : LatticeIndex) :
    0 < cubeWeight ℓ β γ := inv_pos.mpr (cubeMaxDistance_pos hℓ β γ)

theorem cubeWeight_self {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (β : LatticeIndex) :
    cubeWeight ℓ β β = 1 / (Real.sqrt 3 * ℓ) := by
  rw [cubeWeight, cubeMaxDistance_self hℓ, one_div]

theorem cubeWeight_comm (ℓ : ℝ) (β γ : LatticeIndex) :
    cubeWeight ℓ β γ = cubeWeight ℓ γ β := by
  rw [cubeWeight, cubeWeight, cubeMaxDistance_comm]

/-- The extended kernel comparison is valid also at a collision. -/
theorem ofReal_cubeWeight_le_coulombKernel {ℓ : ℝ} (hℓ : 0 < ℓ)
    {β γ : LatticeIndex} {x y : Position}
    (hx : x ∈ latticeClosedCell ℓ β) (hy : y ∈ latticeClosedCell ℓ γ) :
    ENNReal.ofReal (cubeWeight ℓ β γ) ≤ coulombKernel x y := by
  rw [cubeWeight, ENNReal.ofReal_inv_of_pos (cubeMaxDistance_pos hℓ β γ)]
  apply ENNReal.inv_le_inv.mpr
  exact ENNReal.ofReal_le_ofReal (by
    simpa only [dist_eq_norm] using dist_le_cubeMaxDistance hℓ.le hx hy)

/-- Far-field inverse-distance error. -/
theorem inv_dist_sub_cubeWeight_le {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s)
    {β γ : LatticeIndex} {x y : Position}
    (hx : x ∈ latticeClosedCell ℓ β) (hy : y ∈ latticeClosedCell ℓ γ)
    (hfar : s ≤ dist x y) :
    0 ≤ (dist x y)⁻¹ - cubeWeight ℓ β γ ∧
      (dist x y)⁻¹ - cubeWeight ℓ β γ ≤ 2 * Real.sqrt 3 * ℓ / s ^ 2 := by
  have hd : 0 < dist x y := hs.trans_le hfar
  have hm := cubeMaxDistance_pos hℓ β γ
  have hdm := dist_le_cubeMaxDistance hℓ.le hx hy
  have hmd := cubeMaxDistance_le_dist_add hℓ.le hx hy
  constructor
  · simpa only [cubeWeight, one_div] using
      sub_nonneg.mpr (one_div_le_one_div_of_le hd hdm)
  · unfold cubeWeight
    have hprod : s ^ 2 ≤ dist x y * cubeMaxDistance ℓ β γ := by
      calc
        s ^ 2 = s * s := pow_two s
        _ ≤ dist x y * cubeMaxDistance ℓ β γ :=
          mul_le_mul hfar (hfar.trans hdm) hs.le hd.le
    have heq : (dist x y)⁻¹ - (cubeMaxDistance ℓ β γ)⁻¹ =
        (cubeMaxDistance ℓ β γ - dist x y) / (dist x y * cubeMaxDistance ℓ β γ) := by
      field_simp
    rw [heq]
    exact div_le_div₀ (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 3)) hℓ.le)
      (by linarith only [hmd]) (sq_pos_of_pos hs) hprod

end LiebThirring.TFCoulomb

end
