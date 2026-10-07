/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.LatticeCounting
import Mathlib.Tactic

/-!
# Lattice cubes eligible by their interiors

The source counts cubes whose interiors lie in the region. This module retains
that exact eligibility convention for lattice boundary estimates. The closed-cell selections used
in the Swiss-cheese construction are a subfamily and give the same boundary
loss bound.
-/

public section

open Set MeasureTheory Metric

namespace LiebThirring

/-- The open interior of a lattice cube. -/
@[expose] def latticeOpenCell (ℓ : ℝ) (z : LatticeIndex) : Set Position :=
  {x | ∀ i, ℓ * (z i : ℝ) < x i ∧ x i < ℓ * ((z i : ℝ) + 1)}

theorem latticeOpenCell_subset_cell (ℓ : ℝ) (z : LatticeIndex) :
    latticeOpenCell ℓ z ⊆ latticeCell ℓ z := by
  intro x hx i
  exact ⟨(hx i).1.le, (hx i).2⟩

theorem latticeCenter_mem_openCell {ℓ : ℝ} (hℓ : 0 < ℓ) (z : LatticeIndex) :
    latticeCenter ℓ z ∈ latticeOpenCell ℓ z := by
  intro i
  change ℓ * (z i : ℝ) < ℓ * ((z i : ℝ) + 1 / 2) ∧
    ℓ * ((z i : ℝ) + 1 / 2) < ℓ * ((z i : ℝ) + 1)
  constructor <;> nlinarith only [hℓ]

theorem measurableSet_latticeOpenCell (ℓ : ℝ) (z : LatticeIndex) :
    MeasurableSet (latticeOpenCell ℓ z) := by
  have heq : latticeOpenCell ℓ z = ⋂ i,
      {x : Position | ℓ * (z i : ℝ) < x i ∧ x i < ℓ * ((z i : ℝ) + 1)} := by
    ext x
    simp only [latticeOpenCell, mem_iInter, mem_ofPred_eq]
  rw [heq]
  exact MeasurableSet.iInter fun _i =>
    measurableSet_Ioo.preimage (by fun_prop)

theorem volume_latticeOpenCell {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (z : LatticeIndex) :
    volume (latticeOpenCell ℓ z) = ENNReal.ofReal (ℓ ^ 3) := by
  have hpre : latticeOpenCell ℓ z = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹'
      (pi univ fun i => Ioo (ℓ * (z i : ℝ)) (ℓ * ((z i : ℝ) + 1))) := by
    ext x
    simp only [latticeOpenCell, mem_ofPred_eq, mem_preimage, mem_pi, mem_univ,
      forall_const, mem_Ioo]
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding, Real.volume_pi_Ioo]
  have hs : ∀ i : Fin 3, ℓ * ((z i : ℝ) + 1) - ℓ * (z i : ℝ) = ℓ := by
    intro i
    ring
  simp only [hs, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow hℓ 3).symm

theorem interiorLatticeLabels_finite {ℓ : ℝ} (hℓ : 0 < ℓ) {Ω : Set Position}
    (hΩ : Bornology.IsBounded Ω) : {z : LatticeIndex | latticeOpenCell ℓ z ⊆ Ω}.Finite := by
  obtain ⟨A, hA⟩ := hΩ.subset_ball (0 : Position)
  refine (Set.Finite.pi (fun _i : Fin 3 =>
    finite_Icc ⌊-A / ℓ - 1⌋ ⌈A / ℓ + 1⌉)).subset ?_
  intro z hz
  have hc := hA (hz (latticeCenter_mem_openCell hℓ z))
  have hn : ‖latticeCenter ℓ z‖ < A := by
    simpa only [mem_ball, dist_zero_right] using hc
  intro i _
  have hi : |ℓ * ((z i : ℝ) + 1 / 2)| ≤ ‖latticeCenter ℓ z‖ := by
    simpa only [latticeCenter, Real.norm_eq_abs] using PiLp.norm_apply_le (latticeCenter ℓ z) i
  have hb := abs_le.mp (hi.trans hn.le)
  have hlo : -A / ℓ ≤ (z i : ℝ) + 1 / 2 :=
    (div_le_iff₀ hℓ).mpr (by simpa only [mul_comm] using hb.1)
  have hhi : (z i : ℝ) + 1 / 2 ≤ A / ℓ :=
    (le_div_iff₀ hℓ).mpr (by simpa only [mul_comm] using hb.2)
  constructor
  · have hlow : -A / ℓ - 1 ≤ (z i : ℝ) := by linarith only [hlo]
    simpa only [Int.floor_intCast] using Int.floor_mono hlow
  · have hhigh : (z i : ℝ) ≤ A / ℓ + 1 := by linarith only [hhi]
    simpa only [Int.ceil_intCast] using Int.ceil_mono hhigh

/-- All lattice cubes whose open interiors lie in the region, as in LL Lemma 3.1. -/
@[expose] noncomputable def interiorLatticeCubes (ℓ : ℝ) (Ω : Set Position)
    (hℓ : 0 < ℓ) (hΩ : Bornology.IsBounded Ω) : Finset LatticeIndex :=
  (interiorLatticeLabels_finite hℓ hΩ).toFinset

theorem mem_interiorLatticeCubes {ℓ : ℝ} {Ω : Set Position}
    {hℓ : 0 < ℓ} {hΩ : Bornology.IsBounded Ω} {z : LatticeIndex} :
    z ∈ interiorLatticeCubes ℓ Ω hℓ hΩ ↔ latticeOpenCell ℓ z ⊆ Ω :=
  Set.Finite.mem_toFinset _

theorem eligibleLatticeCubes_subset_interiorLatticeCubes {ℓ : ℝ} {Ω : Set Position}
    (hℓ : 0 < ℓ) (hΩ : Bornology.IsBounded Ω) :
    eligibleLatticeCubes ℓ Ω hℓ hΩ ⊆ interiorLatticeCubes ℓ Ω hℓ hΩ := by
  intro z hz
  exact mem_interiorLatticeCubes.mpr ((latticeOpenCell_subset_cell ℓ z).trans
    ((latticeCell_subset_closedCell ℓ z).trans (mem_eligibleLatticeCubes.mp hz)))

theorem interior_lattice_volume_deficit_nonneg {ℓ : ℝ} {Ω : Set Position}
    (hℓ : 0 < ℓ) (hΩ : Bornology.IsBounded Ω) :
    0 ≤ volume.real Ω - ((interiorLatticeCubes ℓ Ω hℓ hΩ).card : ℝ) * ℓ ^ 3 := by
  let s := interiorLatticeCubes ℓ Ω hℓ hΩ
  have hd : (s : Set LatticeIndex).PairwiseDisjoint (latticeOpenCell ℓ) := by
    intro i _ j _ hij
    exact (latticeCell_disjoint hℓ hij).mono
      (latticeOpenCell_subset_cell ℓ i) (latticeOpenCell_subset_cell ℓ j)
  have ht : ∀ i ∈ s, volume (latticeOpenCell ℓ i) ≠ ⊤ := by
    intro i _
    rw [volume_latticeOpenCell hℓ.le]
    exact ENNReal.ofReal_ne_top
  have hvol : volume.real (⋃ i ∈ s, latticeOpenCell ℓ i) = (s.card : ℝ) * ℓ ^ 3 := by
    rw [measureReal_biUnion_finset hd (fun i _ => measurableSet_latticeOpenCell ℓ i) ht]
    simp only [measureReal_def, volume_latticeOpenCell hℓ.le,
      ENNReal.toReal_ofReal (pow_nonneg hℓ.le _), Finset.sum_const, nsmul_eq_mul]
  apply sub_nonneg.mpr
  rw [← hvol]
  apply measureReal_mono _ hΩ.measure_lt_top.ne
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
  exact mem_interiorLatticeCubes.mp hi hxi

theorem interior_lattice_volume_deficit_le_boundaryLayer {ℓ : ℝ} {Ω : Set Position}
    (hℓ : 0 < ℓ) (hΩ : Bornology.IsBounded Ω) :
    volume.real Ω - ((interiorLatticeCubes ℓ Ω hℓ hΩ).card : ℝ) * ℓ ^ 3 ≤
      volume.real (latticeBoundaryLayer ℓ Ω) := by
  have hcard := Finset.card_le_card (eligibleLatticeCubes_subset_interiorLatticeCubes hℓ hΩ)
  have hreal : ((eligibleLatticeCubes ℓ Ω hℓ hΩ).card : ℝ) ≤
      (interiorLatticeCubes ℓ Ω hℓ hΩ).card := by exact_mod_cast hcard
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_right hreal (pow_nonneg hℓ.le _)) _).trans
    (lattice_volume_deficit_le_boundaryLayer hℓ hΩ)

/-- The inscribed open ball is inside the open cell, including tangent cube cases. -/
theorem ball_latticeCenter_subset_openCell (ℓ : ℝ) (z : LatticeIndex) :
    ball (latticeCenter ℓ z) (ℓ / 2) ⊆ latticeOpenCell ℓ z := by
  intro x hx i
  have hcoord := PiLp.norm_apply_le (x - latticeCenter ℓ z) i
  have habs : |x i - ℓ * ((z i : ℝ) + 1 / 2)| < ℓ / 2 := by
    change |(x - latticeCenter ℓ z) i| < ℓ / 2
    rw [← Real.norm_eq_abs]
    exact hcoord.trans_lt (by simpa only [mem_ball, dist_eq_norm] using hx)
  rcases abs_lt.mp habs with ⟨hlo, hhi⟩
  constructor <;> linarith only [hlo, hhi]

theorem interior_lattice_ball_subset {ℓ : ℝ} {Ω : Set Position}
    {hℓ : 0 < ℓ} {hΩ : Bornology.IsBounded Ω} {z : LatticeIndex}
    (hz : z ∈ interiorLatticeCubes ℓ Ω hℓ hΩ) :
    ball (latticeCenter ℓ z) (ℓ / 2) ⊆ Ω :=
  (ball_latticeCenter_subset_openCell ℓ z).trans (mem_interiorLatticeCubes.mp hz)

end LiebThirring

end
