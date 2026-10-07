/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.LatticeCounting

/-!
# Boundary layers of axis-aligned cubes

Coordinate-slab control for the cube case of a lattice construction.
-/

@[expose] public section

open Set MeasureTheory Metric

namespace LiebThirring

/-- The open axis-aligned cube `(0,A)^3` in physical space. -/
def openCoordinateCube (A : ℝ) : Set Position :=
  {x | ∀ i, 0 < x i ∧ x i < A}

def closedCoordinateCube (A : ℝ) : Set Position :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ A}

/-- The union of the six inner face slabs of thickness `h`. -/
def cubeInnerFaceSlabs (A h : ℝ) : Set Position :=
  {x | x ∈ openCoordinateCube A ∧ ∃ i, x i ≤ h ∨ A - h ≤ x i}

def cubeLowerFaceBox (A h : ℝ) (i : Fin 3) : Set Position :=
  {x | ∀ k, 0 < x k ∧ x k ≤ if k = i then h else A}

def cubeUpperFaceBox (A h : ℝ) (i : Fin 3) : Set Position :=
  {x | ∀ k, (if k = i then A - h else 0) ≤ x k ∧ x k ≤ A}

theorem cubeInnerFaceSlabs_subset_faceBoxes (A h : ℝ) :
    cubeInnerFaceSlabs A h ⊆
      (⋃ i : Fin 3, cubeLowerFaceBox A h i ∪ cubeUpperFaceBox A h i) := by
  rintro x ⟨hx, i, hi | hi⟩
  · refine mem_iUnion.mpr ⟨i, Or.inl ?_⟩
    intro k
    by_cases hki : k = i
    · subst k
      simpa using And.intro (hx i).1 hi
    · simp only [ite_eq_right hki]
      exact ⟨(hx k).1, (hx k).2.le⟩
  · refine mem_iUnion.mpr ⟨i, Or.inr ?_⟩
    intro k
    by_cases hki : k = i
    · subst k
      simpa using And.intro hi (hx i).2.le
    · simp only [ite_eq_right hki]
      exact ⟨(hx k).1.le, (hx k).2.le⟩

theorem volume_real_cubeLowerFaceBox {A h : ℝ} (hA : 0 ≤ A) (hh : 0 ≤ h)
    (i : Fin 3) :
    volume.real (cubeLowerFaceBox A h i) = h * A ^ 2 := by
  have hpre : cubeLowerFaceBox A h i = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹'
      (pi univ fun k ↦ Ioc 0 (if k = i then h else A)) := by
    ext x
    simp only [cubeLowerFaceBox, mem_ofPred_eq, mem_preimage, mem_pi, mem_univ, forall_const,
      mem_Ioc]
  rw [hpre, measureReal_def, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding,
    Real.volume_pi_Ioc_toReal]
  · simp only [sub_zero]
    fin_cases i <;> norm_num [Fin.prod_univ_succ] <;> ring
  · intro k
    dsimp
    split <;> assumption

theorem volume_real_cubeUpperFaceBox {A h : ℝ} (hA : 0 ≤ A) (hh : 0 ≤ h)
    (i : Fin 3) :
    volume.real (cubeUpperFaceBox A h i) = h * A ^ 2 := by
  have hpre : cubeUpperFaceBox A h i = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹'
      Icc (fun k ↦ if k = i then A - h else 0) (fun _ ↦ A) := by
    ext x
    simp only [cubeUpperFaceBox, mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def]
    constructor
    · intro hx
      exact ⟨fun k ↦ (hx k).1, fun k ↦ (hx k).2⟩
    · rintro ⟨hlo, hhi⟩ k
      exact ⟨hlo k, hhi k⟩
  rw [hpre, measureReal_def, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding,
    Real.volume_Icc_pi_toReal]
  · have hd : ∀ k : Fin 3, A - (if k = i then A - h else 0) = if k = i then h else A := by
      intro k
      split <;> linarith
    simp only [hd]
    fin_cases i <;> norm_num [Fin.prod_univ_succ] <;> ring
  · intro k
    dsimp
    split <;> linarith

theorem volume_real_openCoordinateCube {A : ℝ} (hA : 0 ≤ A) :
    volume.real (openCoordinateCube A) = A ^ 3 := by
  have hpre : openCoordinateCube A = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹'
      (pi univ fun _ ↦ Ioo 0 A) := by
    ext x
    simp only [openCoordinateCube, mem_ofPred_eq, mem_preimage, mem_pi, mem_univ,
      forall_const, mem_Ioo]
  rw [hpre, measureReal_def, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding,
    Real.volume_pi_Ioo_toReal]
  · norm_num [Fin.prod_univ_succ]
  · intro k
    exact hA

theorem isBounded_openCoordinateCube (A : ℝ) :
    Bornology.IsBounded (openCoordinateCube A) := by
  apply (Metric.isBounded_iff_subset_ball (0 : Position)).2
  refine ⟨Real.sqrt 3 * |A| + 1, ?_⟩
  intro x hx
  have hc : ∀ i : Fin 3, |x i| ≤ |A| := by
    intro i
    apply abs_le.mpr
    exact ⟨(le_trans (neg_nonpos.mpr (abs_nonneg A)) (hx i).1.le),
      (hx i).2.le.trans (le_abs_self A)⟩
  have hsq : ‖x‖ ^ 2 ≤ 3 * |A| ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      ∑ i : Fin 3, ‖x i‖ ^ 2 ≤ ∑ _i : Fin 3, |A| ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc i) 2
      _ = 3 * |A| ^ 2 := by norm_num [Fin.sum_univ_succ]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn : ‖x‖ ≤ Real.sqrt 3 * |A| := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))).mp
    calc
      ‖x‖ ^ 2 ≤ 3 * |A| ^ 2 := hsq
      _ = (Real.sqrt 3 * |A|) ^ 2 := by rw [mul_pow, hs]
  simpa only [mem_ball, dist_zero_right] using hn.trans_lt (lt_add_one _)

theorem volume_closedCoordinateCube_ne_top (A : ℝ) :
    volume (closedCoordinateCube A) ≠ ⊤ := by
  have hpre : closedCoordinateCube A = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹'
      Icc (fun _ ↦ 0) (fun _ ↦ A) := by
    ext x
    simp only [closedCoordinateCube, mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def]
    constructor
    · intro hx
      exact ⟨fun k ↦ (hx k).1, fun k ↦ (hx k).2⟩
    · rintro ⟨hlo, hhi⟩ k
      exact ⟨hlo k, hhi k⟩
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding, Real.volume_Icc_pi]
  exact ENNReal.prod_ne_top fun _ _ ↦ ENNReal.ofReal_ne_top

theorem volume_real_cubeInnerFaceSlabs_le {A h : ℝ} (hA : 0 ≤ A) (hh : 0 ≤ h) :
    volume.real (cubeInnerFaceSlabs A h) ≤ 6 * h * A ^ 2 := by
  by_cases hhA : h ≤ A
  · calc
      volume.real (cubeInnerFaceSlabs A h) ≤
          volume.real (⋃ i : Fin 3, cubeLowerFaceBox A h i ∪ cubeUpperFaceBox A h i) :=
        measureReal_mono (cubeInnerFaceSlabs_subset_faceBoxes A h)
          (measure_ne_top_of_subset (by
            rintro x hx k
            obtain ⟨i, hi⟩ := mem_iUnion.mp hx
            rcases hi with hi | hi
            · exact ⟨(hi k).1.le, (hi k).2.trans (by split <;> linarith)⟩
            · exact ⟨(by
                have hlo := (hi k).1
                split at hlo <;> linarith), (hi k).2⟩)
            (volume_closedCoordinateCube_ne_top A))
      _ ≤ ∑ i : Fin 3, volume.real (cubeLowerFaceBox A h i ∪ cubeUpperFaceBox A h i) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : Fin 3, (h * A ^ 2 + h * A ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [volume_real_cubeLowerFaceBox hA hh i,
          volume_real_cubeUpperFaceBox hA hh i] using
            (@measureReal_union_le _ _ volume (cubeLowerFaceBox A h i) (cubeUpperFaceBox A h i))
      _ = 6 * h * A ^ 2 := by norm_num [Fin.sum_univ_succ]; ring
  · have hAh : A ≤ h := le_of_not_ge hhA
    calc
      volume.real (cubeInnerFaceSlabs A h) ≤ volume.real (openCoordinateCube A) :=
        measureReal_mono (fun _ hx ↦ hx.1)
          (measure_ne_top_of_subset (t := openCoordinateCube A) (s := closedCoordinateCube A)
            (fun _ hx k ↦ ⟨(hx k).1.le, (hx k).2.le⟩)
            (volume_closedCoordinateCube_ne_top A))
      _ = A ^ 3 := volume_real_openCoordinateCube hA
      _ ≤ 6 * h * A ^ 2 := by nlinarith [sq_nonneg A]

theorem latticeBoundaryLayer_openCoordinateCube_subset_faceSlabs
    {A ℓ : ℝ} :
    latticeBoundaryLayer ℓ (openCoordinateCube A) ⊆
      cubeInnerFaceSlabs A (Real.sqrt 3 * ℓ) := by
  intro x hx
  rcases hx with ⟨hxCube, y, hyCube, hxy⟩
  have hy : ∃ i, y i ≤ 0 ∨ A ≤ y i := by
    simpa only [openCoordinateCube, mem_ofPred_eq, not_forall, not_and_or, not_lt] using hyCube
  obtain ⟨i, hi⟩ := hy
  have hcoord : |x i - y i| ≤ dist x y := by
    change |(x - y) i| ≤ dist x y
    rw [dist_eq_norm]
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (x - y) i
  refine ⟨hxCube, i, ?_⟩
  rcases hi with hi | hi
  · left
    have : x i - y i ≤ Real.sqrt 3 * ℓ :=
      (le_abs_self _).trans (hcoord.trans hxy)
    linarith
  · right
    have : y i - x i ≤ Real.sqrt 3 * ℓ :=
      (le_abs_self _).trans (by simpa only [abs_sub_comm] using hcoord.trans hxy)
    linarith

theorem volume_real_latticeBoundaryLayer_openCoordinateCube_le
    {A ℓ : ℝ} (hA : 0 ≤ A) (hℓ : 0 ≤ ℓ) :
    volume.real (latticeBoundaryLayer ℓ (openCoordinateCube A)) ≤
      6 * (Real.sqrt 3 * ℓ) * A ^ 2 := by
  refine (measureReal_mono latticeBoundaryLayer_openCoordinateCube_subset_faceSlabs ?_).trans
    (volume_real_cubeInnerFaceSlabs_le hA (mul_nonneg (Real.sqrt_nonneg 3) hℓ))
  exact measure_ne_top_of_subset (t := cubeInnerFaceSlabs A (Real.sqrt 3 * ℓ))
    (s := closedCoordinateCube A) (fun _ hx k ↦ ⟨(hx.1 k).1.le, (hx.1 k).2.le⟩)
    (volume_closedCoordinateCube_ne_top A)

theorem exists_cube_side_of_pos {sigma : ℝ} (hsigma : 0 < sigma) :
    ∃ A : ℝ, 0 < A ∧ A ^ 3 = sigma := by
  refine ⟨sigma ^ ((3 : ℝ)⁻¹), Real.rpow_pos_of_pos hsigma _, ?_⟩
  exact Real.rpow_inv_natCast_pow hsigma.le (by norm_num : (3 : ℕ) ≠ 0)

theorem volume_real_latticeBoundaryLayer_openCoordinateCube_le_normalized
    {A sigma ℓ : ℝ} (hA : 1 ≤ A) (hsigma : A ^ 3 = sigma) (hℓ : 0 ≤ ℓ) :
    volume.real (latticeBoundaryLayer ℓ (openCoordinateCube A)) ≤
      7 * Real.sqrt 3 * ℓ * sigma := by
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hsigma0 : 0 ≤ sigma := by rw [← hsigma]; positivity
  have hsq : A ^ 2 ≤ sigma := by
    rw [← hsigma]
    nlinarith [sq_nonneg A]
  calc
    volume.real (latticeBoundaryLayer ℓ (openCoordinateCube A)) ≤
        6 * (Real.sqrt 3 * ℓ) * A ^ 2 :=
      volume_real_latticeBoundaryLayer_openCoordinateCube_le hA0 hℓ
    _ ≤ 7 * Real.sqrt 3 * ℓ * sigma := by
      have hsqrt : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
      nlinarith [mul_nonneg hsqrt hℓ, mul_nonneg hℓ hsigma0]

theorem volume_real_latticeBoundaryLayer_openCoordinateCube_two_mul_le
    {A sigma r : ℝ} (hA : 1 ≤ A) (hsigma : A ^ 3 = sigma) (hr : 0 ≤ r) :
    volume.real (latticeBoundaryLayer (2 * r) (openCoordinateCube A)) ≤
      14 * Real.sqrt 3 * sigma * r := by
  have h := volume_real_latticeBoundaryLayer_openCoordinateCube_le_normalized
    (A := A) (sigma := sigma) (ℓ := 2 * r) hA hsigma (mul_nonneg (by norm_num) hr)
  calc
    volume.real (latticeBoundaryLayer (2 * r) (openCoordinateCube A)) ≤
        7 * Real.sqrt 3 * (2 * r) * sigma := h
    _ = 14 * Real.sqrt 3 * sigma * r := by ring

end LiebThirring

end
