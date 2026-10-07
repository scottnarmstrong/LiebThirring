/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.DirichletOrbitals

/-! # Inner products of spatial Dirichlet cube orbitals -/

public section

open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace LiebThirring.TFUpper

private theorem inner_dirichletCubeModeL2_same_spin {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k m : Fin 3 → ℕ+) (s : Fin q) :
    inner ℂ (TFCubes.dirichletCubeModeL2 ℓ b (k, s))
      (TFCubes.dirichletCubeModeL2 ℓ b (m, s)) =
      (↑(∏ i : Fin 3, ∫ x in Ioo 0 ℓ.val,
        TFCubes.dirichletIntervalMode ℓ (k i) x *
          TFCubes.dirichletIntervalMode ℓ (m i) x) : ℂ) := by
  rw [L2.inner_def]
  rw [integral_congr_ae (by
    filter_upwards [TFCubes.dirichletCubeModeL2_ae ℓ b (k, s),
      TFCubes.dirichletCubeModeL2_ae ℓ b (m, s)] with x hk hm
    rw [hk, hm])]
  rw [← (TFCubes.measurePreserving_cubeFromCoordinates_restrict b ℓ).integral_comp
    (TFCubes.cubeCoordinateEquiv b).symm.measurableEmbedding]
  simp [TFCubes.dirichletCubeModeValue, EuclideanSpace.inner_single_left,
    TFCubes.dirichletCubeSpatialMode, TFCubes.cubeFromCoordinates,
    ← Finset.prod_mul_distrib, ← Complex.ofReal_mul]
  unfold TFCubes.cubeCoordinateMeasure
  rw [integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (μ := fun _ : Fin 3 => volume.restrict (Ioo 0 ℓ.val))
    (fun i x => ((TFCubes.dirichletIntervalMode ℓ (k i) x *
      TFCubes.dirichletIntervalMode ℓ (m i) x : ℝ) : ℂ))]
  simp only [integral_complex_ofReal]

private theorem inner_dirichletCubeModeL2_of_ne {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    {p r : TFCubes.DirichletCubeModeIndex q} (hpr : p ≠ r) :
    inner ℂ (TFCubes.dirichletCubeModeL2 ℓ b p)
      (TFCubes.dirichletCubeModeL2 ℓ b r) = 0 := by
  by_cases hs : p.2 = r.2
  · have hk : p.1 ≠ r.1 := fun h => hpr (Prod.ext h hs)
    obtain ⟨i, hi⟩ : ∃ i, p.1 i ≠ r.1 i := by
      simpa only [Function.ne_iff] using hk
    rw [show p = (p.1, p.2) from rfl,
      show r = (r.1, p.2) by ext <;> simp [hs.symm],
      inner_dirichletCubeModeL2_same_spin]
    rw [show (∏ j : Fin 3, ∫ x in Ioo 0 ℓ.val,
        TFCubes.dirichletIntervalMode ℓ (p.1 j) x *
          TFCubes.dirichletIntervalMode ℓ (r.1 j) x) = 0 by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le ℓ.property.le,
        TFCubes.integral_dirichletIntervalMode_mul_of_ne ℓ hi]]
    exact Complex.ofReal_zero
  · rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [TFCubes.dirichletCubeModeL2_ae ℓ b p,
      TFCubes.dirichletCubeModeL2_ae ℓ b r] with x hp hr
    rw [hp, hr]
    simp [TFCubes.dirichletCubeModeValue, EuclideanSpace.inner_single_left, hs]

/-- Same-cube spatial Dirichlet orbitals have Kronecker-delta inner product. -/
theorem inner_dirichletCubeSpatialL2 {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p r : TFCubes.DirichletCubeModeIndex q) :
    inner ℂ (dirichletCubeSpatialL2 ℓ b p) (dirichletCubeSpatialL2 ℓ b r) =
      if p = r then 1 else 0 := by
  change inner ℂ
      ((TFCubes.regionZeroExtendL2LI (𝕜 := ℂ) volume
        (TFCubes.measurableSet_cubeInterior b ℓ))
        (TFCubes.dirichletCubeModeL2 ℓ b p))
      ((TFCubes.regionZeroExtendL2LI (𝕜 := ℂ) volume
        (TFCubes.measurableSet_cubeInterior b ℓ))
        (TFCubes.dirichletCubeModeL2 ℓ b r)) = _
  rw [LinearIsometry.inner_map_map]
  by_cases hpr : p = r
  · subst r
    rw [inner_self_eq_norm_sq_to_K, TFCubes.norm_dirichletCubeModeL2]
    norm_num
  · rw [ite_eq_right hpr, inner_dirichletCubeModeL2_of_ne ℓ b hpr]

end LiebThirring.TFUpper

end
