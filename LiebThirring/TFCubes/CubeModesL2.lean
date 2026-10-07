/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeCoordinates
public import LiebThirring.TFCubes.CubeSpin
public import LiebThirring.TFCubes.IntervalModeBounds
import Mathlib.Tactic

/-! # Translated cube modes in the local spin-valued L2 space -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace LiebThirring.TFCubes

theorem continuous_dirichletCubeModeValue {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Position) (p : DirichletCubeModeIndex q) :
    Continuous (dirichletCubeModeValue ℓ b p) := by
  rw [show dirichletCubeModeValue ℓ b p = fun x => WithLp.toLp 2
      (fun s => if s = p.2 then dirichletCubeSpatialMode ℓ b p.1 x else 0) by
    funext x
    apply PiLp.ext
    intro s
    simp [dirichletCubeModeValue]]
  apply (PiLp.continuous_toLp 2 (fun _ : Fin q => ℂ)).comp
  apply continuous_pi
  intro s
  by_cases hs : s = p.2
  · simp only [hs, ↓reduceIte]
    unfold dirichletCubeSpatialMode
    apply continuous_finsetProd Finset.univ
    intro i _
    exact Complex.continuous_ofReal.comp
      ((continuous_dirichletIntervalMode ℓ (p.1 i)).comp (by fun_prop))
  · simp only [ite_eq_right hs]
    fun_prop

theorem norm_dirichletCubeModeValue_le {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Position) (p : DirichletCubeModeIndex q) (x : Position) :
    ‖dirichletCubeModeValue ℓ b p x‖ ≤
      ∏ _i : Fin 3, Real.sqrt (2 / ℓ.val) := by
  rw [dirichletCubeModeValue, PiLp.norm_single, dirichletCubeSpatialMode, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ =>
    abs_dirichletIntervalMode_le ℓ (p.1 i) (x i - b i)

theorem dirichletCubeModeValue_memLp {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Position) (p : DirichletCubeModeIndex q) :
    MemLp (dirichletCubeModeValue ℓ b p) 2
      (volume.restrict (cubeInterior b ℓ)) :=
  MemLp.of_bound (continuous_dirichletCubeModeValue ℓ b p).aestronglyMeasurable _
    (Filter.Eventually.of_forall (norm_dirichletCubeModeValue_le ℓ b p))

/-- The normalized Dirichlet cube mode in local spin-valued L2. -/
noncomputable def dirichletCubeModeL2 {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Position) (p : DirichletCubeModeIndex q) : CubeState q b ℓ :=
  (dirichletCubeModeValue_memLp ℓ b p).toLp (dirichletCubeModeValue ℓ b p)

theorem dirichletCubeModeL2_ae {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Position) (p : DirichletCubeModeIndex q) :
    dirichletCubeModeL2 ℓ b p =ᵐ[volume.restrict (cubeInterior b ℓ)]
      dirichletCubeModeValue ℓ b p :=
  (dirichletCubeModeValue_memLp ℓ b p).coeFn_toLp

private theorem integral_Ioo_dirichletIntervalMode_sq
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) :
    ∫ x in Ioo 0 ℓ.val, dirichletIntervalMode ℓ n x ^ 2 = 1 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le ℓ.property.le,
    integral_dirichletIntervalMode_sq]

theorem integral_norm_sq_dirichletCubeModeValue {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (p : DirichletCubeModeIndex q) :
    ∫ x, ‖dirichletCubeModeValue ℓ b p x‖ ^ 2
      ∂(volume.restrict (cubeInterior b ℓ)) = 1 := by
  rw [← (measurePreserving_cubeFromCoordinates_restrict b ℓ).integral_comp
    (cubeCoordinateEquiv b).symm.measurableEmbedding]
  simp only [cubeFromCoordinates, dirichletCubeModeValue,
    PiLp.norm_single, dirichletCubeSpatialMode, PiLp.add_apply,
    add_sub_cancel_right, norm_prod, Complex.norm_real, Real.norm_eq_abs,
    ← Finset.prod_pow, sq_abs]
  change (∫ x : Fin 3 → ℝ, ∏ i : Fin 3,
      dirichletIntervalMode ℓ (p.1 i) (x i) ^ 2 ∂cubeCoordinateMeasure ℓ) = 1
  unfold cubeCoordinateMeasure
  rw [integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (μ := fun _ : Fin 3 => volume.restrict (Ioo 0 ℓ.val))
    (fun i x => dirichletIntervalMode ℓ (p.1 i) x ^ 2)]
  simp only [integral_Ioo_dirichletIntervalMode_sq, Finset.prod_const,
    one_pow]

theorem norm_dirichletCubeModeL2 {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Position) (p : DirichletCubeModeIndex q) :
    ‖dirichletCubeModeL2 ℓ b p‖ = 1 := by
  have hs : ‖dirichletCubeModeL2 ℓ b p‖ ^ 2 = 1 ^ 2 := by
    calc
      _ = ∫ x, ‖dirichletCubeModeL2 ℓ b p x‖ ^ 2
          ∂(volume.restrict (cubeInterior b ℓ)) :=
        norm_sq_localL2 _ (dirichletCubeModeL2 ℓ b p)
      _ = ∫ x, ‖dirichletCubeModeValue ℓ b p x‖ ^ 2
          ∂(volume.restrict (cubeInterior b ℓ)) :=
        integral_congr_ae ((dirichletCubeModeL2_ae ℓ b p).fun_comp fun z => ‖z‖ ^ 2)
      _ = 1 := integral_norm_sq_dirichletCubeModeValue ℓ b p
      _ = 1 ^ 2 := by norm_num
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hs

end LiebThirring.TFCubes

end
