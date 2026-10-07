/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeCoordinates
public import LiebThirring.TFCubes.CubeSpin
public import LiebThirring.TFCubes.LocalFormGraph

/-! # One-particle configuration and spin coordinate identifications

The physical one-particle configuration uses `Fin 1 × Fin 3`, and its
spin amplitudes use `Fin 1 → Fin q`. These are transported by actual linear
isometries to the cube's `Position` and `Fin q` carriers.
-/

@[expose] public section

open MeasureTheory Set

namespace LiebThirring.TFCubes

/-- The three one-particle spatial coordinates. -/
def cubeConfigurationIndexEquiv : Fin 3 ≃ Fin 1 × Fin 3 where
  toFun a := (0, a)
  invFun a := a.2
  left_inv _ := rfl
  right_inv a := by
    rcases a with ⟨i, a⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl

/-- The cube's spatial carrier and the one-particle carrier are isometric. -/
noncomputable def cubeConfigurationEquiv : Position ≃ₗᵢ[ℝ] Configuration 1 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ cubeConfigurationIndexEquiv

variable {X F G : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- Pointwise application of a spin isometry on the physical L² space. -/
noncomputable def cubeValueL2Equiv (μ : Measure X) (L : F ≃ₗᵢ[ℂ] G) :
    Lp F 2 μ ≃ₗᵢ[ℂ] Lp G 2 μ where
  toFun := L.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ
  invFun := L.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ
  left_inv u := by
    apply Lp.ext
    filter_upwards [L.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
      (L.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ u),
      L.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL u] with x hx hy
    rw [hx, hy]
    exact L.symm_apply_apply _
  right_inv u := by
    apply Lp.ext
    filter_upwards [L.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
      (L.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ u),
      L.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL u] with x hx hy
    rw [hx, hy]
    exact L.apply_symm_apply _
  map_add' := (L.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ).map_add
  map_smul' := (L.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ).map_smul
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_localL2, norm_sq_localL2]
    apply integral_congr_ae
    filter_upwards [L.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL u] with x hx
    change ‖L.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ u x‖ ^ 2 = ‖u x‖ ^ 2
    rw [hx]
    exact congrArg (fun r : ℝ => r ^ 2) (L.norm_map (u x))

/-- A measure-preserving equivalence gives an onto isometry of physical L² spaces. -/
noncomputable def cubeMeasureL2Equiv {Y : Type*} [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (ν : Measure Y) (hp : MeasurePreserving e μ ν) :
    Lp F 2 μ ≃ₗᵢ[ℂ] Lp F 2 ν where
  toFun := Lp.compMeasurePreserving e.symm (hp.symm e)
  invFun := Lp.compMeasurePreserving e hp
  left_inv u := by
    rw [← Lp.compMeasurePreserving_comp_apply]
    have heq : e.symm ∘ e = id := funext e.symm_apply_apply
    simpa only [heq] using Lp.compMeasurePreserving_id_apply u
  right_inv u := by
    rw [← Lp.compMeasurePreserving_comp_apply]
    have heq : e ∘ e.symm = id := funext e.apply_symm_apply
    simpa only [heq] using Lp.compMeasurePreserving_id_apply u
  map_add' := (Lp.compMeasurePreservingₗᵢ ℂ e.symm (hp.symm e)).map_add
  map_smul' := (Lp.compMeasurePreservingₗᵢ ℂ e.symm (hp.symm e)).map_smul
  norm_map' := (Lp.compMeasurePreservingₗᵢ ℂ e.symm (hp.symm e)).norm_map

end LiebThirring.TFCubes

end
