/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeModes

/-! # Translated cube coordinates with the physical product measure

Subtracting the corner and taking Euclidean coordinates transports restricted
physical volume exactly to the product of the three interval measures.
-/

@[expose] public section

open MeasureTheory Set

namespace LiebThirring.TFCubes

/-- Literal coordinates relative to the cube corner. -/
def cubeCoordinates (b : Position) (x : Position) : Fin 3 → ℝ :=
  fun i => x i - b i

/-- The inverse translated Euclidean coordinate map. -/
def cubeFromCoordinates (b : Position) (x : Fin 3 → ℝ) : Position :=
  WithLp.toLp 2 x + b

theorem cubeFromCoordinates_cubeCoordinates (b x : Position) :
    cubeFromCoordinates b (cubeCoordinates b x) = x := by
  apply PiLp.ext
  intro i
  change (x i - b i) + b i = x i
  exact sub_add_cancel _ _

theorem cubeCoordinates_cubeFromCoordinates (b : Position) (x : Fin 3 → ℝ) :
    cubeCoordinates b (cubeFromCoordinates b x) = x := by
  funext i
  change (x i + b i) - b i = x i
  exact add_sub_cancel_right _ _

/-- Coordinate translation as a genuine measurable equivalence. -/
def cubeCoordinateEquiv (b : Position) : Position ≃ᵐ (Fin 3 → ℝ) where
  toFun := cubeCoordinates b
  invFun := cubeFromCoordinates b
  left_inv := cubeFromCoordinates_cubeCoordinates b
  right_inv := cubeCoordinates_cubeFromCoordinates b
  measurable_toFun := by
    exact ((PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).comp
      (continuous_id.sub continuous_const)).measurable
  measurable_invFun := by
    exact ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).add
      continuous_const).measurable

/-- Three copies of physical Lebesgue interval measure. -/
noncomputable def cubeCoordinateMeasure (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    Measure (Fin 3 → ℝ) :=
  Measure.pi fun _ => volume.restrict (Ioo 0 ℓ.val)

attribute [reducible] cubeCoordinateMeasure

theorem cubeCoordinates_preimage_intervalCube (b : Position)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    cubeCoordinates b ⁻¹' (univ.pi fun _ : Fin 3 => Ioo 0 ℓ.val) =
      cubeInterior b ℓ := by
  ext x
  simp only [mem_preimage, mem_pi, mem_univ, forall_const, mem_Ioo,
    cubeCoordinates, cubeInterior, mem_ofPred_eq]
  constructor
  · intro h i
    constructor <;> linarith [(h i).1, (h i).2]
  · intro h i
    constructor <;> linarith [(h i).1, (h i).2]

/-- Translation and Euclidean coordinates preserve ambient physical volume. -/
theorem measurePreserving_cubeCoordinates (b : Position) :
    MeasurePreserving (cubeCoordinates b) volume volume := by
  exact (PiLp.volume_preserving_ofLp (Fin 3)).comp
    (measurePreserving_sub_right volume b)

/-- Restricted cube volume is exactly the product of physical interval measures. -/
theorem measurePreserving_cubeCoordinates_restrict (b : Position)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    MeasurePreserving (cubeCoordinates b) (volume.restrict (cubeInterior b ℓ))
      (cubeCoordinateMeasure ℓ) := by
  refine ⟨(cubeCoordinateEquiv b).measurable, ?_⟩
  rw [← cubeCoordinates_preimage_intervalCube]
  rw [← Measure.restrict_map (measurePreserving_cubeCoordinates b).measurable
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)]
  rw [(measurePreserving_cubeCoordinates b).map_eq]
  exact Measure.restrict_pi_pi _ _

/-- The inverse coordinate map preserves the same restricted measures. -/
theorem measurePreserving_cubeFromCoordinates_restrict (b : Position)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    MeasurePreserving (cubeFromCoordinates b) (cubeCoordinateMeasure ℓ)
      (volume.restrict (cubeInterior b ℓ)) := by
  exact (measurePreserving_cubeCoordinates_restrict b ℓ).symm (cubeCoordinateEquiv b)

noncomputable instance cubeCoordinateMeasure.instIsFiniteMeasure
    (ℓ : {ℓ : ℝ // 0 < ℓ}) : IsFiniteMeasure (cubeCoordinateMeasure ℓ) := by
  unfold cubeCoordinateMeasure
  infer_instance

noncomputable instance cubeInterior.instIsFiniteMeasure (b : Position)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) : IsFiniteMeasure (volume.restrict (cubeInterior b ℓ)) := by
  have hmap := (measurePreserving_cubeFromCoordinates_restrict b ℓ).map_eq
  rw [← hmap]
  exact Measure.isFiniteMeasure_map _ _

/-- Pullback by the physical coordinate map as a complex linear isometry. -/
noncomputable def cubeCoordinateL2LI {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (b : Position) (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    Lp F 2 (cubeCoordinateMeasure ℓ) →ₗᵢ[ℂ]
      RegionState Position F (cubeInterior b ℓ) :=
  Lp.compMeasurePreservingₗᵢ ℂ _ (measurePreserving_cubeCoordinates_restrict b ℓ)

/-- The pullback uses the literal translated coordinate representative. -/
theorem cubeCoordinateL2LI_ae {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (b : Position) (ℓ : {ℓ : ℝ // 0 < ℓ}) (u : Lp F 2 (cubeCoordinateMeasure ℓ)) :
    cubeCoordinateL2LI b ℓ u =ᵐ[volume.restrict (cubeInterior b ℓ)]
      fun x => u (cubeCoordinates b x) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_cubeCoordinates_restrict b ℓ)

/-- The physical product-coordinate pullback is onto the whole local L² carrier. -/
noncomputable def cubeCoordinateL2Equiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (b : Position) (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    Lp F 2 (cubeCoordinateMeasure ℓ) ≃ₗᵢ[ℂ]
      RegionState Position F (cubeInterior b ℓ) where
  toFun := cubeCoordinateL2LI b ℓ
  invFun := Lp.compMeasurePreserving (cubeFromCoordinates b)
    (measurePreserving_cubeFromCoordinates_restrict b ℓ)
  left_inv u := by
    change Lp.compMeasurePreserving (cubeFromCoordinates b) _
      (Lp.compMeasurePreserving (cubeCoordinates b) _ u) = u
    rw [← Lp.compMeasurePreserving_comp_apply]
    have heq : cubeCoordinates b ∘ cubeFromCoordinates b = id :=
      funext (cubeCoordinates_cubeFromCoordinates b)
    simpa only [heq] using (Lp.compMeasurePreserving_id_apply u)
  right_inv u := by
    change Lp.compMeasurePreserving (cubeCoordinates b) _
      (Lp.compMeasurePreserving (cubeFromCoordinates b) _ u) = u
    rw [← Lp.compMeasurePreserving_comp_apply]
    have heq : cubeFromCoordinates b ∘ cubeCoordinates b = id :=
      funext (cubeFromCoordinates_cubeCoordinates b)
    simpa only [heq] using (Lp.compMeasurePreserving_id_apply u)
  map_add' := (cubeCoordinateL2LI b ℓ).map_add
  map_smul' := (cubeCoordinateL2LI b ℓ).map_smul
  norm_map' := (cubeCoordinateL2LI b ℓ).norm_map

end LiebThirring.TFCubes

end
