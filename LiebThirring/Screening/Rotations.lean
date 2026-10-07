/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Screening.Radialization
import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Probability averaging over spatial rotations

Concrete `SO(3)`, its normalized Haar probability, and averaging of finite
spatial charge measures. The compactness proof bounds every matrix entry by
one. The equal-radius transitivity proof composes two hyperplane reflections.
This supplies the rotation layer used by the radial screening.
-/

public section

open MeasureTheory Set Submodule Module

namespace LiebThirring

/-- The orientation-preserving orthogonal matrices acting on physical space. -/
abbrev SpatialRotation := Matrix.specialOrthogonalGroup (Fin 3) ℝ

instance instContinuousInvSpatialRotation : ContinuousInv SpatialRotation where
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.star

instance instIsTopologicalGroupSpatialRotation : IsTopologicalGroup SpatialRotation where

/-- `SO(3)` is a closed bounded set of matrices, hence compact. -/
theorem isCompact_spatialRotations :
    IsCompact (Matrix.specialOrthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  have hclosed : IsClosed (Matrix.specialOrthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
    change IsClosed ((unitary (Matrix (Fin 3) (Fin 3) ℝ) : Set (Matrix (Fin 3) (Fin 3) ℝ)) ∩
      {A : Matrix (Fin 3) (Fin 3) ℝ | A.det = 1})
    exact isClosed_unitary.inter (isClosed_eq continuous_id.matrix_det continuous_const)
  refine ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).matrix).of_isClosed_subset hclosed ?_
  intro A hA
  rw [Set.mem_matrix]
  intro i j
  have h := entry_norm_bound_of_unitary hA.1 i j
  simpa only [Real.norm_eq_abs, abs_le, Set.mem_Icc] using h

instance instCompactSpaceSpatialRotation : CompactSpace SpatialRotation :=
  isCompact_iff_compactSpace.mp isCompact_spatialRotations

instance instMeasurableSpaceSpatialRotation : MeasurableSpace SpatialRotation :=
  borel SpatialRotation

instance instBorelSpaceSpatialRotation : BorelSpace SpatialRotation := ⟨rfl⟩

/-- Haar measure normalized on the whole compact rotation group. -/
@[expose] noncomputable def spatialRotationMeasure : Measure SpatialRotation :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts SpatialRotation)

instance instIsProbabilityMeasureSpatialRotationMeasure :
    IsProbabilityMeasure spatialRotationMeasure := by
  constructor
  exact Measure.haarMeasure_self

instance instIsMulLeftInvariantSpatialRotationMeasure :
    spatialRotationMeasure.IsMulLeftInvariant := by
  unfold spatialRotationMeasure
  infer_instance

/-- A concrete rotation matrix as a linear isometry of physical space. -/
@[expose] noncomputable def spatialRotationIsometry (Q : SpatialRotation) :
    Position ≃ₗᵢ[ℝ] Position :=
  Unitary.linearIsometryEquiv
    ⟨Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) Q.val,
      Unitary.map_mem (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)) Q.property.1⟩

@[simp] theorem spatialRotationIsometry_apply (Q : SpatialRotation) (x : Position) :
    spatialRotationIsometry Q x = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) Q.val x := rfl

/-- Determinant is unchanged by the matrix-to-Euclidean-operator correspondence. -/
theorem det_toEuclideanCLM (A : Matrix (Fin 3) (Fin 3) ℝ) :
    LinearMap.det (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A).toLinearMap = A.det := by
  change LinearMap.det (Matrix.toEuclideanLin A) = A.det
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]

/-- Matrix rotations represent every orientation-preserving spatial linear isometry. -/
theorem exists_spatialRotation_isometry (Q : Position ≃ₗᵢ[ℝ] Position)
    (hQ : Q.toLinearEquiv.det = 1) :
    ∃ R : SpatialRotation, spatialRotationIsometry R = Q := by
  let u := Unitary.linearIsometryEquiv.symm Q
  let A := (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)).symm (u.val)
  have hu : A ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
    Unitary.map_mem (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)).symm u.property
  have hA : Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A = (Q : Position →L[ℝ] Position) := by
    exact (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)).apply_symm_apply u.val
  have hdet : A.det = 1 := by
    rw [← det_toEuclideanCLM, hA]
    have he : (Q : Position →L[ℝ] Position).toLinearMap = Q.toLinearEquiv.toLinearMap := by
      ext x
      rfl
    rw [he]
    simpa only [LinearEquiv.coe_det, Units.val_one] using congrArg Units.val hQ
  refine ⟨⟨A, hu, hdet⟩, ?_⟩
  apply LinearIsometryEquiv.ext
  intro x
  rw [spatialRotationIsometry_apply]
  exact congrArg (fun f : Position →L[ℝ] Position => f x) hA

/-- Rotation about a chosen spatial centre. -/
@[expose] noncomputable def rotateAbout (Q : SpatialRotation) (c x : Position) : Position :=
  c + spatialRotationIsometry Q (x - c)

theorem continuous_rotateAbout (c : Position) :
    Continuous (fun p : SpatialRotation × Position => rotateAbout p.1 c p.2) := by
  unfold rotateAbout
  simp only [spatialRotationIsometry_apply]
  have hpair : Continuous (fun p : SpatialRotation × Position =>
      (p.1.val, p.2 - c)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_snd.sub continuous_const)
  have hmatrix : Continuous (fun p : Matrix (Fin 3) (Fin 3) ℝ × Position =>
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) p.1 p.2) :=
    Matrix.continuous_uncurry_toEuclideanCLM
  apply Continuous.add
  · exact continuous_const
  · simpa only [Function.comp_def] using hmatrix.comp hpair

theorem rotateAbout_mul (Q R : SpatialRotation) (c x : Position) :
    rotateAbout Q c (rotateAbout R c x) = rotateAbout (Q * R) c x := by
  simp only [rotateAbout, add_sub_cancel_left, spatialRotationIsometry_apply]
  rw [show (Q * R).val = Q.val * R.val from rfl, map_mul]
  rfl

/-- The pushforward of independent Haar rotation and spatial charge. -/
@[expose] noncomputable def rotationAveragedMeasure (c : Position) (μ : Measure Position) :
    Measure Position :=
  (spatialRotationMeasure.prod μ).map (fun p => rotateAbout p.1 c p.2)

instance instIsFiniteMeasureRotationAveragedMeasure (c : Position) (μ : Measure Position)
    [IsFiniteMeasure μ] : IsFiniteMeasure (rotationAveragedMeasure c μ) := by
  unfold rotationAveragedMeasure
  infer_instance

/-- Haar averaging preserves the total charge mass. -/
theorem rotationAveragedMeasure_mass (c : Position) (μ : Measure Position)
    [IsFiniteMeasure μ] : rotationAveragedMeasure c μ univ = μ univ := by
  rw [rotationAveragedMeasure, Measure.map_apply (continuous_rotateAbout c).measurable
    MeasurableSet.univ, preimage_univ, ← univ_prod_univ, Measure.prod_prod,
    measure_univ, one_mul]

/-- A rotation about `c` preserves distance from `c`. -/
theorem norm_rotateAbout_sub (Q : SpatialRotation) (c x : Position) :
    ‖rotateAbout Q c x - c‖ = ‖x-c‖ := by
  rw [rotateAbout, add_sub_cancel_left, LinearIsometryEquiv.norm_map]

/-- A charge measure carried by a concentric closed ball keeps that support after averaging. -/
theorem ae_norm_le_rotationAveragedMeasure (c : Position) (μ : Measure Position)
    [IsFiniteMeasure μ] {r : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x-c‖ ≤ r) :
    ∀ᵐ x ∂rotationAveragedMeasure c μ, ‖x-c‖ ≤ r := by
  unfold rotationAveragedMeasure
  apply (ae_map_iff (continuous_rotateAbout c).measurable.aemeasurable
    (measurableSet_le (measurable_id.sub measurable_const).norm measurable_const)).2
  have h := (measurePreserving_snd (μ := spatialRotationMeasure) (ν := μ)).quasiMeasurePreserving.ae hμ
  filter_upwards [h] with p hp
  change ‖rotateAbout p.1 c p.2 - c‖ ≤ r
  rwa [norm_rotateAbout_sub]

/-- Haar averaging makes a finite charge measure invariant under rotations about its centre. -/
theorem map_rotationAveragedMeasure_rotateAbout (c : Position) (μ : Measure Position)
    [IsFiniteMeasure μ] (Q : SpatialRotation) :
    (rotationAveragedMeasure c μ).map (rotateAbout Q c) = rotationAveragedMeasure c μ := by
  have hact := (continuous_rotateAbout c).measurable
  have hQ : Measurable (rotateAbout Q c) :=
    (continuous_const.add ((spatialRotationIsometry Q).continuous.comp
      (continuous_id.sub continuous_const))).measurable
  have hprod : MeasurePreserving (Prod.map (fun R : SpatialRotation => Q * R) id)
      (spatialRotationMeasure.prod μ) (spatialRotationMeasure.prod μ) :=
    (measurePreserving_mul_left spatialRotationMeasure Q).prod (MeasurePreserving.id μ)
  unfold rotationAveragedMeasure
  rw [Measure.map_map hQ hact]
  have heq : rotateAbout Q c ∘ (fun p : SpatialRotation × Position => rotateAbout p.1 c p.2) =
      (fun p : SpatialRotation × Position => rotateAbout p.1 c p.2) ∘
        Prod.map (fun R : SpatialRotation => Q * R) id := by
    funext p
    exact rotateAbout_mul Q p.1 c p.2
  rw [heq, ← Measure.map_map hact hprod.measurable, hprod.map_eq]

/-- Haar averaging is radial in the common screening API. -/
theorem isRadial_rotationAveragedMeasure (c : Position) (μ : Measure Position)
    [IsFiniteMeasure μ] : IsRadial c (rotationAveragedMeasure c μ) := by
  intro Q hQ
  obtain ⟨R, hR⟩ := exists_spatialRotation_isometry Q hQ
  have h := map_rotationAveragedMeasure_rotateAbout c μ R
  change (rotationAveragedMeasure c μ).map
    (fun x => c + spatialRotationIsometry R (x-c)) = rotationAveragedMeasure c μ at h
  rw [hR] at h
  exact h

/-- Equal-radius points are related by an orientation-preserving linear isometry. -/
theorem exists_rotation_map_eq_of_norm_eq {x y : Position} (h : ‖x‖ = ‖y‖) :
    ∃ Q : Position ≃ₗᵢ[ℝ] Position, Q x = y ∧ Q.toLinearEquiv.det = 1 := by
  classical
  by_cases hxy : x = y
  · exact ⟨LinearIsometryEquiv.refl ℝ Position, hxy, by simp⟩
  have hy : y ≠ 0 := by
    intro hy
    have hx : x = 0 := norm_eq_zero.mp (by simpa only [hy, norm_zero] using h)
    exact hxy (hx.trans hy.symm)
  have hdim : Module.finrank ℝ ↥(ℝ ∙ y)ᗮ = 2 := by
    have hf := (ℝ ∙ y).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hy] at hf
    have hp : Module.finrank ℝ Position = 3 := finrank_euclideanSpace_fin
    rw [hp] at hf
    omega
  have hbot : (ℝ ∙ y)ᗮ ≠ (⊥ : Submodule ℝ Position) := by
    intro hb
    rw [hb, finrank_bot] at hdim
    omega
  obtain ⟨w, hw, hw0⟩ := exists_mem_ne_zero_of_ne_bot hbot
  have hyw : y ∈ (ℝ ∙ w)ᗮ := by
    rw [mem_orthogonal_singleton_iff_inner_right] at hw ⊢
    rw [real_inner_comm]
    exact hw
  let Q₁ := (ℝ ∙ (x-y))ᗮ.reflection
  let Q₂ := (ℝ ∙ w)ᗮ.reflection
  refine ⟨Q₁.trans Q₂, ?_, ?_⟩
  · change Q₂ (Q₁ x) = y
    rw [show Q₁ x = y from reflection_sub h]
    exact reflection_mem_subspace_eq_self hyw
  · rw [LinearIsometryEquiv.toLinearEquiv_trans, LinearEquiv.det_trans]
    have h₁ : Q₁.toLinearEquiv.det = -1 := by
      dsimp [Q₁]
      rw [linearEquiv_det_reflection, orthogonal_orthogonal,
        finrank_span_singleton (sub_ne_zero.mpr hxy), pow_one]
    have h₂ : Q₂.toLinearEquiv.det = -1 := by
      dsimp [Q₂]
      rw [linearEquiv_det_reflection, orthogonal_orthogonal,
        finrank_span_singleton hw0, pow_one]
    rw [h₁, h₂]
    simp

end LiebThirring

end
