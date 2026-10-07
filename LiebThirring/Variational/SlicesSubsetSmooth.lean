/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SlicesSubset
public import LiebThirring.Sobolev.WeakFormDensity

/-! # Smooth restrictions to an arbitrary ordered particle block -/

@[expose] public section
open MeasureTheory WithLp SchwartzMap LineDeriv
open scoped ENNReal NNReal Classical SchwartzMap

namespace LiebThirring.Variational

/-- The selected block coordinate formula for ordered insertion. -/
theorem subsetOrderedInsertion_apply_mem {N k : ℕ} (S : Set (Fin N)) (e : Fin k ≃ S)
    (y : SubsetSpectatorConfiguration S) (x : Configuration k) (j : Fin k) (a : Fin 3) :
    subsetOrderedInsertion S e (y, x) ((e j).val, a) = x (j, a) := by
  change Sobolev.subsetInsertionMeasurableEquiv S
    (Sobolev.configurationReindexMeasurableEquiv e x, y) ((e j).val, a) = _
  rw [Sobolev.subsetInsertion_apply_mem]
  simp only [Sobolev.configurationReindexMeasurableEquiv, MeasurableEquiv.trans_apply,
    MeasurableEquiv.toLp_symm_apply, MeasurableEquiv.toLp_apply]
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : S × Fin 3 => ℝ) (e.prodCongr (Equiv.refl (Fin 3))) x.ofLp (j, a)

/-- The complementary block coordinate formula for ordered insertion. -/
theorem subsetOrderedInsertion_apply_compl {N k : ℕ} (S : Set (Fin N)) (e : Fin k ≃ S)
    (y : SubsetSpectatorConfiguration S) (x : Configuration k)
    (j : (Sᶜ : Set (Fin N))) (a : Fin 3) :
    subsetOrderedInsertion S e (y, x) (j.val, a) = y (j, a) := by
  change Sobolev.subsetInsertionMeasurableEquiv S
    (Sobolev.configurationReindexMeasurableEquiv e x, y) (j.val, a) = _
  exact Sobolev.subsetInsertion_apply_not_mem S _ j a

/-- Hilbert splitting of the full configuration into the two blocks. -/
noncomputable def subsetInsertionLinearIsometryEquiv {N : ℕ} (S : Set (Fin N)) :
    WithLp 2 (EuclideanSpace ℝ (S × Fin 3) × SubsetSpectatorConfiguration S) ≃ₗᵢ[ℝ]
      Configuration N :=
  (PiLp.sumPiLpEquivProdLpPiLp 2
    (fun _ : (S × Fin 3) ⊕ ((Sᶜ : Set (Fin N)) × Fin 3) => ℝ)).symm.trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Sobolev.subsetCoordinateEquiv S).symm)

/-- Coordinate realization of the Hilbert block splitting. -/
theorem subsetInsertionLinearIsometryEquiv_apply {N : ℕ} (S : Set (Fin N))
    (z : WithLp 2 (EuclideanSpace ℝ (S × Fin 3) × SubsetSpectatorConfiguration S)) :
    subsetInsertionLinearIsometryEquiv S z = Sobolev.subsetInsertionMeasurableEquiv S z.ofLp := by
  ext ja
  simp [subsetInsertionLinearIsometryEquiv, Sobolev.subsetInsertionMeasurableEquiv,
    MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi,
    MeasurableEquiv.prodCongr]

/-- Isometric inclusion of the selected block with zero complementary coordinates. -/
noncomputable def subsetConfigurationPairEmbedding {N k : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) : Configuration k →ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (S × Fin 3) × SubsetSpectatorConfiguration S) where
  toFun x := toLp 2 ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (e.prodCongr (Equiv.refl (Fin 3)))) x, (0 : SubsetSpectatorConfiguration S))
  map_add' x y := by apply WithLp.ofLp_injective; simp
  map_smul' c x := by apply WithLp.ofLp_injective; simp
  norm_map' x := by
    change ‖toLp 2 ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (e.prodCongr (Equiv.refl (Fin 3)))) x, (0 : SubsetSpectatorConfiguration S))‖ = ‖x‖
    rw [WithLp.norm_toLp_fst, LinearIsometryEquiv.norm_map]

/-- The selected block embeds isometrically into the full configuration. -/
noncomputable def subsetConfigurationEmbedding {N k : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) : Configuration k →ₗᵢ[ℝ] Configuration N :=
  (subsetInsertionLinearIsometryEquiv S).toLinearIsometry.comp
    (subsetConfigurationPairEmbedding S e)

/-- The selected block embedding equals insertion with complementary coordinates zero. -/
theorem subsetConfigurationEmbedding_apply {N k : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (x : Configuration k) :
    subsetConfigurationEmbedding S e x = subsetOrderedInsertion S e (0, x) := by
  change subsetInsertionLinearIsometryEquiv S (subsetConfigurationPairEmbedding S e x) = _
  rw [subsetInsertionLinearIsometryEquiv_apply]
  change Sobolev.subsetInsertionMeasurableEquiv S
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (e.prodCongr (Equiv.refl (Fin 3)))) x, 0) =
      Sobolev.subsetInsertionMeasurableEquiv S (Sobolev.configurationReindexMeasurableEquiv e x, 0)
  congr 2
  ext ja
  let a : Fin k := e.symm ja.1
  have hea : e a = ja.1 := e.apply_symm_apply ja.1
  have hmeas := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : S × Fin 3 => ℝ) (e.prodCongr (Equiv.refl (Fin 3))) x.ofLp (a, ja.2)
  have hpair : (e.prodCongr (Equiv.refl (Fin 3))) (a, ja.2) = ja := by
    ext <;> simp [hea]
  simp only [Sobolev.configurationReindexMeasurableEquiv, MeasurableEquiv.trans_apply,
    MeasurableEquiv.toLp_symm_apply, MeasurableEquiv.toLp_apply] at hmeas ⊢
  rw [← hpair]
  simpa using hmeas.symm

/-- Fixed spectator insertion is an affine translate of the selected-block inclusion. -/
theorem subsetOrderedInsertion_eq_affine {N k : ℕ} (S : Set (Fin N)) (e : Fin k ≃ S)
    (y : SubsetSpectatorConfiguration S) (x : Configuration k) :
    subsetOrderedInsertion S e (y, x) =
      subsetConfigurationEmbedding S e x + subsetOrderedInsertion S e (y, 0) := by
  rw [subsetConfigurationEmbedding_apply]
  ext ja
  rcases ja with ⟨j, a⟩
  by_cases hj : j ∈ S
  · let h : S := ⟨j, hj⟩
    have he : (e (e.symm h)).val = j := congrArg Subtype.val (e.apply_symm_apply h)
    rw [← he]
    simp only [PiLp.add_apply, subsetOrderedInsertion_apply_mem, PiLp.zero_apply, add_zero]
  · simp only [PiLp.add_apply]
    have hc : (⟨j, hj⟩ : (Sᶜ : Set (Fin N))).val = j := rfl
    rw [← hc, subsetOrderedInsertion_apply_compl, subsetOrderedInsertion_apply_compl,
      subsetOrderedInsertion_apply_compl, PiLp.zero_apply, zero_add]

/-- A selected coordinate basis vector maps to the corresponding original coordinate. -/
theorem subsetConfigurationEmbedding_coordinateVector {N k : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (j : Fin k) (a : Fin 3) :
    subsetConfigurationEmbedding S e (Sobolev.coordinateVector (j, a)) =
      Sobolev.coordinateVector ((e j).val, a) := by
  rw [subsetConfigurationEmbedding_apply]
  ext lb
  rcases lb with ⟨l, b⟩
  by_cases hl : l ∈ S
  · let h : S := ⟨l, hl⟩
    have he : (e (e.symm h)).val = l := congrArg Subtype.val (e.apply_symm_apply h)
    rw [← he, subsetOrderedInsertion_apply_mem]
    by_cases hlj : l = (e j).val
    · have hs : h = e j := Subtype.ext hlj
      simp [h, hs, Sobolev.coordinateVector]
    · have hs : e.symm h ≠ j := by
        intro hh
        have hh' := congrArg (fun v => (e v).val) hh
        rw [he] at hh'
        exact hlj hh'
      simp [Sobolev.coordinateVector, hs, show h.val ≠ (e j).val from hlj]
  · have hne : l ≠ (e j).val := by
      intro h
      exact hl (h ▸ (e j).property)
    have hc : (⟨l, hl⟩ : (Sᶜ : Set (Fin N))).val = l := rfl
    rw [← hc, subsetOrderedInsertion_apply_compl]
    simp [Sobolev.coordinateVector, hne]

/-- Fixed-complement insertion is temperate. -/
theorem subsetOrderedInsertion_hasTemperateGrowth {N k : ℕ} (S : Set (Fin N)) (e : Fin k ≃ S)
    (y : SubsetSpectatorConfiguration S) :
    (fun x => subsetOrderedInsertion S e (y, x)).HasTemperateGrowth := by
  have heq : (fun x => subsetOrderedInsertion S e (y, x)) =
      fun x => subsetConfigurationEmbedding S e x + subsetOrderedInsertion S e (y, 0) :=
    funext (subsetOrderedInsertion_eq_affine S e y)
  rw [heq]
  exact (subsetConfigurationEmbedding S e).toContinuousLinearMap.hasTemperateGrowth.add (.const _)

/-- Fixed-complement insertion is distance preserving. -/
theorem subsetOrderedInsertion_antilipschitz {N k : ℕ} (S : Set (Fin N)) (e : Fin k ≃ S)
    (y : SubsetSpectatorConfiguration S) :
    AntilipschitzWith 1 (fun x => subsetOrderedInsertion S e (y, x)) := by
  rw [antilipschitzWith_iff_le_mul_dist]
  intro x z
  rw [subsetOrderedInsertion_eq_affine S e y x, subsetOrderedInsertion_eq_affine S e y z]
  simp only [dist_eq_norm, add_sub_add_right_eq_sub]
  rw [← map_sub, LinearIsometry.norm_map]
  simp

/-- Fix complementary spins and regroup the selected spin amplitude. -/
noncomputable def subsetSpinEvaluationCLM {N k q : ℕ} (S : Set (Fin N)) (e : Fin k ≃ S)
    (α : SubsetSpectatorSpins S q) : SpinAmplitudes N q →L[ℂ] SpinAmplitudes k q :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : SubsetSpectatorSpins S q => SpinAmplitudes k q) α).comp
    (subsetSpinCurrying S e).toContinuousLinearEquiv.toContinuousLinearMap

/-- Restrict a Schwartz state to a fixed complement position and spin. -/
noncomputable def subsetParticleSchwartz {N k q : ℕ} (S : Set (Fin N)) (e : Fin k ≃ S)
    (y : SubsetSpectatorConfiguration S) (α : SubsetSpectatorSpins S q)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) : 𝓢(Configuration k, SpinAmplitudes k q) :=
  SchwartzMap.postcompCLM (subsetSpinEvaluationCLM S e α)
    (SchwartzMap.compCLMOfAntilipschitz ℂ (subsetOrderedInsertion_hasTemperateGrowth S e y)
      (subsetOrderedInsertion_antilipschitz S e y) f)

@[simp] theorem subsetParticleSchwartz_apply {N k q : ℕ} (S : Set (Fin N)) (e : Fin k ≃ S)
    (y : SubsetSpectatorConfiguration S) (α : SubsetSpectatorSpins S q)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (x : Configuration k) (s : SpinLabels k q) :
    subsetParticleSchwartz S e y α f x s =
      f (subsetOrderedInsertion S e (y, x)) (subsetOrderedSpinEquiv S e (α, s)) := rfl

/-- Differentiation in a selected coordinate commutes with smooth block restriction. -/
theorem lineDerivOp_subsetParticleSchwartz {N k q : ℕ} (S : Set (Fin N)) (e : Fin k ≃ S)
    (y : SubsetSpectatorConfiguration S) (α : SubsetSpectatorSpins S q)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (j : Fin k) (a : Fin 3) :
    lineDerivOp (Sobolev.coordinateVector (j, a)) (subsetParticleSchwartz S e y α f) =
      subsetParticleSchwartz S e y α
        (lineDerivOp (Sobolev.coordinateVector ((e j).val, a)) f) := by
  ext x s
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, subsetParticleSchwartz_apply]
  change ((fderiv ℝ (fun z => subsetSpinEvaluationCLM S e α
    (f (subsetOrderedInsertion S e (y, z)))) x) (Sobolev.coordinateVector (j, a))) s = _
  have heq : (fun z => subsetOrderedInsertion S e (y, z)) =
      fun z => subsetConfigurationEmbedding S e z + subsetOrderedInsertion S e (y, 0) :=
    funext (subsetOrderedInsertion_eq_affine S e y)
  have hg : HasFDerivAt (fun z => subsetOrderedInsertion S e (y, z))
      (subsetConfigurationEmbedding S e).toContinuousLinearMap x := by
    rw [heq]
    exact HasFDerivAt.add_const (subsetOrderedInsertion S e (y, 0))
      (subsetConfigurationEmbedding S e).toContinuousLinearMap.hasFDerivAt
  have hf := ((f.smooth 1).differentiable (by norm_num)).differentiableAt.hasFDerivAt
    (x := subsetOrderedInsertion S e (y, x))
  have htotal := (subsetSpinEvaluationCLM S e α).restrictScalars ℝ |>.hasFDerivAt.comp x
    (hf.comp x hg)
  have hfd := htotal.fderiv
  change ((fderiv ℝ ((subsetSpinEvaluationCLM S e α).restrictScalars ℝ ∘
    (fun z => f z) ∘ (fun z => subsetOrderedInsertion S e (y, z))) x)
      (Sobolev.coordinateVector (j, a))) s = _
  rw [hfd]
  simp only [ContinuousLinearMap.comp_apply]
  rw [show (subsetConfigurationEmbedding S e).toContinuousLinearMap
    (Sobolev.coordinateVector (j, a)) = Sobolev.coordinateVector ((e j).val, a) from
      subsetConfigurationEmbedding_coordinateVector S e j a]
  rfl

end LiebThirring.Variational
end
