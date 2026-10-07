/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.WeakFormDensity
public import LiebThirring.Variational.SlicesReindex

/-! # Smooth residual slices -/

@[expose] public section

open MeasureTheory WithLp
open scoped ENNReal SchwartzMap
open LineDeriv

namespace LiebThirring.Variational

/-- The Hilbert splitting of a configuration into particle `i` and its complement. -/
noncomputable def configurationInsertionLinearIsometryEquiv {N : ℕ} (i : Fin N) :
    WithLp 2 (Position × OtherConfiguration i) ≃ₗᵢ[ℝ] Configuration N :=
  ((PiLp.sumPiLpEquivProdLpPiLp 2
      (fun _ : Fin 3 ⊕ ({j : Fin N // j ≠ i} × Fin 3) => ℝ)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (insertionIndexEquiv i).symm))

@[simp] theorem configurationInsertionLinearIsometryEquiv_apply {N : ℕ} (i : Fin N)
    (z : WithLp 2 (Position × OtherConfiguration i)) :
    configurationInsertionLinearIsometryEquiv i z = insertParticle i z.ofLp.1 z.ofLp.2 := by
  ext ja
  simp [configurationInsertionLinearIsometryEquiv, insertParticle, insertionIndexEquiv]
  split <;> rfl

/-- Isometric embedding of a residual configuration with the selected particle at zero. -/
noncomputable def residualConfigurationPairEmbedding {N k : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) :
    Configuration k →ₗᵢ[ℝ] WithLp 2 (Position × OtherConfiguration i) :=
    { toFun := fun y => toLp 2
        ((0 : Position), (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
          (e.prodCongr (Equiv.refl (Fin 3)))) y)
      map_add' := by intro x y; apply WithLp.ofLp_injective; simp
      map_smul' := by intro c x; apply WithLp.ofLp_injective; simp
      norm_map' := by
        intro y
        change ‖toLp 2
          ((0 : Position), (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
            (e.prodCongr (Equiv.refl (Fin 3)))) y)‖ = ‖y‖
        rw [WithLp.norm_toLp_snd]
        rw [LinearIsometryEquiv.norm_map]
        }

/-- Isometric embedding of a residual configuration with the selected particle at zero. -/
noncomputable def residualConfigurationEmbedding {N k : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) : Configuration k →ₗᵢ[ℝ] Configuration N :=
  (configurationInsertionLinearIsometryEquiv i).toLinearIsometry.comp
    (residualConfigurationPairEmbedding i e)

/-- A residual coordinate basis vector maps to the corresponding original coordinate. -/
theorem residualConfigurationEmbedding_coordinateVector {N k : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (a : Fin k) (b : Fin 3) :
    residualConfigurationEmbedding i e (Sobolev.coordinateVector (a, b)) =
      Sobolev.coordinateVector ((e a).val, b) := by
  change configurationInsertionLinearIsometryEquiv i
    (residualConfigurationPairEmbedding i e (Sobolev.coordinateVector (a, b))) = _
  rw [configurationInsertionLinearIsometryEquiv_apply]
  ext jb
  simp only [residualConfigurationPairEmbedding, LinearIsometry.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Sobolev.coordinateVector, EuclideanSpace.basisFun_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, insertParticle, PiLp.toLp_apply]
  split
  · rename_i hsel
    have hpair : jb ≠ ((e a).val, b) := by
      intro hp
      exact (e a).property (hsel ▸ (congrArg Prod.fst hp).symm)
    simp [hpair]
  · rename_i hsel
    by_cases hb : jb.1 = (e a).val
    · have hsub : (⟨jb.1, hsel⟩ : {j : Fin N // j ≠ i}) = e a := Subtype.ext hb
      have hinv : e.symm (⟨jb.1, hsel⟩ : {j : Fin N // j ≠ i}) = a := by
        rw [hsub, e.symm_apply_apply]
      by_cases hc : jb.2 = b
      · have hp : jb = ((e a).val, b) := Prod.ext hb hc
        simp [hp]
      · have hp : jb ≠ ((e a).val, b) := by
          intro hp
          exact hc (congrArg Prod.snd hp)
        simp [hinv, hc, hp]
    · have hsub : (⟨jb.1, hsel⟩ : {j : Fin N // j ≠ i}) ≠ e a := by
        intro hs
        exact hb (congrArg Subtype.val hs)
      have hpair : jb ≠ ((e a).val, b) := by
        intro hp
        exact hb (congrArg Prod.fst hp)
      have hinv : e.symm (⟨jb.1, hsel⟩ : {j : Fin N // j ≠ i}) ≠ a := by
        intro heq
        apply hsub
        rw [← heq, e.apply_symm_apply]
      simp [hinv, hpair]

/-- Affine insertion of fixed selected coordinates is temperate and distance preserving. -/
noncomputable def residualAffineInsertion {N k : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (x : Position) : Configuration k → Configuration N :=
  fun y => residualConfigurationEmbedding i e y + insertParticle i x 0

theorem configurationLinearReindex_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (y : EuclideanSpace ℝ (ι × Fin 3)) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
        (e.prodCongr (Equiv.refl (Fin 3))) y =
      Sobolev.configurationReindexMeasurableEquiv e y := by
  ext ja
  let a : ι := e.symm ja.1
  have hea : e a = ja.1 := e.apply_symm_apply ja.1
  have hmeas := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : κ × Fin 3 => ℝ) (e.prodCongr (Equiv.refl (Fin 3))) y.ofLp (a, ja.2)
  have hpair : (e.prodCongr (Equiv.refl (Fin 3))) (a, ja.2) = ja := by
    ext <;> simp [hea]
  simp only [Sobolev.configurationReindexMeasurableEquiv, MeasurableEquiv.trans_apply,
    MeasurableEquiv.toLp_symm_apply, MeasurableEquiv.toLp_apply] at hmeas ⊢
  rw [← hpair]
  simpa using hmeas.symm

/-- The affine Hilbert embedding is literal insertion with reindexed residual coordinates. -/
theorem residualAffineInsertion_eq {N k : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (x : Position) (y : Configuration k) :
    residualAffineInsertion i e x y =
      insertParticle i x (Sobolev.configurationReindexMeasurableEquiv e y) := by
  rw [residualAffineInsertion]
  rw [residualConfigurationEmbedding]
  change configurationInsertionLinearIsometryEquiv i
      (residualConfigurationPairEmbedding i e y) + insertParticle i x 0 = _
  rw [configurationInsertionLinearIsometryEquiv_apply]
  simp only [residualConfigurationPairEmbedding, LinearIsometry.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk]
  rw [configurationLinearReindex_eq]
  ext jb
  simp only [PiLp.add_apply, insertParticle, PiLp.toLp_apply]
  split <;> simp

theorem residualAffineInsertion_hasTemperateGrowth {N k : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (x : Position) :
    (residualAffineInsertion i e x).HasTemperateGrowth := by
  exact (residualConfigurationEmbedding i e).toContinuousLinearMap.hasTemperateGrowth.add
    (.const _)

theorem residualAffineInsertion_antilipschitz {N k : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (x : Position) :
    AntilipschitzWith 1 (residualAffineInsertion i e x) := by
  rw [antilipschitzWith_iff_le_mul_dist]
  intro a b
  simp only [residualAffineInsertion, dist_eq_norm, add_sub_add_right_eq_sub]
  rw [← map_sub, LinearIsometry.norm_map]
  simp

/-- Extract the selected spin and reindex the residual spin amplitudes. -/
noncomputable def residualSpinEvaluationCLM {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (s : Fin q) :
    SpinAmplitudes N q →L[ℂ] SpinAmplitudes k q :=
  (residualSpinReindex i e).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((PiLp.proj (𝕜 := ℂ) 2
      (fun _ : Fin q => EuclideanSpace ℂ (OtherSpinLabels i q)) s).comp
      (spinCurryingLinearIsometryEquiv i).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem residualSpinEvaluationCLM_apply {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (s : Fin q) (v : SpinAmplitudes N q)
    (t : SpinLabels k q) :
    residualSpinEvaluationCLM i e s v t = v (insertSpin i s (fun j => t (e.symm j))) := by
  simp [residualSpinEvaluationCLM, residualSpinReindex, residualSpinLabelEquiv]

/-- Restriction of a Schwartz state to fixed selected spatial coordinates. -/
noncomputable def residualSpatialSchwartz {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (x : Position)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    𝓢(Configuration k, SpinAmplitudes N q) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (residualAffineInsertion_hasTemperateGrowth i e x)
    (residualAffineInsertion_antilipschitz i e x) f

/-- Smooth residual state after fixing both the selected position and spin. -/
noncomputable def residualParticleSchwartz {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (x : Position) (s : Fin q)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    𝓢(Configuration k, SpinAmplitudes k q) :=
  SchwartzMap.postcompCLM (residualSpinEvaluationCLM i e s)
    (residualSpatialSchwartz i e x f)

@[simp] theorem residualParticleSchwartz_apply {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (x : Position) (s : Fin q)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (y : Configuration k)
    (t : SpinLabels k q) :
    residualParticleSchwartz i e x s f y t =
      f (residualAffineInsertion i e x y) (insertSpin i s (fun j => t (e.symm j))) := by
  rfl

/-- Coordinate differentiation commutes with smooth residual restriction. -/
theorem lineDerivOp_residualParticleSchwartz {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (x : Position) (s : Fin q)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (a : Fin k) (b : Fin 3) :
    lineDerivOp (Sobolev.coordinateVector (a, b))
        (residualParticleSchwartz i e x s f) =
      residualParticleSchwartz i e x s
        (lineDerivOp (Sobolev.coordinateVector ((e a).val, b)) f) := by
  ext y t
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, residualParticleSchwartz_apply]
  change ((fderiv ℝ (fun z => residualSpinEvaluationCLM i e s
    (f (residualAffineInsertion i e x z))) y) (Sobolev.coordinateVector (a, b))) t = _
  have hg : HasFDerivAt (residualAffineInsertion i e x)
      (residualConfigurationEmbedding i e).toContinuousLinearMap y := by
    change HasFDerivAt (fun z => residualConfigurationEmbedding i e z +
      insertParticle i x 0) (residualConfigurationEmbedding i e).toContinuousLinearMap y
    exact HasFDerivAt.add_const (insertParticle i x 0)
      (residualConfigurationEmbedding i e).toContinuousLinearMap.hasFDerivAt
  have hf : HasFDerivAt (fun z => f z) (fderiv ℝ (fun z => f z)
      (residualAffineInsertion i e x y)) (residualAffineInsertion i e x y) :=
    ((f.smooth 1).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have htotal := (residualSpinEvaluationCLM i e s).restrictScalars ℝ |>.hasFDerivAt.comp y
    (hf.comp y hg)
  have hfd := htotal.fderiv
  change ((fderiv ℝ ((residualSpinEvaluationCLM i e s).restrictScalars ℝ ∘
    (fun z => f z) ∘ residualAffineInsertion i e x) y)
      (Sobolev.coordinateVector (a, b))) t = _
  rw [hfd]
  simp only [ContinuousLinearMap.comp_apply]
  change (residualSpinEvaluationCLM i e s
    ((fderiv ℝ (fun z => f z) (residualAffineInsertion i e x y))
      (residualConfigurationEmbedding i e (Sobolev.coordinateVector (a, b))))) t = _
  rw [residualConfigurationEmbedding_coordinateVector]
  exact residualSpinEvaluationCLM_apply i e s _ t

end LiebThirring.Variational

end
