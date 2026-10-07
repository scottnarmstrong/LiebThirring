/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SlicesReindex
public import LiebThirring.TFQuantum.SlaterProduct
public import LiebThirring.TFQuantum.SlaterFourierTensor

/-! # Fourier transport under particle reindexing

Orthogonal pullback commutes with the actual L² Fourier transform even when
source and target are different Euclidean carriers. Applying this together
with bounded spin reindexing gives Fourier covariance of one-particle spatial
identification and of residual-state ordering. The genuine inserted L² tensor
has its literal product representative almost everywhere. Proof: argument
Slater construction; direct proof coordinate transport and product-measure argument.
-/

public section

open MeasureTheory
open scoped SchwartzMap FourierTransform

namespace LiebThirring.SlaterTensor

variable {V W H : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Schwartz Fourier covariance under an orthogonal change of variables. -/
theorem fourier_comp_isometry (A : W ≃ₗᵢ[ℝ] V) (f : 𝓢(V, H)) :
    𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv (𝓕 f) := by
  ext x
  exact Real.fourier_comp_linearIsometry A (fun y => f y) x

omit [CompleteSpace H] in
/-- The measure-preserving L² pullback agrees with composition on Schwartz maps. -/
theorem compMeasurePreserving_toLp (A : W ≃ₗᵢ[ℝ] V) (f : 𝓢(V, H)) :
    Lp.compMeasurePreserving A A.measurePreserving (f.toLp 2 (volume : Measure V)) =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (f.toLp 2 (volume : Measure V)) A.measurePreserving,
    A.measurePreserving.quasiMeasurePreserving.ae (f.coeFn_toLp 2 (volume : Measure V)),
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f).coeFn_toLp 2 volume]
    with x hx hf hg
  rw [hx, hg]
  exact hf

/-- Fourier on L² commutes with orthogonal spatial pullback. -/
theorem fourier_compMeasurePreserving (A : W ≃ₗᵢ[ℝ] V)
    (f : Lp H 2 (volume : Measure V)) :
    𝓕 (Lp.compMeasurePreserving A A.measurePreserving f) =
      Lp.compMeasurePreserving A A.measurePreserving (𝓕 f) := by
  apply DenseRange.induction_on (p := fun f : Lp H 2 (volume : Measure V) =>
    𝓕 (Lp.compMeasurePreserving A A.measurePreserving f) =
      Lp.compMeasurePreserving A A.measurePreserving (𝓕 f))
    (SchwartzMap.denseRange_toLpCLM (E := V) (F := H) (p := 2)
      (μ := (volume : Measure V)) ENNReal.ofNat_ne_top) f
  · have hc : Continuous (Lp.compMeasurePreserving A A.measurePreserving :
        Lp H 2 (volume : Measure V) → Lp H 2 (volume : Measure W)) :=
      (Lp.compMeasurePreservingₗᵢ ℂ A A.measurePreserving).continuous
    exact isClosed_eq ((Lp.fourierTransformₗᵢ W H).continuous.comp hc)
      (hc.comp (Lp.fourierTransformₗᵢ V H).continuous)
  · intro g
    change 𝓕 (Lp.compMeasurePreserving A A.measurePreserving (g.toLp 2 volume)) =
      Lp.compMeasurePreserving A A.measurePreserving (𝓕 (g.toLp 2 volume))
    rw [compMeasurePreserving_toLp, SchwartzMap.toLp_fourier_eq, fourier_comp_isometry,
      SchwartzMap.toLp_fourier_eq, compMeasurePreserving_toLp]

end LiebThirring.SlaterTensor

namespace LiebThirring

@[expose] noncomputable def orbitalSpinEquiv (q : ℕ) :
    SpinAmplitudes 1 q ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin q) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ({ toFun := fun s : SpinLabels 1 q => s 0
       invFun := oneParticleSpinLabel
       left_inv := fun s => by funext i; exact congrArg s (Subsingleton.elim 0 i)
       right_inv := fun _ => rfl } : SpinLabels 1 q ≃ Fin q)

@[expose] noncomputable def orbitalSpatialStateEquiv (q : ℕ) :
    State 1 q ≃ₗᵢ[ℂ] Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position) :=
  (l2PullbackEquiv (E := SpinAmplitudes 1 q)
    oneParticleConfigurationEquiv.toMeasurableEquiv
    oneParticleConfigurationEquiv.measurePreserving).trans
      (l2TargetEquiv volume (orbitalSpinEquiv q))

theorem orbitalSpatialStateEquiv_ae {q : ℕ} (u : State 1 q) :
    ∀ᵐ x : Position, ∀ t : Fin q,
      orbitalSpatialStateEquiv q u x t = orbitalValue u x t := by
  filter_upwards [l2TargetEquiv_ae volume (orbitalSpinEquiv q)
      (l2PullbackEquiv (E := SpinAmplitudes 1 q)
        oneParticleConfigurationEquiv.toMeasurableEquiv
        oneParticleConfigurationEquiv.measurePreserving u),
    l2PullbackEquiv_ae (E := SpinAmplitudes 1 q)
      oneParticleConfigurationEquiv.toMeasurableEquiv
      oneParticleConfigurationEquiv.measurePreserving u] with x hx hy
  intro t
  have hh := hx.trans (congrArg (orbitalSpinEquiv q) hy)
  exact congrArg (fun z : EuclideanSpace ℂ (Fin q) => z t) hh

theorem fourier_orbitalSpatialStateEquiv {q : ℕ} (u : State 1 q) :
    𝓕 (orbitalSpatialStateEquiv q u) = orbitalSpatialStateEquiv q (𝓕 u) := by
  change 𝓕 ((orbitalSpinEquiv q).toContinuousLinearEquiv.toContinuousLinearMap.compLp
    (Lp.compMeasurePreserving oneParticleConfigurationEquiv
      oneParticleConfigurationEquiv.measurePreserving u)) = _
  rw [Fourier.fourier_compLp, SlaterTensor.fourier_compMeasurePreserving]
  rfl

@[expose] noncomputable def configurationReindexLinearIsometryEquiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    EuclideanSpace ℝ (ι × Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (κ × Fin 3) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (e.prodCongr (Equiv.refl (Fin 3)))

theorem configurationReindexLinearIsometryEquiv_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (x : EuclideanSpace ℝ (ι × Fin 3)) :
    configurationReindexLinearIsometryEquiv e x =
      Sobolev.configurationReindexMeasurableEquiv e x := by
  ext ja
  change x (e.symm ja.1, ja.2) =
    (Equiv.piCongrLeft (fun _ : κ × Fin 3 => ℝ)
      (e.prodCongr (Equiv.refl (Fin 3)))) (fun b => x b) ja
  rw [Equiv.piCongrLeft_apply_eq_cast, cast_eq]
  rfl

theorem fourier_residualStateReindex {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : RestState i q) :
    𝓕 (Variational.residualStateReindex i e u) =
      Variational.residualStateReindex i e (𝓕 u) := by
  let A := configurationReindexLinearIsometryEquiv e
  have hA : (A : Configuration k → OtherConfiguration i) =
      Sobolev.configurationReindexMeasurableEquiv e :=
    funext (configurationReindexLinearIsometryEquiv_apply e)
  change 𝓕 ((Variational.residualSpinReindex i e).toContinuousLinearEquiv.toContinuousLinearMap.compLp
    (Lp.compMeasurePreserving (Sobolev.configurationReindexMeasurableEquiv e)
      (Sobolev.measurePreserving_configurationReindex e) u)) = _
  rw [Fourier.fourier_compLp]
  have hp (v : RestState i q) :
      Lp.compMeasurePreserving (Sobolev.configurationReindexMeasurableEquiv e)
        (Sobolev.measurePreserving_configurationReindex e) v =
      Lp.compMeasurePreserving A A.measurePreserving v := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving v
      (Sobolev.measurePreserving_configurationReindex e),
      Lp.coeFn_compMeasurePreserving v A.measurePreserving] with x hx hy
    rw [hx, hy, hA]
  rw [hp, SlaterTensor.fourier_compMeasurePreserving]
  exact congrArg
    (Variational.residualSpinReindex i e).toContinuousLinearEquiv.toContinuousLinearMap.compLp
    (hp (𝓕 u)).symm

theorem fourier_residualStateReindex_symm {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State k q) :
    𝓕 ((Variational.residualStateReindex i e).symm u) =
      (Variational.residualStateReindex i e).symm (𝓕 u) := by
  apply (Variational.residualStateReindex i e).injective
  rw [← fourier_residualStateReindex, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]

theorem residualStateReindex_symm_ae {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State k q) :
    ∀ᵐ y : OtherConfiguration i, ∀ t : OtherSpinLabels i q,
      (Variational.residualStateReindex i e).symm u y t =
        u ((Sobolev.configurationReindexMeasurableEquiv e).symm y)
          (fun j => t (e j)) := by
  have ha := Variational.residualStateReindex_ae i e
    ((Variational.residualStateReindex i e).symm u)
  rw [LinearIsometryEquiv.apply_symm_apply] at ha
  have hb := (MeasurePreserving.symm (Sobolev.configurationReindexMeasurableEquiv e)
    (Sobolev.measurePreserving_configurationReindex e)).quasiMeasurePreserving.ae ha
  filter_upwards [hb] with y hy
  intro t
  simpa only [MeasurableEquiv.apply_symm_apply, Equiv.apply_symm_apply] using
    (hy (fun j => t (e j))).symm

theorem oneParticleInsertion_coe_ae {N q : ℕ} (i : Fin N)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position))
    (v : RestState i q) :
    (oneParticleInsertion i f v : Configuration N → SpinAmplitudes N q) =ᵐ[volume]
      particleTensorFunction i f v := by
  let ψ := oneParticleInsertion i f v
  have hnested : ∀ᵐ x : Position, ∀ᵐ y : OtherConfiguration i,
      ψ (insertParticle i x y) = particleTensorFunction i f v (insertParticle i x y) := by
    filter_upwards [oneParticleInsertion_ae i f v] with x hx
    filter_upwards [ae_all_iff.mpr hx] with y hy
    apply (spinCurryingLinearIsometryEquiv i).injective
    ext s t
    rw [spinCurryingLinearIsometryEquiv_apply, spinCurryingLinearIsometryEquiv_apply,
      particleTensorFunction_insert, hy s t]
  have hf := (Lp.stronglyMeasurable f).comp_measurable
    (measurable_fst.comp (insertionMeasurableEquiv i).symm.measurable)
  have hv := (Lp.stronglyMeasurable v).comp_measurable
    (measurable_snd.comp (insertionMeasurableEquiv i).symm.measurable)
  have hF := (spinCurryingLinearIsometryEquiv (q := q) i).symm.continuous.comp_stronglyMeasurable
    ((tensorInsertionBilinear (ι := Fin q) (H := EuclideanSpace ℂ (OtherSpinLabels i q))).continuous₂.comp_stronglyMeasurable (hv.prodMk hf))
  have hψ := (Lp.stronglyMeasurable ψ).measurable.comp
    (measurePreserving_insertParticle i).measurable
  have hF' : Measurable (fun z : Position × OtherConfiguration i =>
      particleTensorFunction i f v (insertParticle i z.1 z.2)) :=
    hF.measurable.comp (measurePreserving_insertParticle i).measurable
  have hprod := (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hψ hF')).mpr hnested
  have h := (MeasurePreserving.symm (insertionMeasurableEquiv i)
    (measurePreserving_insertion i)).quasiMeasurePreserving.ae hprod
  filter_upwards [h] with X hX
  simpa only [Function.comp_apply, ← insertionMeasurableEquiv_apply,
    MeasurableEquiv.apply_symm_apply] using hX

theorem fourier_zeroParticleState {q : ℕ} (ψ : State 0 q) : 𝓕 ψ = ψ := by
  apply DenseRange.induction_on (p := fun ψ : State 0 q => 𝓕 ψ = ψ)
    (SchwartzMap.denseRange_toLpCLM (E := Configuration 0) (F := SpinAmplitudes 0 q)
      (p := 2) (μ := (volume : Measure (Configuration 0))) ENNReal.ofNat_ne_top) ψ
  · exact isClosed_eq (Lp.fourierTransformₗᵢ _ _).continuous continuous_id
  · intro f
    change 𝓕 (f.toLp 2 volume) = f.toLp 2 volume
    rw [SchwartzMap.toLp_fourier_eq]
    congr 1
    ext x
    rw [SchwartzMap.fourier_coe, Real.fourier_eq, volume_euclideanSpace_eq_dirac]
    simp [show x = (0 : Configuration 0) from Subsingleton.elim _ _]

end LiebThirring
end
