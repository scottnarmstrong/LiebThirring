/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoStability.FourierFactor

/-! # The two spatial block orders and their Fourier transforms -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap FourierTransform

namespace LiebThirring.ThermoStability

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

/-- Nuclear L² fibres with electron position as the outer coordinate. -/
@[expose] noncomputable def nuclearFibreField {N M q : ℕ} (ψ : QuantumState N M q) :
    Lp (Lp (SpinAmplitudes N q) 2 (volume : Measure (Configuration M))) 2
      (volume : Measure (Configuration N)) :=
  l2Curry (Lp.compMeasurePreserving (MeasurableEquiv.toLp 2 _)
    (WithLp.volume_preserving_toLp _ _) ψ)

/-- The electronic-outer field is also a surjective complex linear isometry. -/
@[expose] noncomputable def nuclearFibreEquiv (N M q : ℕ) :
    QuantumState N M q ≃ₗᵢ[ℂ]
      Lp (Lp (SpinAmplitudes N q) 2 (volume : Measure (Configuration M))) 2
        (volume : Measure (Configuration N)) :=
  (l2PullbackEquiv (E := SpinAmplitudes N q) (MeasurableEquiv.toLp 2 _)
    (WithLp.volume_preserving_toLp _ _)).trans l2CurryLinearIsometryEquiv

theorem blockSwap_nuclearFibreField {N M q : ℕ} (ψ : QuantumState N M q) :
    blockSwapCurrying (nuclearFibreField ψ) = electronFibreField ψ := by
  let g := Lp.compMeasurePreserving (MeasurableEquiv.toLp 2 (Configuration N × Configuration M))
    (WithLp.volume_preserving_toLp _ _) ψ
  have hinv : (l2CurryLinearIsometryEquiv (E := SpinAmplitudes N q)
    (μ := (volume : Measure (Configuration N)))
    (ν := (volume : Measure (Configuration M)))).symm (nuclearFibreField ψ) = g :=
      (l2CurryLinearIsometryEquiv (E := SpinAmplitudes N q)
        (μ := (volume : Measure (Configuration N)))
        (ν := (volume : Measure (Configuration M)))).symm_apply_apply g
  rw [blockSwapCurrying_apply, hinv]
  apply congrArg l2Curry
  apply Lp.ext
  filter_upwards [l2PullbackEquiv_ae MeasurableEquiv.prodComm Measure.measurePreserving_swap g,
    (Measure.measurePreserving_swap (μ := (volume : Measure (Configuration M)))
      (ν := (volume : Measure (Configuration N)))).quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving ψ (WithLp.volume_preserving_toLp _ _)),
    Lp.coeFn_compMeasurePreserving ψ (measurePreserving_nuclearFirstEquiv N M)] with a ha hg hψ
  exact ha.trans (hg.trans hψ.symm)

theorem blockSwap_electronFibreField {N M q : ℕ} (ψ : QuantumState N M q) :
    blockSwapCurrying (electronFibreField ψ) = nuclearFibreField ψ := by
  let g := Lp.compMeasurePreserving (nuclearFirstEquiv N M)
    (measurePreserving_nuclearFirstEquiv N M) ψ
  have hinv : (l2CurryLinearIsometryEquiv (E := SpinAmplitudes N q)
    (μ := (volume : Measure (Configuration M)))
    (ν := (volume : Measure (Configuration N)))).symm (electronFibreField ψ) = g :=
      (l2CurryLinearIsometryEquiv (E := SpinAmplitudes N q)
        (μ := (volume : Measure (Configuration M)))
        (ν := (volume : Measure (Configuration N)))).symm_apply_apply g
  rw [blockSwapCurrying_apply, hinv]
  apply congrArg l2Curry
  apply Lp.ext
  filter_upwards [l2PullbackEquiv_ae MeasurableEquiv.prodComm Measure.measurePreserving_swap g,
    (Measure.measurePreserving_swap (μ := (volume : Measure (Configuration N)))
      (ν := (volume : Measure (Configuration M)))).quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving ψ (measurePreserving_nuclearFirstEquiv N M)),
    Lp.coeFn_compMeasurePreserving ψ (WithLp.volume_preserving_toLp _ _)] with a ha hg hψ
  exact ha.trans (hg.trans hψ.symm)

theorem nuclearFibreField_jointTensor {N M q : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Configuration M))) (v : State N q) :
    nuclearFibreField (jointTensor f v) = (blockScalarInsertion f).compLp v := by
  rw [← blockSwap_electronFibreField, electronFibreField_jointTensor]
  exact blockSwapCurrying_tensor f v

theorem nuclearFourier_blockScalarInsertion {N M q : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Configuration M))) (v : State N q) :
    (Lp.fourierTransformₗᵢ (Configuration M) (SpinAmplitudes N q)).toContinuousLinearEquiv.toContinuousLinearMap.compLp
      ((blockScalarInsertion f).compLp v) = (blockScalarInsertion (𝓕 f)).compLp v := by
  let Fn := (Lp.fourierTransformₗᵢ (Configuration M) (SpinAmplitudes N q)).toContinuousLinearEquiv.toContinuousLinearMap
  apply Lp.ext
  filter_upwards [Fn.coeFn_compLp ((blockScalarInsertion f).compLp v),
    (blockScalarInsertion f).coeFn_compLp v,
    (blockScalarInsertion (𝓕 f)).coeFn_compLp v] with x hFn hf hT
  rw [hFn, hf, hT]
  change 𝓕 ((ContinuousLinearMap.toSpanSingleton ℂ (v x)).compLp f) =
    (ContinuousLinearMap.toSpanSingleton ℂ (v x)).compLp (𝓕 f)
  exact Fourier.fourier_compLp _ _

theorem nuclearFibreField_fourier_jointTensor_schwartz {N M q : ℕ}
    (f : 𝓢(Configuration M, ℂ)) (v : 𝓢(Configuration N, SpinAmplitudes N q)) :
    nuclearFibreField (𝓕 (jointTensor (f.toLp 2 volume) (v.toLp 2 volume))) =
      (Lp.fourierTransformₗᵢ (Configuration M) (SpinAmplitudes N q)).toContinuousLinearEquiv.toContinuousLinearMap.compLp
        (𝓕 (nuclearFibreField (jointTensor (f.toLp 2 volume) (v.toLp 2 volume)))) := by
  rw [fourier_jointTensor_schwartz, nuclearFibreField_jointTensor,
    nuclearFibreField_jointTensor, Fourier.fourier_compLp,
    nuclearFourier_blockScalarInsertion, SchwartzMap.toLp_fourier_eq,
    SchwartzMap.toLp_fourier_eq]

/-- Full Fourier in the opposite block order: electronic outer transform and nuclear target
transform. The target nuclear transform preserves each electronic-frequency fibre norm. -/
theorem nuclearFibreField_fourier {N M q : ℕ} (ψ : QuantumState N M q) :
    nuclearFibreField (𝓕 ψ) =
      (Lp.fourierTransformₗᵢ (Configuration M) (SpinAmplitudes N q)).toContinuousLinearEquiv.toContinuousLinearMap.compLp
        (𝓕 (nuclearFibreField ψ)) := by
  let C := (nuclearFibreEquiv N M q).toContinuousLinearEquiv.toContinuousLinearMap
  let F := (Lp.fourierTransformₗᵢ (QuantumConfiguration N M) (SpinAmplitudes N q)).toContinuousLinearEquiv.toContinuousLinearMap
  let Fn := (Lp.fourierTransformₗᵢ (Configuration M) (SpinAmplitudes N q)).toContinuousLinearEquiv.toContinuousLinearMap
  let Fe := (Lp.fourierTransformₗᵢ (Configuration N)
    (Lp (SpinAmplitudes N q) 2 (volume : Measure (Configuration M)))).toContinuousLinearEquiv.toContinuousLinearMap
  have hC (v : QuantumState N M q) : C v = nuclearFibreField v := rfl
  have heq : C.comp F = (Fn.compLpL 2 volume).comp (Fe.comp C) := by
    apply continuousLinearMap_ext_jointTensor_schwartz
    intro f v
    change C (𝓕 (jointTensor (f.toLp 2 volume) (v.toLp 2 volume))) =
      Fn.compLp (𝓕 (C (jointTensor (f.toLp 2 volume) (v.toLp 2 volume))))
    exact nuclearFibreField_fourier_jointTensor_schwartz f v
  have hψ := congrArg (fun T => T ψ) heq
  change C (𝓕 ψ) = Fn.compLp (𝓕 (C ψ)) at hψ
  rwa [hC, hC] at hψ

end LiebThirring.ThermoStability

end
