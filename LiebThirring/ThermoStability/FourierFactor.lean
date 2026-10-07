/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoStability.FourierTensors
public import LiebThirring.ThermoStability.BlockCurrying

/-! # Full joint Fourier factorization on electronic fibres -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap FourierTransform

namespace LiebThirring.ThermoStability

/-- Insert a fixed electronic state, continuously in its nuclear amplitude. -/
@[expose] noncomputable def jointTensorLeft {N M q : ℕ} (v : State N q) :
    Lp ℂ 2 (volume : Measure (Configuration M)) →L[ℂ] QuantumState N M q :=
  (electronFibreEquiv N M q).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((stateScalarMap v).compLpL 2 volume)

/-- Insert a fixed nuclear amplitude, continuously in its electronic state. -/
@[expose] noncomputable def jointTensorRight {N M q : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Configuration M))) : State N q →L[ℂ] QuantumState N M q :=
  (electronFibreEquiv N M q).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (blockScalarInsertion f)

theorem continuousLinearMap_ext_jointTensor_schwartz {N M q : ℕ} {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (A B : QuantumState N M q →L[ℂ] K)
    (h : ∀ (f : 𝓢(Configuration M, ℂ)) (v : 𝓢(Configuration N, SpinAmplitudes N q)),
      A (jointTensor (f.toLp 2 volume) (v.toLp 2 volume)) =
        B (jointTensor (f.toLp 2 volume) (v.toLp 2 volume))) : A = B := by
  apply continuousLinearMap_ext_jointTensor
  intro f v
  apply DenseRange.induction_on
    (p := fun v : State N q => A (jointTensor f v) = B (jointTensor f v))
    (SchwartzMap.denseRange_toLpCLM (E := Configuration N) (F := SpinAmplitudes N q)
      (p := 2) (μ := (volume : Measure (Configuration N))) ENNReal.ofNat_ne_top) v
  · exact isClosed_eq (A.continuous.comp (jointTensorRight f).continuous)
      (B.continuous.comp (jointTensorRight f).continuous)
  · intro w
    apply DenseRange.induction_on
      (p := fun f : Lp ℂ 2 (volume : Measure (Configuration M)) =>
        A (jointTensor f (w.toLp 2 volume)) = B (jointTensor f (w.toLp 2 volume)))
      (SchwartzMap.denseRange_toLpCLM (E := Configuration M) (F := ℂ)
        (p := 2) (μ := (volume : Measure (Configuration M))) ENNReal.ofNat_ne_top) f
    · exact isClosed_eq (A.continuous.comp (jointTensorLeft (w.toLp 2 volume)).continuous)
        (B.continuous.comp (jointTensorLeft (w.toLp 2 volume)).continuous)
    · intro g
      exact h g w

/-- Full joint Fourier is inner electronic Fourier followed by outer nuclear Fourier. -/
theorem electronFibreField_fourier {N M q : ℕ} (ψ : QuantumState N M q) :
    electronFibreField (𝓕 ψ) =
      𝓕 ((Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)).toContinuousLinearEquiv.toContinuousLinearMap.compLp
        (electronFibreField ψ)) := by
  let C := (electronFibreEquiv N M q).toContinuousLinearEquiv.toContinuousLinearMap
  let F := (Lp.fourierTransformₗᵢ (QuantumConfiguration N M) (SpinAmplitudes N q)).toContinuousLinearEquiv.toContinuousLinearMap
  let Fe := (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)).toContinuousLinearEquiv.toContinuousLinearMap
  let Fn := (Lp.fourierTransformₗᵢ (Configuration M) (State N q)).toContinuousLinearEquiv.toContinuousLinearMap
  have heq : C.comp F = Fn.comp ((Fe.compLpL 2 volume).comp C) := by
    apply continuousLinearMap_ext_jointTensor_schwartz
    intro f v
    change electronFibreField (𝓕 (jointTensor (f.toLp 2 volume) (v.toLp 2 volume))) =
      𝓕 (Fe.compLp (electronFibreField (jointTensor (f.toLp 2 volume) (v.toLp 2 volume))))
    rw [fourier_jointTensor_schwartz, electronFibreField_jointTensor, electronFibreField_jointTensor]
    have ht : Fe.compLp ((stateScalarMap (v.toLp 2 volume)).compLp (f.toLp 2 volume)) =
        (stateScalarMap (𝓕 (v.toLp 2 volume))).compLp (f.toLp 2 volume) := by
      apply Lp.ext
      filter_upwards [Fe.coeFn_compLp ((stateScalarMap (v.toLp 2 volume)).compLp (f.toLp 2 volume)),
        (stateScalarMap (v.toLp 2 volume)).coeFn_compLp (f.toLp 2 volume),
        (stateScalarMap (𝓕 (v.toLp 2 volume))).coeFn_compLp (f.toLp 2 volume)] with R hR hv hT
      rw [hR, hv, hT]
      exact map_smul Fe _ _
    rw [ht, Fourier.fourier_compLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  exact congrArg (fun T => T ψ) heq

end LiebThirring.ThermoStability

end
