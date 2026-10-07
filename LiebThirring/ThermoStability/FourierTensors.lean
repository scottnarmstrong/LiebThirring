/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoStability.Tensors
public import LiebThirring.Fourier.Functoriality
import LiebThirring.Fourier.IntegralL2

/-! # Joint Fourier transform on the separated tensor core -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap FourierTransform

namespace LiebThirring.ThermoStability

/-- The pointwise representative of a separated nuclear/electron tensor. -/
@[expose] noncomputable def rawJointTensor {N M q : ℕ}
    (f : Configuration M → ℂ) (v : Configuration N → SpinAmplitudes N q)
    (X : QuantumConfiguration N M) : SpinAmplitudes N q := f X.snd • v X.fst

theorem integrable_rawJointTensor {N M q : ℕ}
    {f : Configuration M → ℂ} {v : Configuration N → SpinAmplitudes N q}
    (hf : Integrable f) (hv : Integrable v) : Integrable (rawJointTensor f v) := by
  have h := hf.smul_prod hv
  exact ((measurePreserving_nuclearFirstEquiv N M).symm.integrable_comp
    h.aestronglyMeasurable).mpr h

theorem fourier_rawJointTensor {N M q : ℕ}
    {f : Configuration M → ℂ} {v : Configuration N → SpinAmplitudes N q}
    (ξ : Configuration N) (η : Configuration M) :
    (𝓕 (rawJointTensor f v)) (toLp 2 (ξ, η)) =
      (𝓕 f) η • (𝓕 v) ξ := by
  rw [Real.fourier_eq]
  rw [← (measurePreserving_nuclearFirstEquiv N M).integral_comp
    (nuclearFirstEquiv N M).measurableEmbedding]
  have heq : (fun a : Configuration M × Configuration N =>
      Real.fourierChar (-inner ℝ (nuclearFirstEquiv N M a) (toLp 2 (ξ, η))) •
        rawJointTensor f v (nuclearFirstEquiv N M a)) =
      (fun a : Configuration M × Configuration N =>
        (Real.fourierChar (-inner ℝ a.1 η) • f a.1) •
          (Real.fourierChar (-inner ℝ a.2 ξ) • v a.2)) := by
    funext a
    change Real.fourierChar (-inner ℝ (toLp 2 (a.2, a.1)) (toLp 2 (ξ, η))) •
      (f a.1 • v a.2) =
        (Real.fourierChar (-inner ℝ a.1 η) • f a.1) •
          (Real.fourierChar (-inner ℝ a.2 ξ) • v a.2)
    rw [WithLp.prod_inner_apply]
    simp only [neg_add, Real.fourierChar.map_add_eq_mul, Circle.smul_def,
      Circle.coe_mul, smul_smul, smul_eq_mul]
    congr 1
    ring
  rw [heq]
  exact integral_prod_smul (𝕜 := ℂ)
    (μ := (volume : Measure (Configuration M)))
    (ν := (volume : Measure (Configuration N)))
    (fun R => Real.fourierChar (-inner ℝ R η) • f R)
    (fun x => Real.fourierChar (-inner ℝ x ξ) • v x)

theorem jointTensor_schwartz_ae {N M q : ℕ}
    (f : 𝓢(Configuration M, ℂ)) (v : 𝓢(Configuration N, SpinAmplitudes N q)) :
    (jointTensor (f.toLp 2 volume) (v.toLp 2 volume) :
      QuantumConfiguration N M → SpinAmplitudes N q) =ᵐ[volume] rawJointTensor f v := by
  have hprod : ∀ᵐ a : Configuration M × Configuration N,
      jointTensor (f.toLp 2 volume) (v.toLp 2 volume) (nuclearFirstEquiv N M a) =
        rawJointTensor f v (nuclearFirstEquiv N M a) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      ((Lp.stronglyMeasurable _).measurable.comp (nuclearFirstEquiv N M).measurable)
      ((f.continuous.stronglyMeasurable.comp_measurable measurable_fst).smul
        (v.continuous.stronglyMeasurable.comp_measurable measurable_snd)).measurable)).mpr
    filter_upwards [jointTensor_ae (f.toLp 2 volume) (v.toLp 2 volume),
      f.coeFn_toLp 2 volume] with R hR hf
    filter_upwards [hR, v.coeFn_toLp 2 volume] with x hx hv
    change jointTensor (f.toLp 2 volume) (v.toLp 2 volume) (toLp 2 (x, R)) = f R • v x
    rw [hx, hf, hv]
  have h := (measurePreserving_nuclearFirstEquiv N M).symm.quasiMeasurePreserving.ae hprod
  filter_upwards [h] with X hX
  simpa only [MeasurableEquiv.apply_symm_apply] using hX

theorem fourier_jointTensor_schwartz {N M q : ℕ}
    (f : 𝓢(Configuration M, ℂ)) (v : 𝓢(Configuration N, SpinAmplitudes N q)) :
    𝓕 (jointTensor (f.toLp 2 volume) (v.toLp 2 volume)) =
      jointTensor ((𝓕 f).toLp 2 volume) ((𝓕 v).toLp 2 volume) := by
  let ψ := jointTensor (f.toLp 2 volume) (v.toLp 2 volume)
  have hψ := jointTensor_schwartz_ae f v
  have hm : MemLp (rawJointTensor f v) 2 volume := (Lp.memLp ψ).ae_eq hψ
  have hc : hm.toLp (rawJointTensor f v) = ψ := by
    apply Lp.ext
    exact hm.coeFn_toLp.trans hψ.symm
  have hF := Fourier.fourier_toLp_ae_eq
    (integrable_rawJointTensor (f.integrable (μ := volume)) (v.integrable (μ := volume))) hm
  rw [hc] at hF
  apply Lp.ext
  have hraw : (𝓕 (rawJointTensor f v) : QuantumConfiguration N M → SpinAmplitudes N q)
      =ᵐ[volume] rawJointTensor (𝓕 f : 𝓢(Configuration M, ℂ))
        (𝓕 v : 𝓢(Configuration N, SpinAmplitudes N q)) := by
    filter_upwards with X
    exact fourier_rawJointTensor X.fst X.snd
  exact hF.trans (hraw.trans (jointTensor_schwartz_ae (𝓕 f) (𝓕 v)).symm)

end LiebThirring.ThermoStability

end
