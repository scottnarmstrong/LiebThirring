/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.TFQuantum.DilationBasic
public import LiebThirring.Fourier.Covariance
/-! # Fourier covariance of normalized dilation

Normalized pullback at scale r transforms in Fourier space into normalized
pullback at reciprocal scale. The Schwartz integral identity extends to all
L² states by density and continuity. Proof: large-charge dilation.
-/

public section
open MeasureTheory
open scoped SchwartzMap FourierTransform ENNReal NNReal
namespace LiebThirring.Dilation
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[expose] noncomputable def spatialEquiv (r : ℝ) (hr : 0 < r) : V ≃L[ℝ] V :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 r hr.ne')

@[expose] noncomputable def schwartz (r : ℝ) (hr : 0 < r) (f : 𝓢(V,H)) : 𝓢(V,H) :=
  (amplitude V r : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (spatialEquiv r hr) f

omit [MeasurableSpace V] [BorelSpace V] [CompleteSpace H] in
@[simp] theorem schwartz_apply (r : ℝ) (hr : 0 < r) (f : 𝓢(V,H)) (x : V) :
    schwartz r hr f x = (amplitude V r : ℂ) • f (r • x) := rfl

omit [CompleteSpace H] in
theorem applyL2_toLp (r : ℝ) (hr : 0 < r) (f : 𝓢(V,H)) :
    applyL2 r hr (f.toLp 2 volume) = (schwartz r hr f).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [coeFn_applyL2 r hr (f.toLp 2 (volume : Measure V)),
    (Measure.quasiMeasurePreserving_smul volume hr.ne').ae (f.coeFn_toLp 2 volume),
    (schwartz r hr f).coeFn_toLp 2 volume] with x hx hf hg
  rw [hx, hf, hg, schwartz_apply]

omit [MeasurableSpace V] [BorelSpace V] in
theorem amplitude_mul_inv_pow (r : ℝ) (hr : 0 < r) :
    amplitude V r * (r^Module.finrank ℝ V)⁻¹ = (amplitude V r)⁻¹ := by
  rw [← amplitude_sq r hr, pow_two, mul_inv_rev, ← mul_assoc,
    mul_inv_cancel₀ (amplitude_pos (V := V) r hr).ne', one_mul]

omit [CompleteSpace H] in
theorem fourier_schwartz (r : ℝ) (hr : 0 < r) (f : 𝓢(V,H)) :
    𝓕 (schwartz r hr f) = schwartz r⁻¹ (inv_pos.mpr hr) (𝓕 f) := by
  ext ξ
  change 𝓕 (fun x : V => (amplitude V r : ℂ) • f (r • x)) ξ =
    (amplitude V r⁻¹ : ℂ) • 𝓕 (fun x : V => f x) (r⁻¹ • ξ)
  let g : V → H := fun x => Real.fourierChar (-inner ℝ x (r⁻¹ • ξ)) • f x
  have hi (x : V) : inner ℝ (r • x) (r⁻¹ • ξ) = inner ℝ x ξ := by
    simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  calc
    _ = (amplitude V r : ℂ) • ∫ x, g (r • x) := by
      rw [Real.fourier_eq, ← integral_smul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only [g]
        rw [hi, smul_comm])
    _ = (amplitude V r : ℂ) • ((r^Module.finrank ℝ V)⁻¹ • ∫ x, g x) := by
      rw [Measure.integral_comp_smul_of_nonneg volume g r (hR := hr.le)]
    _ = _ := by
      have hs (a : ℝ) (v : H) : (a : ℂ) • v = a • v := by
        simpa only [Complex.coe_algebraMap] using algebraMap_smul ℂ a v
      simp only [hs]
      rw [smul_smul, amplitude_mul_inv_pow r hr, ← amplitude_inv]
      rfl

theorem fourier_applyL2 (r : ℝ) (hr : 0 < r) (ψ : Lp H 2 (volume : Measure V)) :
    𝓕 (applyL2 r hr ψ) = applyL2 r⁻¹ (inv_pos.mpr hr) (𝓕 ψ) := by
  apply DenseRange.induction_on
    (p := fun ψ : Lp H 2 (volume : Measure V) =>
      𝓕 (applyL2 r hr ψ) = applyL2 r⁻¹ (inv_pos.mpr hr) (𝓕 ψ))
    (SchwartzMap.denseRange_toLpCLM (E := V) (F := H) (p := 2)
      (μ := (volume : Measure V)) ENNReal.ofNat_ne_top) ψ
  · have hc : Continuous (applyL2 r hr : Lp H 2 (volume : Measure V) → Lp H 2 volume) :=
      (linearIsometry r hr).continuous
    have hi : Continuous (applyL2 r⁻¹ (inv_pos.mpr hr) :
        Lp H 2 (volume : Measure V) → Lp H 2 volume) :=
      (linearIsometry r⁻¹ (inv_pos.mpr hr)).continuous
    exact isClosed_eq ((Lp.fourierTransformₗᵢ V H).continuous.comp hc)
      (hi.comp (Lp.fourierTransformₗᵢ V H).continuous)
  · intro f
    change 𝓕 (applyL2 r hr (f.toLp 2 volume)) =
      applyL2 r⁻¹ (inv_pos.mpr hr) (𝓕 (f.toLp 2 volume))
    rw [applyL2_toLp, SchwartzMap.toLp_fourier_eq, fourier_schwartz,
      SchwartzMap.toLp_fourier_eq, applyL2_toLp]
end LiebThirring.Dilation
end
