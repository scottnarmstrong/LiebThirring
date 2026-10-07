/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.Fourier.Covariance
public import LiebThirring.ThermoClusters.StateMotion
/-!
# Fourier covariance of rigid joint-state transport

Translation contributes a unit complex Fourier phase for every Hilbert-valued
L² function. The proof uses Schwartz density and continuous L∞ multiplication.
Combining translation with the existing orthogonal covariance theorem gives
the exact Fourier magnitude of a transported correlated quantum state.

Proof: rigid-motion and domain-inclusion identities (joint coordinate change).
-/

public section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap RealInnerProductSpace
namespace LiebThirring.Fourier
variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem phase_memLp (b : V) :
    MemLp (fun x : V => (Real.fourierChar ⟪b,x⟫ : ℂ)) ⊤ (volume : Measure V) := by
  apply memLp_top_of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall (fun _ => (Circle.norm_coe _).le)

private noncomputable def phaseLp (b : V) : Lp ℂ ⊤ (volume : Measure V) :=
  (phase_memLp b).toLp (fun x => (Real.fourierChar ⟪b,x⟫ : ℂ))

private theorem phaseLp_ae (b : V) :
    ⇑(phaseLp b) =ᵐ[volume] fun x : V => (Real.fourierChar ⟪b,x⟫ : ℂ) :=
  MemLp.coeFn_toLp _

private noncomputable def phaseMulLM (b : V) :
    Lp H 2 (volume : Measure V) →ₗ[ℂ] Lp H 2 (volume : Measure V) where
  toFun f := phaseLp b • f
  map_add' f g := Lp.add_smul (phaseLp b) f g
  map_smul' c f := (Lp.smul_comm c (phaseLp b) f).symm

omit [CompleteSpace H] in
private theorem phaseMul_ae (b : V) (f : Lp H 2 (volume : Measure V)) :
    ⇑(phaseMulLM b f) =ᵐ[volume] fun x => Real.fourierChar ⟪b,x⟫ • f x := by
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (phaseLp b) f, phaseLp_ae b] with x hx hb
  change (phaseLp b • f : Lp H 2 (volume : Measure V)) x = _
  rw [hx]
  change (phaseLp b x) • f x = _
  rw [hb]
  rfl

private noncomputable def phaseMulCLM (b : V) :
    Lp H 2 (volume : Measure V) →L[ℂ] Lp H 2 (volume : Measure V) :=
  (phaseMulLM b).mkContinuous 1 (fun f => by
    rw [one_mul]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [phaseMul_ae b f] with x hx
    rw [hx, Circle.norm_smul])

omit [CompleteSpace H] in
private theorem phaseMulCLM_ae (b : V) (f : Lp H 2 (volume : Measure V)) :
    ⇑(phaseMulCLM b f) =ᵐ[volume] fun x => Real.fourierChar ⟪b,x⟫ • f x :=
  phaseMul_ae b f

omit [CompleteSpace H] in
private theorem translate_toLp (b : V) (f : 𝓢(V,H)) :
    Lp.compMeasurePreserving (fun x => x+b) (measurePreserving_add_right volume b)
      (f.toLp 2 volume) = (f.compSubConstCLM ℂ (-b)).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (f.toLp 2 volume)
      (measurePreserving_add_right volume b),
    (measurePreserving_add_right volume b).quasiMeasurePreserving.ae (f.coeFn_toLp 2 volume),
    (f.compSubConstCLM ℂ (-b)).coeFn_toLp 2 volume] with x hx hf hg
  rw [hx, hg]
  simpa only [Function.comp_apply, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add] using hf

omit [CompleteSpace H] in
private theorem fourier_translate_schwartz (b : V) (f : 𝓢(V,H)) (x : V) :
    (𝓕 (f.compSubConstCLM ℂ (-b))) x = Real.fourierChar ⟪b,x⟫ • (𝓕 f) x := by
  change 𝓕 (fun y => f (y- -b)) x = _
  simp only [sub_neg_eq_add]
  exact congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure V) (innerₗ V) (fun y => f y) b) x

private theorem fourier_translate (b : V) (f : Lp H 2 (volume : Measure V)) :
    𝓕 (Lp.compMeasurePreserving (fun x => x+b) (measurePreserving_add_right volume b) f) =
      phaseMulCLM b (𝓕 f) := by
  apply DenseRange.induction_on (p := fun f : Lp H 2 (volume : Measure V) =>
    𝓕 (Lp.compMeasurePreserving (fun x => x+b) (measurePreserving_add_right volume b) f) =
      phaseMulCLM b (𝓕 f))
    (SchwartzMap.denseRange_toLpCLM (E := V) (F := H) (p := 2)
      (μ := (volume : Measure V)) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq
      ((Lp.fourierTransformₗᵢ V H).continuous.comp
        (Lp.compMeasurePreservingₗᵢ ℂ (fun x => x+b) (measurePreserving_add_right volume b)).continuous)
      ((phaseMulCLM b).continuous.comp (Lp.fourierTransformₗᵢ V H).continuous)
  · intro g
    change 𝓕 (Lp.compMeasurePreserving (fun x => x+b) (measurePreserving_add_right volume b)
      (g.toLp 2 volume)) = phaseMulCLM b (𝓕 (g.toLp 2 volume))
    rw [translate_toLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
    apply Lp.ext
    filter_upwards [(𝓕 (g.compSubConstCLM ℂ (-b))).coeFn_toLp 2 volume,
      phaseMulCLM_ae b ((𝓕 g).toLp 2 volume), (𝓕 g).coeFn_toLp 2 volume] with x hx hp hg
    rw [hx, hp, hg]
    exact fourier_translate_schwartz b g x

/-- Translation affects an arbitrary L² Fourier transform only by a unit complex phase. -/
theorem fourier_comp_add_right_ae (b : V) (f : Lp H 2 (volume : Measure V)) :
    ∀ᵐ x ∂(volume : Measure V),
      (𝓕 (Lp.compMeasurePreserving (fun y => y+b) (measurePreserving_add_right volume b) f)) x =
        Real.fourierChar ⟪b,x⟫ • (𝓕 f) x := by
  rw [fourier_translate]
  exact phaseMulCLM_ae b (𝓕 f)

/-- Translation preserves the pointwise Fourier magnitude almost everywhere. -/
theorem nnnorm_fourier_comp_add_right_ae (b : V) (f : Lp H 2 (volume : Measure V)) :
    ∀ᵐ x ∂(volume : Measure V),
      ‖(𝓕 (Lp.compMeasurePreserving (fun y => y+b) (measurePreserving_add_right volume b) f)) x‖₊ =
        ‖(𝓕 f) x‖₊ := by
  filter_upwards [fourier_comp_add_right_ae b f] with x hx
  apply NNReal.eq
  change ‖_‖ = ‖_‖
  rw [hx, Circle.norm_smul]

end LiebThirring.Fourier

namespace LiebThirring

private theorem quantumStateMotion_eq_translation_rotation {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumState N M q) :
    quantumStateMotion Q c ψ =
      Lp.compMeasurePreserving (fun X => X + -quantumShift N M c)
        (measurePreserving_add_right volume (-quantumShift N M c))
        (Lp.compMeasurePreserving (quantumRotation Q).symm
          (quantumRotation Q).symm.measurePreserving ψ) := by
  change Lp.compMeasurePreserving (quantumRigidMotion Q c).symm _ ψ = _
  have hmap : ((quantumRigidMotion (N := N) (M := M) Q c).symm :
      QuantumConfiguration N M → QuantumConfiguration N M) =
      (quantumRotation Q).symm ∘ (fun X => X + -quantumShift N M c) := by
    funext X
    rw [quantumRigidMotion_symm_apply, sub_eq_add_neg]
    rfl
  simpa only [← hmap] using
    Lp.compMeasurePreserving_comp_apply ψ (quantumRotation Q).symm.measurePreserving
      (measurePreserving_add_right volume (-quantumShift N M c))

/-- Spatial rigid transport preserves Fourier magnitudes up to the inverse rotation
of the frequency variable. Translation contributes only a unit complex phase. -/
theorem nnnorm_fourier_quantumStateMotion_ae {N M q : ℕ}
    (Q : Position ≃ₗᵢ[ℝ] Position) (c : Position) (ψ : QuantumState N M q) :
    ∀ᵐ ξ ∂(volume : Measure (QuantumConfiguration N M)),
      ‖(𝓕 (quantumStateMotion Q c ψ)) ξ‖₊ =
        ‖(𝓕 ψ) ((quantumRotation Q).symm ξ)‖₊ := by
  rw [quantumStateMotion_eq_translation_rotation]
  have hnorm := Fourier.nnnorm_fourier_comp_add_right_ae (-quantumShift N M c)
    (Lp.compMeasurePreserving (quantumRotation Q).symm
      (quantumRotation Q).symm.measurePreserving ψ)
  rw [Fourier.fourier_compMeasurePreserving] at hnorm
  filter_upwards [hnorm, Lp.coeFn_compMeasurePreserving (𝓕 ψ)
    (quantumRotation Q).symm.measurePreserving] with ξ hξ hψ
  rw [hξ, hψ]
  rfl

end LiebThirring
end
