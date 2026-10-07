/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormHardy
public import LiebThirring.Variational.FormIntegral
public import LiebThirring.Assembly.RealFormPairs

/-! # Selected-coordinate Hardy estimates with variable poles

Hardy estimates: full-spin slicing permits a pole depending on the spectator coordinates.
-/

public section
open MeasureTheory WithLp
open scoped ENNReal NNReal FourierTransform
namespace LiebThirring
open Assembly

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

/-- Disintegration of a Coulomb power with a spectator-dependent pole. -/
theorem lintegral_particle_coulomb_pow_eq_slices {N q : ℕ} (i : Fin N)
    (c : OtherConfiguration i → Position) (hc : Measurable c) (n : ℕ) (ψ : State N q) :
    (∫⁻ X : Configuration N,
      coulombKernel (particlePosition X i) (c (((insertionMeasurableEquiv i).symm X).2)) ^ n *
        (‖ψ X‖₊ : ℝ≥0∞) ^ 2) =
    ∫⁻ y : OtherConfiguration i, ∫⁻ x : Position,
      coulombKernel x (c y) ^ n *
        (‖realFormSwapCurrying (realFormParticleCurrying i ψ) y x‖₊ : ℝ≥0∞) ^ 2 := by
  let F : Configuration N → ℝ≥0∞ := fun X =>
    coulombKernel (particlePosition X i) (c (((insertionMeasurableEquiv i).symm X).2)) ^ n *
      (‖ψ X‖₊ : ℝ≥0∞) ^ 2
  have hF : Measurable F :=
    ((measurable_coulombKernel.comp
      ((measurable_particlePosition i).prodMk (hc.comp (measurable_snd.comp (insertionMeasurableEquiv i).symm.measurable)))).pow_const n).mul
        (measurable_state_norm_sq ψ)
  have hI : Measurable (fun z : Position × OtherConfiguration i =>
      F (insertParticle i z.1 z.2)) :=
    hF.comp (measurePreserving_insertParticle i).measurable
  calc
    _ = ∫⁻ z : Position × OtherConfiguration i, F (insertParticle i z.1 z.2) :=
      ((measurePreserving_insertParticle i).lintegral_comp hF).symm
    _ = ∫⁻ y : OtherConfiguration i, ∫⁻ x : Position, F (insertParticle i x y) :=
      lintegral_prod_symm _ hI.aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [realFormParticleSlices_ae i ψ] with y hy
      apply lintegral_congr_ae
      filter_upwards [hy] with x hx
      simp only [F, particlePosition_insertParticle, hx]
      rw [← insertionMeasurableEquiv_apply i (x, y),
        MeasurableEquiv.symm_apply_apply]

/-- Inverse-square Hardy for a pole depending on the spectator coordinates. -/
theorem lintegral_particle_coulomb_sq_le {N q : ℕ} (i : Fin N)
    (c : OtherConfiguration i → Position) (hc : Measurable c) (ψ : State N q) :
    (∫⁻ X : Configuration N,
      coulombKernel (particlePosition X i) (c (((insertionMeasurableEquiv i).symm X).2)) ^ 2 *
        (‖ψ X‖₊ : ℝ≥0∞) ^ 2) ≤ 4 * particleFourierEnergy ψ i := by
  let u := realFormParticleCurrying i ψ
  let v := realFormSwapCurrying u
  let w : Position → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2
  have hw : Measurable w :=
    measurable_const.mul (measurable_id.nnnorm.coe_nnreal_ennreal.pow_const 2)
  have henergy : (∫⁻ y : OtherConfiguration i, ∫⁻ ξ : Position, w ξ *
      (‖(Lp.fourierTransformₗᵢ Position (SpinAmplitudes N q) (v y)) ξ‖₊ : ℝ≥0∞) ^ 2) =
      particleFourierEnergy ψ i :=
    (realFormSwapCurrying_fourier_weighted_norm_sq u w hw).trans
      (realFormParticleCurrying_fourier_energy i ψ)
  rw [lintegral_particle_coulomb_pow_eq_slices i c hc 2 ψ]
  calc
    _ ≤ ∫⁻ y : OtherConfiguration i, 4 * ∫⁻ ξ : Position, w ξ *
          (‖(Lp.fourierTransformₗᵢ Position (SpinAmplitudes N q) (v y)) ξ‖₊ : ℝ≥0∞) ^ 2 :=
      lintegral_mono (fun y => lintegral_coulomb_sq_le_of_fourier (c y) (v y))
    _ = _ := by
      rw [lintegral_const_mul' 4 _ (by norm_num), henergy]


/-- Inverse-square Hardy at a fixed nuclear pole. -/
theorem lintegral_nucleus_coulomb_sq_le {N q : ℕ} (i : Fin N)
    (c : Position) (ψ : State N q) :
    (∫⁻ X : Configuration N, coulombKernel (particlePosition X i) c ^ 2 *
      (‖ψ X‖₊ : ℝ≥0∞) ^ 2) ≤ 4 * particleFourierEnergy ψ i :=
  lintegral_particle_coulomb_sq_le i (fun _ => c) measurable_const ψ

/-- The spectator pole for an electron pair is exactly the other position. -/
theorem particle_pair_pole_eq {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (X : Configuration N) :
    particlePosition (insertParticle i 0 ((insertionMeasurableEquiv i).symm X).2) j =
      particlePosition X j := by
  let y := (insertionMeasurableEquiv i).symm X
  have hy : insertParticle i y.1 y.2 = X :=
    (insertionMeasurableEquiv_apply i y).symm.trans
      ((insertionMeasurableEquiv i).apply_symm_apply X)
  exact (realForm_particlePosition_insert_ne i j hij y.1 y.2).symm.trans
    (congrArg (fun Y => particlePosition Y j) hy)

/-- Inverse-square Hardy at another electron, with no symmetry assumption. -/
theorem lintegral_pair_coulomb_sq_le {N q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : State N q) :
    (∫⁻ X : Configuration N,
      coulombKernel (particlePosition X i) (particlePosition X j) ^ 2 *
        (‖ψ X‖₊ : ℝ≥0∞) ^ 2) ≤ 4 * particleFourierEnergy ψ i := by
  have hm : Measurable (fun y : OtherConfiguration i =>
      particlePosition (insertParticle i 0 y) j) :=
    (measurable_particlePosition j).comp
      ((measurePreserving_insertParticle i).measurable.comp
        (measurable_const.prodMk measurable_id))
  have h := lintegral_particle_coulomb_sq_le i
    (fun y => particlePosition (insertParticle i 0 y) j) hm ψ
  simpa only [particle_pair_pole_eq i j hij] using h

/-- Cauchy–Schwarz turns a particle inverse-square bound into sharp Coulomb control. -/
theorem lintegral_coulomb_le_sqrt_of_sq_le {N q : ℕ} (i : Fin N)
    {p : Configuration N → ℝ≥0∞} (hp : Measurable p) (ψ : State N q)
    (hT : kineticEnergy ψ < ⊤)
    (hs : (∫⁻ X : Configuration N, p X ^ 2 * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) ≤
      4 * particleFourierEnergy ψ i) :
    (∫⁻ X : Configuration N, p X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) < ⊤ ∧
    (∫⁻ X : Configuration N, p X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2).toReal ≤
      2 * Real.sqrt (‖ψ‖ ^ 2 * (particleFourierEnergy ψ i).toReal) := by
  have hi := (realForm_particleFourierEnergy_le i ψ).trans_lt hT
  have h4 : 4 * particleFourierEnergy ψ i < ⊤ :=
    ENNReal.mul_lt_top (by norm_num) hi
  have hm : (∫⁻ X : Configuration N, (‖ψ X‖₊ : ℝ≥0∞) ^ 2) < ⊤ := by
    rw [lintegral_state_norm_sq]
    exact ENNReal.pow_lt_top ENNReal.coe_lt_top
  obtain ⟨hf, hb⟩ := lintegral_weight_first_le hp.aemeasurable
    (Lp.aestronglyMeasurable ψ) hm (hs.trans_lt h4)
  refine ⟨hf, ?_⟩
  rw [lintegral_state_norm_sq, ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm] at hb
  have hsr := ENNReal.toReal_mono h4.ne hs
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hsr
  calc
    _ ≤ Real.sqrt (‖ψ‖ ^ 2) * Real.sqrt
        (∫⁻ X : Configuration N, p X ^ 2 * (‖ψ X‖₊ : ℝ≥0∞) ^ 2).toReal := hb
    _ ≤ Real.sqrt (‖ψ‖ ^ 2) * Real.sqrt (4 * (particleFourierEnergy ψ i).toReal) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsr) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_mul (sq_nonneg ‖ψ‖)]
      rw [show Real.sqrt 4 = 2 by
        have h : (4 : ℝ) = 2 ^ 2 := by norm_num
        rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]
      ring

/-- Sharp first-power Coulomb estimate for each nucleus. -/
theorem lintegral_nucleus_coulomb_le_sqrt {N q : ℕ} (i : Fin N) (c : Position)
    (ψ : State N q) (hT : kineticEnergy ψ < ⊤) :
    (∫⁻ X : Configuration N, coulombKernel (particlePosition X i) c *
      (‖ψ X‖₊ : ℝ≥0∞) ^ 2) < ⊤ ∧
    (∫⁻ X : Configuration N, coulombKernel (particlePosition X i) c *
      (‖ψ X‖₊ : ℝ≥0∞) ^ 2).toReal ≤
        2 * Real.sqrt (‖ψ‖ ^ 2 * (particleFourierEnergy ψ i).toReal) :=
  lintegral_coulomb_le_sqrt_of_sq_le i
    (measurable_coulombKernel.comp ((measurable_particlePosition i).prodMk measurable_const))
    ψ hT (lintegral_nucleus_coulomb_sq_le i c ψ)

/-- Sharp first-power Coulomb estimate for each electron pair. -/
theorem lintegral_pair_coulomb_le_sqrt {N q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : State N q) (hT : kineticEnergy ψ < ⊤) :
    (∫⁻ X : Configuration N,
      coulombKernel (particlePosition X i) (particlePosition X j) *
        (‖ψ X‖₊ : ℝ≥0∞) ^ 2) < ⊤ ∧
    (∫⁻ X : Configuration N,
      coulombKernel (particlePosition X i) (particlePosition X j) *
        (‖ψ X‖₊ : ℝ≥0∞) ^ 2).toReal ≤
          2 * Real.sqrt (‖ψ‖ ^ 2 * (particleFourierEnergy ψ i).toReal) :=
  lintegral_coulomb_le_sqrt_of_sq_le i
    (measurable_coulombKernel.comp
      ((measurable_particlePosition i).prodMk (measurable_particlePosition j)))
    ψ hT (lintegral_pair_coulomb_sq_le i j hij ψ)

end LiebThirring
end
