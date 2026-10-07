/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormPolarization
import LiebThirring.Variational.FormIntegralBounds

/-! # Graph-norm bounds and coercivity of the Coulomb form

form continuity: all constants depend only on the fixed nuclear data and particle number.
The graph size is the literal square root of mass plus finite Fourier energy.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring
open Assembly

/-- The literal Fourier form graph norm. -/
@[expose] noncomputable def formGraphNorm {N q : ℕ} (ψ : FormDomain N q) : ℝ :=
  Real.sqrt (‖(ψ : State N q)‖ ^ 2 + (kineticEnergy (ψ : State N q)).toReal)

/-- Nonnegativity of the form graph norm. -/
theorem formGraphNorm_nonneg {N q : ℕ} (ψ : FormDomain N q) : 0 ≤ formGraphNorm ψ :=
  Real.sqrt_nonneg _

/-- Squaring the graph norm recovers exactly mass plus kinetic energy. -/
theorem formGraphNorm_sq {N q : ℕ} (ψ : FormDomain N q) :
    formGraphNorm ψ ^ 2 = ‖(ψ : State N q)‖ ^ 2 + (kineticEnergy (ψ : State N q)).toReal :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)

/-- The L² mass is controlled by the form graph norm. -/
theorem norm_state_le_formGraphNorm {N q : ℕ} (ψ : FormDomain N q) :
    ‖(ψ : State N q)‖ ≤ formGraphNorm ψ := by
  unfold formGraphNorm
  rw [Real.le_sqrt (norm_nonneg _) (add_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)]
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

/-- A quadratic upper bound gives the corresponding weighted pairing bound. -/
theorem sqrt_mul_sqrt_le_of_le_mul {x y C a b : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hx : x ≤ C * a ^ 2) (hy : y ≤ C * b ^ 2) :
    Real.sqrt x * Real.sqrt y ≤ C * a * b := by
  calc
    _ ≤ Real.sqrt (C * a ^ 2) * Real.sqrt (C * b ^ 2) :=
      mul_le_mul (Real.sqrt_le_sqrt hx) (Real.sqrt_le_sqrt hy)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul hC, Real.sqrt_mul hC, Real.sqrt_sq ha, Real.sqrt_sq hb]
      calc
        _ = Real.sqrt C ^ 2 * a * b := by ring
        _ = _ := by rw [Real.sq_sqrt hC]

/-- The repulsion expectation is bounded by a fixed multiple of graph norm squared. -/
theorem repulsion_le_formGraphNorm_sq {N q : ℕ} (ψ : FormDomain N q) :
    (∫⁻ X : Configuration N, electronRepulsion X * (‖(ψ : State N q) X‖₊ : ℝ≥0∞) ^ 2).toReal ≤
      (1 + (N.choose 2 : ℝ) ^ 2) * formGraphNorm ψ ^ 2 := by
  have h := lintegral_electronRepulsion_toReal_le (ψ : State N q) ψ.property.2
    (δ := 1) (by norm_num)
  rw [formGraphNorm_sq]
  simp only [one_mul, div_one] at h
  nlinarith only [h, sq_nonneg ‖(ψ : State N q)‖,
    (mul_nonneg (sq_nonneg (N.choose 2 : ℝ))
      (ENNReal.toReal_nonneg : 0 ≤ (kineticEnergy (ψ : State N q)).toReal))]

/-- The attraction expectation is bounded by a fixed multiple of graph norm squared. -/
theorem attraction_le_formGraphNorm_sq {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ψ : FormDomain N q) :
    (∫⁻ X : Configuration N, attraction z R X * (‖(ψ : State N q) X‖₊ : ℝ≥0∞) ^ 2).toReal ≤
      (1 + (N : ℝ) * (∑ k : Fin M, (z k : ℝ)) ^ 2) * formGraphNorm ψ ^ 2 := by
  have h := lintegral_attraction_toReal_le z R (ψ : State N q) ψ.property.2
    (δ := 1) (by norm_num)
  rw [formGraphNorm_sq]
  simp only [one_mul, div_one] at h
  have hc : 0 ≤ (N : ℝ) * (∑ k : Fin M, (z k : ℝ)) ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  nlinarith only [h, sq_nonneg ‖(ψ : State N q)‖,
    (mul_nonneg hc (ENNReal.toReal_nonneg : 0 ≤ (kineticEnergy (ψ : State N q)).toReal))]

/-- A concrete fixed bound for the entire literal Hermitian form. -/
theorem norm_energyForm_le {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (φ ψ : FormDomain N q) :
    ‖energyForm z R hR φ ψ‖ ≤
      (3 + (N.choose 2 : ℝ) ^ 2 + (N : ℝ) * (∑ k : Fin M, (z k : ℝ)) ^ 2 +
        (nuclearRepulsion z R).toReal) * formGraphNorm φ * formGraphNorm ψ := by
  have hkφ : (kineticEnergy (φ : State N q)).toReal ≤ formGraphNorm φ ^ 2 := by
    rw [formGraphNorm_sq]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hkψ : (kineticEnergy (ψ : State N q)).toReal ≤ formGraphNorm ψ ^ 2 := by
    rw [formGraphNorm_sq]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hp : Measurable (fun ξ : Configuration N =>
      ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2) :=
    measurable_const.mul (measurable_id.nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hk := norm_integral_weight_inner_le hp.aemeasurable
    (Lp.aestronglyMeasurable (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)
      (φ : State N q)))
    (Lp.aestronglyMeasurable (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)
      (ψ : State N q))) φ.property.2 ψ.property.2
  simp only [formKineticWeight_toReal] at hk
  have hk' := hk.trans (sqrt_mul_sqrt_le_of_le_mul (C := 1) (by norm_num)
    (formGraphNorm_nonneg φ) (formGraphNorm_nonneg ψ)
    (by simpa only [one_mul, kineticEnergy, mul_assoc] using hkφ)
    (by simpa only [one_mul, kineticEnergy, mul_assoc] using hkψ))
  simp only [one_mul] at hk'
  have hr := norm_integral_weight_inner_le measurable_electronRepulsion.aemeasurable
    (Lp.aestronglyMeasurable (φ : State N q)) (Lp.aestronglyMeasurable (ψ : State N q))
    (lintegral_electronRepulsion_lt_top (φ : State N q) φ.property.2)
    (lintegral_electronRepulsion_lt_top (ψ : State N q) ψ.property.2)
  have hr' := hr.trans (sqrt_mul_sqrt_le_of_le_mul (by positivity)
    (formGraphNorm_nonneg φ) (formGraphNorm_nonneg ψ)
    (repulsion_le_formGraphNorm_sq φ) (repulsion_le_formGraphNorm_sq ψ))
  have ha := norm_integral_weight_inner_le (measurable_attraction z R).aemeasurable
    (Lp.aestronglyMeasurable (φ : State N q)) (Lp.aestronglyMeasurable (ψ : State N q))
    (lintegral_attraction_lt_top z R (φ : State N q) φ.property.2)
    (lintegral_attraction_lt_top z R (ψ : State N q) ψ.property.2)
  have ha' := ha.trans (sqrt_mul_sqrt_le_of_le_mul (by positivity)
    (formGraphNorm_nonneg φ) (formGraphNorm_nonneg ψ)
    (attraction_le_formGraphNorm_sq z R φ) (attraction_le_formGraphNorm_sq z R ψ))
  have hn : ‖((nuclearRepulsion z R).toReal : ℂ) * inner ℂ (φ : State N q) (ψ : State N q)‖ ≤
      (nuclearRepulsion z R).toReal * formGraphNorm φ * formGraphNorm ψ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    apply (mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) ENNReal.toReal_nonneg).trans
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (norm_state_le_formGraphNorm φ) (norm_state_le_formGraphNorm ψ)
        (norm_nonneg _) (formGraphNorm_nonneg _)) ENNReal.toReal_nonneg
  unfold energyForm
  simp_rw [Complex.ofReal_sub, sub_mul]
  rw [integral_sub (integrable_energyForm_repulsion φ ψ)
    (integrable_energyForm_attraction z R φ ψ)]
  apply (norm_add_le _ _).trans
  apply (add_le_add ((norm_add_le _ _).trans
    (add_le_add hk' ((norm_sub_le _ _).trans (add_le_add hr' ha')))) hn).trans_eq
  ring

/-- Molecular coercivity, retaining the nonnegative repulsion and nuclear terms. -/
theorem realEnergy_coercive {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (ψ : FormDomain N q) :
    (kineticEnergy (ψ : State N q)).toReal / 2 -
      2 * (N : ℝ) * (∑ k : Fin M, (z k : ℝ)) ^ 2 * ‖(ψ : State N q)‖ ^ 2 ≤
        realEnergy z R hR ψ := by
  have h := lintegral_attraction_toReal_le z R (ψ : State N q) ψ.property.2
    (δ := 1 / 2) (by norm_num)
  unfold realEnergy
  have hr : 0 ≤ (∫⁻ X : Configuration N,
      electronRepulsion X * (‖(ψ : State N q) X‖₊ : ℝ≥0∞) ^ 2).toReal := ENNReal.toReal_nonneg
  have hn := mul_nonneg (ENNReal.toReal_nonneg : 0 ≤ (nuclearRepulsion z R).toReal)
    (sq_nonneg ‖(ψ : State N q)‖)
  linarith only [h, hr, hn]

/-- The standard positive shift dominates half the graph norm squared. -/
theorem realEnergy_shift_ge {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (ψ : FormDomain N q) :
    formGraphNorm ψ ^ 2 / 2 ≤ realEnergy z R hR ψ +
      (2 * (N : ℝ) * (∑ k : Fin M, (z k : ℝ)) ^ 2 + 1) * ‖(ψ : State N q)‖ ^ 2 := by
  rw [formGraphNorm_sq]
  linarith only [realEnergy_coercive z R hR ψ, sq_nonneg ‖(ψ : State N q)‖]

end LiebThirring
end
