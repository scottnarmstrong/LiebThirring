/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.WeightedContinuity

/-! # Convergence of the joint kinetic expectations

Argument thermodynamic confined form estimates. Weighted quadratic continuity applies to the
two separate Fourier blocks without any normalization assumption.
-/

public section

open MeasureTheory Filter WithLp
open scoped ENNReal NNReal Topology

namespace LiebThirring

/-- A fixed finite additive kinetic bound transfers form convergence to an expectation.
This generic lemma is applied below to the proved Coulomb bounds. -/
theorem tendsto_zero_of_joint_kinetic_bound {N M q : ℕ} {β : Type*} {l : Filter β}
    (P : QuantumState N M q → ℝ≥0∞) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hbound : ∀ ψ : QuantumState N M q, P ψ ≤
      C * (ENNReal.ofReal (‖ψ‖ ^ 2) + quantumElectronKineticEnergy ψ +
        quantumNuclearKineticEnergy ψ))
    (v : β → QuantumFormDomain N M q)
    (h0 : Tendsto (fun n => ‖(v n).val‖) l (𝓝 0))
    (he : Tendsto (fun n => (quantumElectronKineticEnergy (v n).val).toReal) l (𝓝 0))
    (hn : Tendsto (fun n => (quantumNuclearKineticEnergy (v n).val).toReal) l (𝓝 0)) :
    Tendsto (fun n => (P (v n).val).toReal) l (𝓝 0) := by
  have hm : Tendsto (fun n => ENNReal.ofReal (‖(v n).val‖ ^ 2)) l (𝓝 0) := by
    simpa only [Function.comp_def, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (h0.pow 2)
  have he' : Tendsto (fun n => quantumElectronKineticEnergy (v n).val) l (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp he
    have heq : (fun n => ENNReal.ofReal (quantumElectronKineticEnergy (v n).val).toReal) =
        (fun n => quantumElectronKineticEnergy (v n).val) :=
      funext (fun n => ENNReal.ofReal_toReal (v n).property.2.2.1.ne)
    simp only [Function.comp_def] at h
    rw [heq, ENNReal.ofReal_zero] at h
    exact h
  have hn' : Tendsto (fun n => quantumNuclearKineticEnergy (v n).val) l (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hn
    have heq : (fun n => ENNReal.ofReal (quantumNuclearKineticEnergy (v n).val).toReal) =
        (fun n => quantumNuclearKineticEnergy (v n).val) :=
      funext (fun n => ENNReal.ofReal_toReal (v n).property.2.2.2.ne)
    simp only [Function.comp_def] at h
    rw [heq, ENNReal.ofReal_zero] at h
    exact h
  have hupper : Tendsto (fun n => C * (ENNReal.ofReal (‖(v n).val‖ ^ 2) +
      quantumElectronKineticEnergy (v n).val + quantumNuclearKineticEnergy (v n).val))
      l (𝓝 0) := by
    simpa only [zero_add, mul_zero] using
      ENNReal.Tendsto.const_mul ((hm.add he').add hn') (Or.inr hC)
  have hP : Tendsto (fun n => P (v n).val) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => (show (0 : ℝ≥0∞) ≤ P (v n).val from bot_le))
      (fun n => hbound (v n).val)
  simpa only [Function.comp_def, ENNReal.toReal_zero] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hP

theorem tendsto_quantumElectronKineticEnergy_of_difference {N M q : ℕ}
    {β : Type*} {l : Filter β} (u : QuantumFormDomain N M q)
    (v : β → QuantumFormDomain N M q)
    (hlim : Tendsto (fun n => (quantumElectronKineticEnergy (v n - u).val).toReal)
      l (𝓝 0)) :
    Tendsto (fun n => (quantumElectronKineticEnergy (v n).val).toReal)
      l (𝓝 (quantumElectronKineticEnergy u.val).toReal) := by
  let p : QuantumConfiguration N M → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ.fst‖₊ : ℝ≥0∞) ^ 2
  have hp : Measurable p := measurable_const.mul
    (((WithLp.fstL 2 ℝ (Configuration N) (Configuration M)).continuous.measurable).nnnorm.coe_nnreal_ennreal.pow_const 2)
  let F := Lp.fourierTransformₗᵢ (QuantumConfiguration N M) (SpinAmplitudes N q)
  have hd (n : β) :
      (∫⁻ ξ, p ξ * (‖(F (v n).val - F u.val) ξ‖₊ : ℝ≥0∞) ^ 2) < ⊤ := by
    rw [← map_sub]
    exact (v n - u).property.2.2.1
  apply tendsto_lintegral_weight_sq_of_difference p hp (F u.val)
    (fun n => F (v n).val) u.property.2.2.1 (fun n => (v n).property.2.2.1) hd
  change Tendsto (fun n =>
    (∫⁻ ξ, p ξ * (‖(F ((v n).val - u.val)) ξ‖₊ : ℝ≥0∞) ^ 2).toReal) l (𝓝 0) at hlim
  simpa only [map_sub] using hlim

theorem tendsto_quantumNuclearKineticEnergy_of_difference {N M q : ℕ}
    {β : Type*} {l : Filter β} (u : QuantumFormDomain N M q)
    (v : β → QuantumFormDomain N M q)
    (hlim : Tendsto (fun n => (quantumNuclearKineticEnergy (v n - u).val).toReal)
      l (𝓝 0)) :
    Tendsto (fun n => (quantumNuclearKineticEnergy (v n).val).toReal)
      l (𝓝 (quantumNuclearKineticEnergy u.val).toReal) := by
  let p : QuantumConfiguration N M → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ.snd‖₊ : ℝ≥0∞) ^ 2
  have hp : Measurable p := measurable_const.mul
    (((WithLp.sndL 2 ℝ (Configuration N) (Configuration M)).continuous.measurable).nnnorm.coe_nnreal_ennreal.pow_const 2)
  let F := Lp.fourierTransformₗᵢ (QuantumConfiguration N M) (SpinAmplitudes N q)
  have hd (n : β) :
      (∫⁻ ξ, p ξ * (‖(F (v n).val - F u.val) ξ‖₊ : ℝ≥0∞) ^ 2) < ⊤ := by
    rw [← map_sub]
    exact (v n - u).property.2.2.2
  apply tendsto_lintegral_weight_sq_of_difference p hp (F u.val)
    (fun n => F (v n).val) u.property.2.2.2 (fun n => (v n).property.2.2.2) hd
  change Tendsto (fun n =>
    (∫⁻ ξ, p ξ * (‖(F ((v n).val - u.val)) ξ‖₊ : ℝ≥0∞) ^ 2).toReal) l (𝓝 0) at hlim
  simpa only [map_sub] using hlim

end LiebThirring

end
