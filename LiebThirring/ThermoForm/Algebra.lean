/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.SmoothCore
import LiebThirring.Variational.FormAlgebra
import LiebThirring.Variational.TrialScaling

/-! # Algebra of the joint finite-kinetic form domain

Argument thermodynamic confined form estimates. The form carrier is a complex submodule;
its two Fourier kinetic forms have the usual homogeneity and triangle bound.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

theorem lintegral_weight_add_sq_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} (w : α → ℝ≥0∞) (hw : Measurable w)
    (u v : Lp E 2 μ) :
    (∫⁻ x, w x * (‖(u + v) x‖₊ : ℝ≥0∞) ^ 2 ∂μ) ≤
      2 * ((∫⁻ x, w x * (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂μ) +
        ∫⁻ x, w x * (‖v x‖₊ : ℝ≥0∞) ^ 2 ∂μ) := by
  calc
    _ ≤ ∫⁻ x, 2 * (w x * (‖u x‖₊ : ℝ≥0∞) ^ 2 +
        w x * (‖v x‖₊ : ℝ≥0∞) ^ 2) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [Lp.coeFn_add u v] with x hx
      dsimp only [Pi.add_apply] at hx
      rw [hx]
      exact (mul_le_mul_right (enorm_add_sq_le (u x) (v x)) (w x)).trans_eq (by ring)
    _ = _ := by
      rw [lintegral_const_mul' 2 _ (by norm_num), lintegral_add_left']
      exact hw.aemeasurable.mul ((Lp.aestronglyMeasurable u).nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2)

theorem quantumElectronKineticEnergy_add_le {N M q : ℕ} (u v : QuantumState N M q) :
    quantumElectronKineticEnergy (u + v) ≤
      2 * (quantumElectronKineticEnergy u + quantumElectronKineticEnergy v) := by
  unfold quantumElectronKineticEnergy
  rw [map_add]
  apply lintegral_weight_add_sq_le
  exact measurable_const.mul
    (((WithLp.fstL 2 ℝ (Configuration N) (Configuration M)).continuous.measurable).nnnorm.coe_nnreal_ennreal.pow_const 2)

theorem quantumNuclearKineticEnergy_add_le {N M q : ℕ} (u v : QuantumState N M q) :
    quantumNuclearKineticEnergy (u + v) ≤
      2 * (quantumNuclearKineticEnergy u + quantumNuclearKineticEnergy v) := by
  unfold quantumNuclearKineticEnergy
  rw [map_add]
  apply lintegral_weight_add_sq_le
  exact measurable_const.mul
    (((WithLp.sndL 2 ℝ (Configuration N) (Configuration M)).continuous.measurable).nnnorm.coe_nnreal_ennreal.pow_const 2)

theorem quantumElectronKineticEnergy_smul {N M q : ℕ} (c : ℂ) (u : QuantumState N M q) :
    quantumElectronKineticEnergy (c • u) =
      (‖c‖₊ : ℝ≥0∞) ^ 2 * quantumElectronKineticEnergy u := by
  unfold quantumElectronKineticEnergy
  rw [map_smul]
  exact trial_lintegral_weight_smul _ c _

theorem quantumNuclearKineticEnergy_smul {N M q : ℕ} (c : ℂ) (u : QuantumState N M q) :
    quantumNuclearKineticEnergy (c • u) =
      (‖c‖₊ : ℝ≥0∞) ^ 2 * quantumNuclearKineticEnergy u := by
  unfold quantumNuclearKineticEnergy
  rw [map_smul]
  exact trial_lintegral_weight_smul _ c _

theorem quantum_antisymmetric_zero (N M q : ℕ) :
    quantum_antisymmetric (0 : QuantumState N M q) := by
  intro σ
  have h := Lp.coeFn_zero (SpinAmplitudes N q) 2
    (volume : Measure (QuantumConfiguration N M))
  filter_upwards [h, (measurePreserving_quantum_electron_permutation σ).quasiMeasurePreserving.ae h]
    with X hX hσX
  intro s
  rw [hX, hσX]
  simp only [Pi.zero_apply, PiLp.zero_apply, mul_zero]

theorem nuclear_symmetric_zero (N M q : ℕ) : nuclear_symmetric (0 : QuantumState N M q) := by
  intro τ
  have h := Lp.coeFn_zero (SpinAmplitudes N q) 2
    (volume : Measure (QuantumConfiguration N M))
  filter_upwards [h, (measurePreserving_quantum_nuclear_permutation τ).quasiMeasurePreserving.ae h]
    with X hX hτX
  intro s
  rw [hX, hτX]
  simp only [Pi.zero_apply, PiLp.zero_apply]

theorem quantum_antisymmetric_add {N M q : ℕ} {u v : QuantumState N M q}
    (hu : quantum_antisymmetric u) (hv : quantum_antisymmetric v) :
    quantum_antisymmetric (u + v) := by
  intro σ
  have h := Lp.coeFn_add u v
  filter_upwards [hu σ, hv σ, h,
    (measurePreserving_quantum_electron_permutation σ).quasiMeasurePreserving.ae h]
    with X huX hvX hX hσX
  intro s
  rw [hX, hσX]
  simp only [Pi.add_apply, PiLp.add_apply, huX, hvX, mul_add]

theorem nuclear_symmetric_add {N M q : ℕ} {u v : QuantumState N M q}
    (hu : nuclear_symmetric u) (hv : nuclear_symmetric v) : nuclear_symmetric (u + v) := by
  intro τ
  have h := Lp.coeFn_add u v
  filter_upwards [hu τ, hv τ, h,
    (measurePreserving_quantum_nuclear_permutation τ).quasiMeasurePreserving.ae h]
    with X huX hvX hX hτX
  intro s
  rw [hX, hτX]
  simp only [Pi.add_apply, PiLp.add_apply, huX, hvX]

theorem quantum_antisymmetric_smul {N M q : ℕ} (c : ℂ) {u : QuantumState N M q}
    (hu : quantum_antisymmetric u) : quantum_antisymmetric (c • u) := by
  intro σ
  have h := Lp.coeFn_smul c u
  filter_upwards [hu σ, h,
    (measurePreserving_quantum_electron_permutation σ).quasiMeasurePreserving.ae h]
    with X huX hX hσX
  intro s
  rw [hX, hσX]
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, huX]
  ring

theorem nuclear_symmetric_smul {N M q : ℕ} (c : ℂ) {u : QuantumState N M q}
    (hu : nuclear_symmetric u) : nuclear_symmetric (c • u) := by
  intro τ
  have h := Lp.coeFn_smul c u
  filter_upwards [hu τ, h,
    (measurePreserving_quantum_nuclear_permutation τ).quasiMeasurePreserving.ae h]
    with X huX hX hτX
  intro s
  rw [hX, hτX]
  simp only [Pi.smul_apply, PiLp.smul_apply, huX]

@[expose] noncomputable def quantumFormDomainSubmodule (N M q : ℕ) :
    Submodule ℂ (QuantumState N M q) where
  carrier := {ψ | quantum_antisymmetric ψ ∧ nuclear_symmetric ψ ∧
    quantumElectronKineticEnergy ψ < ⊤ ∧ quantumNuclearKineticEnergy ψ < ⊤}
  zero_mem' := ⟨quantum_antisymmetric_zero N M q, nuclear_symmetric_zero N M q,
    by rw [quantumElectronKineticEnergy_zero]; exact ENNReal.zero_lt_top,
    by rw [quantumNuclearKineticEnergy_zero]; exact ENNReal.zero_lt_top⟩
  add_mem' hu hv := ⟨quantum_antisymmetric_add hu.1 hv.1,
    nuclear_symmetric_add hu.2.1 hv.2.1,
    (quantumElectronKineticEnergy_add_le _ _).trans_lt
      (ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hu.2.2.1, hv.2.2.1⟩)),
    (quantumNuclearKineticEnergy_add_le _ _).trans_lt
      (ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hu.2.2.2, hv.2.2.2⟩))⟩
  smul_mem' c ψ hψ := ⟨quantum_antisymmetric_smul c hψ.1,
    nuclear_symmetric_smul c hψ.2.1,
    by rw [quantumElectronKineticEnergy_smul]
       exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hψ.2.2.1,
    by rw [quantumNuclearKineticEnergy_smul]
       exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hψ.2.2.2⟩

noncomputable instance {N M q : ℕ} : AddCommGroup (QuantumFormDomain N M q) :=
  inferInstanceAs (AddCommGroup (quantumFormDomainSubmodule N M q))

end LiebThirring

end
