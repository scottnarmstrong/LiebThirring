/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoStability.FibreStability
public import LiebThirring.Thermodynamic.QuantumEnergy

/-! # Integrating static stability while retaining nuclear kinetic energy

The extended bound needs only electronic antisymmetry and finite electronic kinetic energy.
The real-energy conclusion additionally uses finiteness of repulsion, supplied by the pair
Hardy estimates of the confined form estimates.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring.ThermoStability

theorem quantum_extended_stability (q : ℕ) (hq : 1 ≤ q) (z : ℕ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (N M : ℕ) (ψ : QuantumState N M q),
      quantum_antisymmetric ψ → quantumElectronKineticEnergy ψ < ⊤ →
      quantumAttractionEnergy z ψ ≤ quantumElectronKineticEnergy ψ +
        quantumRepulsionEnergy z ψ +
        (C : ℝ≥0∞) * (N + M : ℕ) * (‖ψ‖₊ : ℝ≥0∞) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := homogeneous_static_stability q hq z
  refine ⟨C, hC, ?_⟩
  intro N M ψ hanti hT
  rw [quantumAttractionEnergy_eq_fibre_lintegral]
  have hpoint : ∀ᵐ R : Configuration M,
      (∫⁻ x : Configuration N,
        attraction (fun _ : Fin M => (z : ℝ≥0)) (fun k => particlePosition R k) x *
          (‖electronFibreField ψ R x‖₊ : ℝ≥0∞) ^ 2) ≤
        kineticEnergy (electronFibreField ψ R) +
        ((∫⁻ x : Configuration N, electronRepulsion x *
          (‖electronFibreField ψ R x‖₊ : ℝ≥0∞) ^ 2) +
          nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0)) (fun k => particlePosition R k) *
            (‖electronFibreField ψ R‖₊ : ℝ≥0∞) ^ 2) +
        (C : ℝ≥0∞) * (N + M : ℕ) * (‖electronFibreField ψ R‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [antisymmetric_electronFibreField_ae ψ hanti,
      kineticEnergy_electronFibre_lt_top_ae ψ hT, ae_injective_nuclearPositions M]
      with R hRanti hRT hR
    exact hbound N M R hR ⟨electronFibreField ψ R, hRanti, hRT⟩
  refine (lintegral_mono_ae hpoint).trans_eq ?_
  have hmass : AEMeasurable (fun R : Configuration M =>
      (C : ℝ≥0∞) * (N + M : ℕ) * (‖electronFibreField ψ R‖₊ : ℝ≥0∞) ^ 2) volume := by
    have hm : AEMeasurable (fun R : Configuration M => ‖electronFibreField ψ R‖ₑ ^ 2) volume :=
      (Lp.aestronglyMeasurable (electronFibreField ψ)).enorm.pow_const 2
    simpa only [enorm_eq_nnnorm] using hm.const_mul ((C : ℝ≥0∞) * (N + M : ℕ))
  rw [lintegral_add_right' _ hmass,
    lintegral_add_left' (aemeasurable_electronFibre_kineticEnergy ψ),
    ← quantumElectronKineticEnergy_eq_fibre_lintegral,
    ← quantumRepulsionEnergy_eq_fibre_lintegral]
  congr 1
  change (∫⁻ R, ((C : ℝ≥0∞) * (N + M : ℕ)) * ‖electronFibreField ψ R‖ₑ ^ 2) = _
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.natCast_ne_top _))]
  change _ * (∫⁻ R, ‖electronFibreField ψ R‖ₑ ^ 2) = _
  rw [lintegral_l2_enorm_sq]
  have hn : ‖electronFibreField ψ‖₊ = ‖ψ‖₊ := NNReal.coe_injective (electronFibreField_norm ψ)
  rw [enorm_eq_nnnorm, hn]

/-- Convert the integrated extended bound to the exact real inequality once confined form estimates supplies
finite repulsion. Attraction finiteness follows from the stability inequality itself. -/
theorem quantum_real_bound_of_extended {N M q z : ℕ}
    (C : ℝ≥0) (m : {m : ℝ≥0 // 0 < m}) (ψ : QuantumFormDomain N M q)
    (hrep : quantumRepulsionEnergy z ψ.val < ⊤)
    (hbound : quantumAttractionEnergy z ψ.val ≤ quantumElectronKineticEnergy ψ.val +
      quantumRepulsionEnergy z ψ.val + (C : ℝ≥0∞) * (N + M : ℕ) * (‖ψ.val‖₊ : ℝ≥0∞) ^ 2) :
    -(C : ℝ) * ((N + M : ℕ) : ℝ) * ‖ψ.val‖ ^ 2 +
      (nuclearKineticCoefficient m : ℝ) * (quantumNuclearKineticEnergy ψ.val).toReal ≤
        quantumEnergy z m ψ := by
  let D : ℝ≥0 := C * ‖ψ.val‖₊ ^ 2
  have hext : quantumAttractionEnergy z ψ.val ≤ quantumElectronKineticEnergy ψ.val +
      quantumRepulsionEnergy z ψ.val + 0 + (D : ℝ≥0∞) * (N + M : ℕ) := by
    simpa only [D, ENNReal.coe_mul, ENNReal.coe_pow, add_zero,
      mul_right_comm] using hbound
  have h := (Assembly.real_form_of_extended_bound D (N + M)
    ψ.property.2.2.1 hrep (by simp) hext).2
  simp only [D, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm, ENNReal.toReal_zero,
    add_zero] at h
  unfold quantumEnergy quantumCoulombEnergy
  linarith only [h]

end LiebThirring.ThermoStability

end
