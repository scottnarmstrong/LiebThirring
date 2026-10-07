/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.QuantumEnergy
import LiebThirring.ThermoStability.IntegratedStability
import LiebThirring.ThermoForm.HardyJoint

/-! # Extensive stability with quantum nuclei

The static stability constant is integrated over nuclear configurations. The joint pair
Hardy bounds make repulsion finite, and the extended stability bound itself makes attraction
finite. Nuclear kinetic energy is retained unchanged in the real inequality.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring.Proofs

/-- An extensive lower bound for quantum nuclear energy. -/
theorem quantum_stability (q : ℕ) (hq : 1 ≤ q) (z : ℕ) (_hz : 1 ≤ z) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (N M : ℕ) (m : {m : ℝ≥0 // 0 < m}) (ψ : QuantumFormDomain N M q),
        -(C : ℝ) * ((N + M : ℕ) : ℝ) * ‖ψ.val‖ ^ 2 +
          (nuclearKineticCoefficient m : ℝ) *
            (quantumNuclearKineticEnergy ψ.val).toReal ≤ quantumEnergy z m ψ := by
  obtain ⟨C, hC, hbound⟩ := ThermoStability.quantum_extended_stability q hq z
  refine ⟨C, hC, ?_⟩
  intro N M m ψ
  have hTe := ψ.property.2.2.1
  have hTn := ψ.property.2.2.2
  have hmass : ‖ψ.val‖ₑ ^ 2 < ⊤ :=
    ENNReal.pow_lt_top (by simpa only [enorm_eq_nnnorm] using
      (ENNReal.coe_lt_top : (‖ψ.val‖₊ : ℝ≥0∞) < ⊤))
  have hpairs (K : ℕ) :
      (∑ i : Fin K, ∑ _j ∈ Finset.univ.filter (fun j => i < j), (1 : ℝ≥0∞)) < ⊤ :=
    ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.sum_lt_top.mpr fun _ _ => by norm_num
  have hncoeff : ((z : ℝ≥0∞) ^ 2 *
      (∑ _σ : SpinLabels N q, ∑ i : Fin M,
        ∑ _j ∈ Finset.univ.filter (fun j => i < j), (1 : ℝ≥0∞))) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.pow_lt_top (ENNReal.natCast_lt_top z))
      (ENNReal.sum_lt_top.mpr fun _ _ => hpairs M)
  have he : (∫⁻ X : QuantumConfiguration N M,
      electronRepulsion X.fst * (‖ψ.val X‖₊ : ℝ≥0∞) ^ 2) < ⊤ :=
    lt_of_le_of_lt (quantumElectronRepulsionEnergy_le_formBound ψ.val)
      (ENNReal.mul_lt_top (hpairs N)
        (ENNReal.add_lt_top.mpr ⟨hmass, ENNReal.mul_lt_top (by norm_num) hTe⟩))
  have hn : (∫⁻ X : QuantumConfiguration N M,
      nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
        (fun k => particlePosition X.snd k) * (‖ψ.val X‖₊ : ℝ≥0∞) ^ 2) < ⊤ :=
    lt_of_le_of_lt (quantumNuclearRepulsionEnergy_le_formBound z ψ.val)
      (ENNReal.mul_lt_top hncoeff
        (ENNReal.add_lt_top.mpr ⟨hmass, ENNReal.mul_lt_top (by norm_num) hTn⟩))
  have hrep : quantumRepulsionEnergy z ψ.val < ⊤ := by
    unfold quantumRepulsionEnergy
    simp_rw [add_mul]
    have hm : Measurable (fun X : QuantumConfiguration N M =>
        electronRepulsion X.fst * (‖ψ.val X‖₊ : ℝ≥0∞) ^ 2) :=
      (Assembly.measurable_electronRepulsion.comp
        (continuous_fst.comp (WithLp.prod_continuous_ofLp ..)).measurable).mul
        ((Lp.stronglyMeasurable ψ.val).measurable.nnnorm.coe_nnreal_ennreal.pow_const 2)
    rw [lintegral_add_left hm]
    exact ENNReal.add_lt_top.mpr ⟨he, hn⟩
  exact ThermoStability.quantum_real_bound_of_extended C m ψ hrep
    (hbound N M ψ.val ψ.property.1 hTe)

end LiebThirring.Proofs

end
