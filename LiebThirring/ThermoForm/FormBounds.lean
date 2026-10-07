/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.HardyJoint

/-! # A finite joint Coulomb bound at fixed particle counts

Argument thermodynamic confined form estimates. Coarse finite pair counts suffice for continuity
of the form on a fixed sector; no uniform stability constant is claimed here.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

theorem quantumRepulsionEnergy_eq_components {N M q : ℕ} (z : ℕ)
    (ψ : QuantumState N M q) :
    quantumRepulsionEnergy z ψ =
      (∫⁻ X : QuantumConfiguration N M,
        electronRepulsion X.fst * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) +
      ∫⁻ X : QuantumConfiguration N M,
        nuclearRepulsion (fun _ : Fin M => (z : ℝ≥0))
          (fun k => particlePosition X.snd k) * (‖ψ X‖₊ : ℝ≥0∞) ^ 2 := by
  have hw : Measurable (fun X : QuantumConfiguration N M => electronRepulsion X.fst) :=
    Assembly.measurable_electronRepulsion.comp
      (continuous_fst.comp (WithLp.prod_continuous_ofLp ..)).measurable
  have hd : AEMeasurable (fun X => (‖ψ X‖₊ : ℝ≥0∞) ^ 2) volume := by
    simpa only [enorm_eq_nnnorm] using (Lp.aestronglyMeasurable ψ).enorm.pow_const 2
  unfold quantumRepulsionEnergy
  simp_rw [add_mul]
  exact lintegral_add_left' (hw.aemeasurable.mul hd) _

private theorem mass_add_four_kinetic_le (a b c : ℝ≥0∞) :
    a + 4 * b ≤ 4 * (a + b + c) := by
  have ha : a ≤ 4 * a := by
    calc
      a = 1 * a := (one_mul a).symm
      _ ≤ 4 * a := (mul_le_mul_left (by norm_num : (1 : ℝ≥0∞) ≤ 4)) a
  calc
    a + 4 * b ≤ 4 * a + 4 * b := add_le_add ha le_rfl
    _ ≤ 4 * a + 4 * b + 4 * c := le_add_right le_rfl
    _ = _ := by rw [mul_add, mul_add]

/-- Both exact Coulomb expectations obey a finite additive graph bound at fixed counts. -/
theorem exists_quantumCoulomb_formBound (N M q z : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ ψ : QuantumState N M q,
      quantumRepulsionEnergy z ψ ≤ C *
        (ENNReal.ofReal (‖ψ‖ ^ 2) + quantumElectronKineticEnergy ψ +
          quantumNuclearKineticEnergy ψ) ∧
      quantumAttractionEnergy z ψ ≤ C *
        (ENNReal.ofReal (‖ψ‖ ^ 2) + quantumElectronKineticEnergy ψ +
          quantumNuclearKineticEnergy ψ) := by
  classical
  let A : ℝ≥0∞ := ∑ i : Fin N, ∑ _j ∈ Finset.univ.filter (fun j => i < j), 1
  let B : ℝ≥0∞ := (z : ℝ≥0∞) ^ 2 *
    (∑ _σ : SpinLabels N q, ∑ i : Fin M,
      ∑ _j ∈ Finset.univ.filter (fun j => i < j), 1)
  let D : ℝ≥0∞ := ∑ _i : Fin N, ∑ _k : Fin M, (z : ℝ≥0∞)
  have hA : A ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr fun _ _ =>
      ENNReal.sum_ne_top.mpr fun _ _ => by norm_num
  have hB : B ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by finiteness) (ENNReal.sum_ne_top.mpr fun _ _ =>
      ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.sum_ne_top.mpr fun _ _ => by norm_num)
  have hD : D ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr fun _ _ =>
      ENNReal.sum_ne_top.mpr fun _ _ => by finiteness
  refine ⟨(A + B + D) * 4, ENNReal.mul_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hA, hB⟩, hD⟩) (by norm_num), ?_⟩
  intro ψ
  let S := ENNReal.ofReal (‖ψ‖ ^ 2) + quantumElectronKineticEnergy ψ +
    quantumNuclearKineticEnergy ψ
  have hm : ‖ψ‖ₑ ^ 2 = ENNReal.ofReal (‖ψ‖ ^ 2) := by
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg ψ)]
  have he : ‖ψ‖ₑ ^ 2 + 4 * quantumElectronKineticEnergy ψ ≤ 4 * S := by
    rw [hm]
    exact mass_add_four_kinetic_le _ _ _
  have hn : ‖ψ‖ₑ ^ 2 + 4 * quantumNuclearKineticEnergy ψ ≤ 4 * S := by
    rw [hm]
    have h := mass_add_four_kinetic_le (ENNReal.ofReal (‖ψ‖ ^ 2))
      (quantumNuclearKineticEnergy ψ) (quantumElectronKineticEnergy ψ)
    rwa [add_right_comm] at h
  constructor
  · rw [quantumRepulsionEnergy_eq_components]
    calc
      _ ≤ A * (‖ψ‖ₑ ^ 2 + 4 * quantumElectronKineticEnergy ψ) +
          B * (‖ψ‖ₑ ^ 2 + 4 * quantumNuclearKineticEnergy ψ) :=
        add_le_add (quantumElectronRepulsionEnergy_le_formBound ψ)
          (quantumNuclearRepulsionEnergy_le_formBound z ψ)
      _ ≤ A * (4 * S) + B * (4 * S) := add_le_add
        ((mul_le_mul_right he) A) ((mul_le_mul_right hn) B)
      _ = (A + B) * (4 * S) := (add_mul _ _ _).symm
      _ ≤ (A + B + D) * (4 * S) := (mul_le_mul_left (le_add_right le_rfl)) _
      _ = _ := (mul_assoc _ _ _).symm
  · calc
      _ ≤ D * (‖ψ‖ₑ ^ 2 + 4 * quantumElectronKineticEnergy ψ) :=
        quantumAttractionEnergy_le_formBound z ψ
      _ ≤ D * (4 * S) := (mul_le_mul_right he) D
      _ ≤ (A + B + D) * (4 * S) := (mul_le_mul_left (le_add_left le_rfl)) _
      _ = _ := (mul_assoc _ _ _).symm

end LiebThirring

end
