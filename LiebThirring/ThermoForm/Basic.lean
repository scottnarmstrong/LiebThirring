/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.DirichletBallFormDomain
public import LiebThirring.Thermodynamic.QuantumEnergy

/-! # Elementary joint form identities

Basic zero-state and vacuum identities for confined forms.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

theorem quantumElectronKineticEnergy_zero (N M q : ℕ) :
    quantumElectronKineticEnergy (0 : QuantumState N M q) = 0 := by
  unfold quantumElectronKineticEnergy
  rw [map_zero]
  calc
    _ = ∫⁻ _ : QuantumConfiguration N M, (0 : ℝ≥0∞) := by
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_zero (SpinAmplitudes N q) 2
        (volume : Measure (QuantumConfiguration N M))] with ξ hξ
      simp only [hξ, Pi.zero_apply, nnnorm_zero, ENNReal.coe_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    _ = 0 := lintegral_zero

theorem quantumNuclearKineticEnergy_zero (N M q : ℕ) :
    quantumNuclearKineticEnergy (0 : QuantumState N M q) = 0 := by
  unfold quantumNuclearKineticEnergy
  rw [map_zero]
  calc
    _ = ∫⁻ _ : QuantumConfiguration N M, (0 : ℝ≥0∞) := by
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_zero (SpinAmplitudes N q) 2
        (volume : Measure (QuantumConfiguration N M))] with ξ hξ
      simp only [hξ, Pi.zero_apply, nnnorm_zero, ENNReal.coe_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    _ = 0 := lintegral_zero

theorem quantumElectronKineticEnergy_vacuum {M q : ℕ} (ψ : QuantumState 0 M q) :
    quantumElectronKineticEnergy ψ = 0 := by
  unfold quantumElectronKineticEnergy
  calc
    _ = ∫⁻ _ : QuantumConfiguration 0 M, (0 : ℝ≥0∞) := by
      apply lintegral_congr
      intro ξ
      rw [show ξ.fst = 0 from Subsingleton.elim _ _]
      simp only [nnnorm_zero, ENNReal.coe_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]
    _ = 0 := lintegral_zero

theorem quantumNuclearKineticEnergy_vacuum {N q : ℕ} (ψ : QuantumState N 0 q) :
    quantumNuclearKineticEnergy ψ = 0 := by
  unfold quantumNuclearKineticEnergy
  calc
    _ = ∫⁻ _ : QuantumConfiguration N 0, (0 : ℝ≥0∞) := by
      apply lintegral_congr
      intro ξ
      rw [show ξ.snd = 0 from Subsingleton.elim _ _]
      simp only [nnnorm_zero, ENNReal.coe_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]
    _ = 0 := lintegral_zero

theorem quantumRepulsionEnergy_vacuum {q : ℕ} (z : ℕ) (ψ : QuantumState 0 0 q) :
    quantumRepulsionEnergy z ψ = 0 := by
  simp only [quantumRepulsionEnergy, electronRepulsion, nuclearRepulsion,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_mul, lintegral_zero]

theorem quantumAttractionEnergy_no_electrons {M q : ℕ} (z : ℕ)
    (ψ : QuantumState 0 M q) : quantumAttractionEnergy z ψ = 0 := by
  simp only [quantumAttractionEnergy, attraction, Finset.univ_eq_empty,
    Finset.sum_empty, zero_mul, lintegral_zero]

theorem quantumEnergy_vacuum {q : ℕ} (z : ℕ) (m : {m : ℝ≥0 // 0 < m})
    (ψ : QuantumFormDomain 0 0 q) : quantumEnergy z m ψ = 0 := by
  simp only [quantumEnergy, quantumCoulombEnergy, quantumElectronKineticEnergy_vacuum,
    quantumNuclearKineticEnergy_vacuum, quantumRepulsionEnergy_vacuum,
    quantumAttractionEnergy_no_electrons, ENNReal.toReal_zero, mul_zero,
    add_zero, sub_zero]

end LiebThirring

end
