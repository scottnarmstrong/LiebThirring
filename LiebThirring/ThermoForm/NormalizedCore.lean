/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.Algebra

/-! # Normalization in the joint kinetic graph norm

Quantitative estimates showing that inverse-norm normalization preserves convergence in the
full electron--nuclear kinetic graph norm.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- The exact nonnegative error used in the Dirichlet closure. -/
@[expose] noncomputable def quantumGraphError {N M q : ℕ}
    (m : {m : ℝ≥0 // 0 < m}) (u v : QuantumState N M q) : ℝ≥0∞ :=
  ENNReal.ofReal (‖u - v‖ ^ 2) + quantumElectronKineticEnergy (u - v) +
    (nuclearKineticCoefficient m : ℝ≥0∞) * quantumNuclearKineticEnergy (u - v)

theorem norm_inv_norm_le_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u v : E) (hu : ‖u‖ = 1) (hv : v ≠ 0) (hd : ‖u - v‖ < 1 / 2) :
    ‖((‖v‖⁻¹ : ℝ) : ℂ)‖ ≤ 2 := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hlower : 1 / 2 < ‖v‖ := by
    have hrev := norm_sub_norm_le u v
    rw [hu] at hrev
    linarith only [hrev, hd]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
  exact (inv_le_iff_one_le_mul₀ hvpos).mpr (by linarith)

theorem norm_one_sub_inv_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u v : E) (hu : ‖u‖ = 1) (hv : v ≠ 0) (hd : ‖u - v‖ < 1 / 2) :
    ‖(((1 - ‖v‖⁻¹ : ℝ) : ℂ))‖ ≤ 2 * ‖u - v‖ := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hlower : 1 / 2 < ‖v‖ := by
    have hrev := norm_sub_norm_le u v
    rw [hu] at hrev
    linarith only [hrev, hd]
  have hnorm : |1 - ‖v‖| ≤ ‖u - v‖ := by
    simpa only [hu] using abs_norm_sub_norm_le u v
  rw [Complex.norm_real, Real.norm_eq_abs]
  rw [show 1 - ‖v‖⁻¹ = (‖v‖ - 1) / ‖v‖ by field_simp]
  rw [abs_div, abs_of_pos hvpos, abs_sub_comm]
  apply (div_le_div_of_nonneg_right hnorm (norm_nonneg v)).trans
  exact (div_le_iff₀ hvpos).mpr (by nlinarith only [hlower, norm_nonneg (u - v)])

/-- Normalizing a nearby nonzero state costs only a fixed multiple of its full graph error. -/
theorem quantumGraphError_normalize_le {N M q : ℕ}
    (m : {m : ℝ≥0 // 0 < m}) (u v : QuantumState N M q)
    (hu : ‖u‖ = 1) (hv : v ≠ 0) (hd : ‖u - v‖ < 1 / 2) :
    quantumGraphError m u (((‖v‖⁻¹ : ℝ) : ℂ) • v) ≤
      16 * (1 + quantumElectronKineticEnergy u +
        (nuclearKineticCoefficient m : ℝ≥0∞) * quantumNuclearKineticEnergy u) *
          quantumGraphError m u v := by
  let c : ℂ := ((‖v‖⁻¹ : ℝ) : ℂ)
  let b : ℂ := (((1 - ‖v‖⁻¹ : ℝ) : ℂ))
  have hc : (‖c‖₊ : ℝ≥0∞) ^ 2 ≤ 4 := by
    apply ENNReal.coe_le_coe.mpr
    rw [← NNReal.coe_le_coe]
    norm_num only [NNReal.coe_pow, NNReal.coe_ofNat, coe_nnnorm]
    nlinarith only [norm_inv_norm_le_two u v hu hv hd, norm_nonneg c]
  have hb : (‖b‖₊ : ℝ≥0∞) ^ 2 ≤ 4 * ENNReal.ofReal (‖u - v‖ ^ 2) := by
    have h := norm_one_sub_inv_norm_le u v hu hv hd
    change ‖b‖ ≤ 2 * ‖u - v‖ at h
    have hbnn : ‖b‖₊ ^ 2 ≤ 4 * ‖u - v‖₊ ^ 2 := by
      rw [← NNReal.coe_le_coe]
      norm_num only [NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_ofNat, coe_nnnorm]
      nlinarith only [h, norm_nonneg b, norm_nonneg (u - v)]
    calc
      _ ≤ 4 * ((‖u - v‖₊ : ℝ≥0∞) ^ 2) := by
        exact ENNReal.coe_le_coe.mpr hbnn
      _ = _ := by
        rw [← enorm_eq_nnnorm, ← ofReal_norm,
          ← ENNReal.ofReal_pow (norm_nonneg (u - v))]
  have hid : u - c • v = c • (u - v) + b • u := by
    dsimp only [c, b]
    module
  have hn : ENNReal.ofReal (‖u - c • v‖ ^ 2) ≤
      16 * ENNReal.ofReal (‖u - v‖ ^ 2) := by
    have hnorm : ‖u - c • v‖ ≤ 4 * ‖u - v‖ := by
      rw [hid]
      calc
        _ ≤ ‖c‖ * ‖u - v‖ + ‖b‖ * ‖u‖ := by
          simpa only [norm_smul] using norm_add_le (c • (u - v)) (b • u)
        _ ≤ 2 * ‖u - v‖ + 2 * ‖u - v‖ * 1 := by
          gcongr
          · exact norm_inv_norm_le_two u v hu hv hd
          · exact norm_one_sub_inv_norm_le u v hu hv hd
          · exact le_of_eq hu
        _ = 4 * ‖u - v‖ := by ring
    calc
      _ ≤ ENNReal.ofReal ((4 * ‖u - v‖) ^ 2) := by
        exact ENNReal.ofReal_le_ofReal
          ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))).mpr hnorm)
      _ = _ := by
        rw [mul_pow, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4 ^ 2)]
        norm_num
  have he : quantumElectronKineticEnergy (u - c • v) ≤
      8 * (quantumElectronKineticEnergy (u - v) +
        ENNReal.ofReal (‖u - v‖ ^ 2) * quantumElectronKineticEnergy u) := by
    rw [hid]
    calc
      _ ≤ 2 * (quantumElectronKineticEnergy (c • (u - v)) +
          quantumElectronKineticEnergy (b • u)) := quantumElectronKineticEnergy_add_le _ _
      _ = 2 * ((‖c‖₊ : ℝ≥0∞) ^ 2 * quantumElectronKineticEnergy (u - v) +
          (‖b‖₊ : ℝ≥0∞) ^ 2 * quantumElectronKineticEnergy u) := by
            rw [quantumElectronKineticEnergy_smul, quantumElectronKineticEnergy_smul]
      _ ≤ 2 * (4 * quantumElectronKineticEnergy (u - v) +
          (4 * ENNReal.ofReal (‖u - v‖ ^ 2)) * quantumElectronKineticEnergy u) := by
            gcongr
      _ = _ := by ring
  have hnu : (nuclearKineticCoefficient m : ℝ≥0∞) *
      quantumNuclearKineticEnergy (u - c • v) ≤
      8 * ((nuclearKineticCoefficient m : ℝ≥0∞) *
          quantumNuclearKineticEnergy (u - v) +
        ENNReal.ofReal (‖u - v‖ ^ 2) *
          ((nuclearKineticCoefficient m : ℝ≥0∞) * quantumNuclearKineticEnergy u)) := by
    rw [hid]
    calc
      _ ≤ (nuclearKineticCoefficient m : ℝ≥0∞) *
          (2 * (quantumNuclearKineticEnergy (c • (u - v)) +
            quantumNuclearKineticEnergy (b • u))) := by
              gcongr
              exact quantumNuclearKineticEnergy_add_le _ _
      _ = (nuclearKineticCoefficient m : ℝ≥0∞) *
          (2 * ((‖c‖₊ : ℝ≥0∞) ^ 2 * quantumNuclearKineticEnergy (u - v) +
            (‖b‖₊ : ℝ≥0∞) ^ 2 * quantumNuclearKineticEnergy u)) := by
              rw [quantumNuclearKineticEnergy_smul, quantumNuclearKineticEnergy_smul]
      _ ≤ (nuclearKineticCoefficient m : ℝ≥0∞) *
          (2 * (4 * quantumNuclearKineticEnergy (u - v) +
            (4 * ENNReal.ofReal (‖u - v‖ ^ 2)) * quantumNuclearKineticEnergy u)) := by
              gcongr
      _ = _ := by ring
  dsimp only [quantumGraphError]
  calc
    _ ≤ 16 * ENNReal.ofReal (‖u - v‖ ^ 2) +
        8 * (quantumElectronKineticEnergy (u - v) +
          ENNReal.ofReal (‖u - v‖ ^ 2) * quantumElectronKineticEnergy u) +
        8 * ((nuclearKineticCoefficient m : ℝ≥0∞) * quantumNuclearKineticEnergy (u - v) +
          ENNReal.ofReal (‖u - v‖ ^ 2) *
            ((nuclearKineticCoefficient m : ℝ≥0∞) * quantumNuclearKineticEnergy u)) :=
      add_le_add (add_le_add hn he) hnu
    _ ≤ 16 * (1 + quantumElectronKineticEnergy u +
        (nuclearKineticCoefficient m : ℝ≥0∞) * quantumNuclearKineticEnergy u) *
          (ENNReal.ofReal (‖u - v‖ ^ 2) + quantumElectronKineticEnergy (u - v) +
            (nuclearKineticCoefficient m : ℝ≥0∞) * quantumNuclearKineticEnergy (u - v)) := by
      let E : ℝ≥0∞ := ENNReal.ofReal (‖u - v‖ ^ 2) +
        quantumElectronKineticEnergy (u - v) +
          (nuclearKineticCoefficient m : ℝ≥0∞) * quantumNuclearKineticEnergy (u - v)
      have hx : ENNReal.ofReal (‖u - v‖ ^ 2) ≤ E := by
        exact (le_add_right le_rfl).trans (le_add_right le_rfl)
      have he' : quantumElectronKineticEnergy (u - v) ≤ E := by
        exact (le_add_left le_rfl).trans (le_add_right le_rfl)
      have hn' : (nuclearKineticCoefficient m : ℝ≥0∞) *
          quantumNuclearKineticEnergy (u - v) ≤ E := le_add_left le_rfl
      calc
        _ ≤ 16 * E + 8 * (E * quantumElectronKineticEnergy u) +
            8 * (E * ((nuclearKineticCoefficient m : ℝ≥0∞) *
              quantumNuclearKineticEnergy u)) := by
                calc
                  _ = (16 * ENNReal.ofReal (‖u - v‖ ^ 2) +
                      8 * quantumElectronKineticEnergy (u - v) +
                      8 * ((nuclearKineticCoefficient m : ℝ≥0∞) *
                        quantumNuclearKineticEnergy (u - v))) +
                      8 * (ENNReal.ofReal (‖u - v‖ ^ 2) * quantumElectronKineticEnergy u) +
                      8 * (ENNReal.ofReal (‖u - v‖ ^ 2) *
                        ((nuclearKineticCoefficient m : ℝ≥0∞) *
                          quantumNuclearKineticEnergy u)) := by ring
                  _ ≤ _ := by
                    gcongr
                    calc
                      16 * ENNReal.ofReal (‖u - v‖ ^ 2) +
                          8 * quantumElectronKineticEnergy (u - v) +
                          8 * ((nuclearKineticCoefficient m : ℝ≥0∞) *
                            quantumNuclearKineticEnergy (u - v))
                          ≤ 16 * ENNReal.ofReal (‖u - v‖ ^ 2) +
                            16 * quantumElectronKineticEnergy (u - v) +
                            16 * ((nuclearKineticCoefficient m : ℝ≥0∞) *
                              quantumNuclearKineticEnergy (u - v)) := by gcongr <;> norm_num
                      _ = 16 * E := by dsimp only [E]; ring
        _ ≤ 16 * E + 16 * (E * quantumElectronKineticEnergy u) +
            16 * (E * ((nuclearKineticCoefficient m : ℝ≥0∞) *
              quantumNuclearKineticEnergy u)) := by
                gcongr <;> norm_num
        _ = _ := by dsimp only [E]; ring

end LiebThirring

end
