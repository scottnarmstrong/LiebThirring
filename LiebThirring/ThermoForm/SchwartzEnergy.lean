/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.QuantumFormDomain
import LiebThirring.Fourier.Schwartz
import LiebThirring.Variational.TrialBasic

/-! # Joint Fourier and gradient energies on the smooth core

Argument thermodynamic confined form estimates: the Fourier multiplier has exactly the
`(2π)²` gradient-square normalization for both species.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap FourierTransform

namespace LiebThirring

theorem quantumElectronKineticEnergy_schwartz (N M q : ℕ) (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    quantumElectronKineticEnergy (f.toLp 2 (volume : Measure (QuantumConfiguration N M))) =
      ∑ i : Fin N, ∑ a : Fin 3, ∫⁻ x : QuantumConfiguration N M,
        (‖fderiv ℝ (fun y => f y) x (toLp 2 (PiLp.single 2 (i, a) (1 : ℝ), (0 : Configuration M)))‖₊ : ℝ≥0∞) ^ 2 := by
  classical
  have hnorm (x : QuantumConfiguration N M) :
      (‖x.fst‖₊ : ℝ≥0∞) ^ 2 =
        ∑ i : Fin N, ∑ a : Fin 3, ENNReal.ofReal (x.fst (i, a) ^ 2) := by
    change ‖x.fst‖ₑ ^ 2 = _
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
      ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
    exact Fintype.sum_prod_type _
  have hderiv (i : Fin N) (a : Fin 3) :
      (∫⁻ x : QuantumConfiguration N M,
        (‖fderiv ℝ (fun y => f y) x (toLp 2 (PiLp.single 2 (i, a) (1 : ℝ), (0 : Configuration M)))‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x : QuantumConfiguration N M, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        ENNReal.ofReal (x.fst (i, a) ^ 2) * (‖(𝓕 f) x‖₊ : ℝ≥0∞) ^ 2 := by
    simpa only [WithLp.prod_inner_apply, WithLp.fst, WithLp.snd,
      inner_zero_right, zero_add, add_zero, EuclideanSpace.inner_single_right, map_one, one_mul,
      RCLike.conj_to_real] using
      Fourier.lintegral_fderiv_eq_fourier f (toLp 2 (PiLp.single 2 (i, a) (1 : ℝ), (0 : Configuration M)))
  unfold quantumElectronKineticEnergy
  change (∫⁻ x : QuantumConfiguration N M, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
    (‖x.fst‖₊ : ℝ≥0∞) ^ 2 *
      (‖(𝓕 (f.toLp 2 (volume : Measure (QuantumConfiguration N M))) : QuantumState N M q) x‖₊ : ℝ≥0∞) ^ 2) = _
  rw [SchwartzMap.toLp_fourier_eq]
  calc
    _ = ∫⁻ x : QuantumConfiguration N M, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        (‖x.fst‖₊ : ℝ≥0∞) ^ 2 * (‖(𝓕 f) x‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [(𝓕 f).coeFn_toLp 2 (volume : Measure (QuantumConfiguration N M))] with x hx
      rw [hx]
    _ = ∫⁻ x : QuantumConfiguration N M, ∑ i : Fin N, ∑ a : Fin 3,
        ENNReal.ofReal ((2 * Real.pi) ^ 2) * ENNReal.ofReal (x.fst (i, a) ^ 2) *
          (‖(𝓕 f) x‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr
      intro x
      rw [hnorm]
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i : Fin N, ∑ a : Fin 3, ∫⁻ x : QuantumConfiguration N M,
        ENNReal.ofReal ((2 * Real.pi) ^ 2) * ENNReal.ofReal (x.fst (i, a) ^ 2) *
          (‖(𝓕 f) x‖₊ : ℝ≥0∞) ^ 2 := by
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [lintegral_finsetSum]
        intro a _
        fun_prop
      · intro i _
        fun_prop
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      exact (hderiv i a).symm


theorem quantumNuclearKineticEnergy_schwartz (N M q : ℕ) (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    quantumNuclearKineticEnergy (f.toLp 2 (volume : Measure (QuantumConfiguration N M))) =
      ∑ i : Fin M, ∑ a : Fin 3, ∫⁻ x : QuantumConfiguration N M,
        (‖fderiv ℝ (fun y => f y) x (toLp 2 ((0 : Configuration N), PiLp.single 2 (i, a) (1 : ℝ)))‖₊ : ℝ≥0∞) ^ 2 := by
  classical
  have hnorm (x : QuantumConfiguration N M) :
      (‖x.snd‖₊ : ℝ≥0∞) ^ 2 =
        ∑ i : Fin M, ∑ a : Fin 3, ENNReal.ofReal (x.snd (i, a) ^ 2) := by
    change ‖x.snd‖ₑ ^ 2 = _
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
      ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
    exact Fintype.sum_prod_type _
  have hderiv (i : Fin M) (a : Fin 3) :
      (∫⁻ x : QuantumConfiguration N M,
        (‖fderiv ℝ (fun y => f y) x (toLp 2 ((0 : Configuration N), PiLp.single 2 (i, a) (1 : ℝ)))‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x : QuantumConfiguration N M, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        ENNReal.ofReal (x.snd (i, a) ^ 2) * (‖(𝓕 f) x‖₊ : ℝ≥0∞) ^ 2 := by
    simpa only [WithLp.prod_inner_apply, WithLp.fst, WithLp.snd,
      inner_zero_right, zero_add, add_zero, EuclideanSpace.inner_single_right, map_one, one_mul,
      RCLike.conj_to_real] using
      Fourier.lintegral_fderiv_eq_fourier f (toLp 2 ((0 : Configuration N), PiLp.single 2 (i, a) (1 : ℝ)))
  unfold quantumNuclearKineticEnergy
  change (∫⁻ x : QuantumConfiguration N M, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
    (‖x.snd‖₊ : ℝ≥0∞) ^ 2 *
      (‖(𝓕 (f.toLp 2 (volume : Measure (QuantumConfiguration N M))) : QuantumState N M q) x‖₊ : ℝ≥0∞) ^ 2) = _
  rw [SchwartzMap.toLp_fourier_eq]
  calc
    _ = ∫⁻ x : QuantumConfiguration N M, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        (‖x.snd‖₊ : ℝ≥0∞) ^ 2 * (‖(𝓕 f) x‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [(𝓕 f).coeFn_toLp 2 (volume : Measure (QuantumConfiguration N M))] with x hx
      rw [hx]
    _ = ∫⁻ x : QuantumConfiguration N M, ∑ i : Fin M, ∑ a : Fin 3,
        ENNReal.ofReal ((2 * Real.pi) ^ 2) * ENNReal.ofReal (x.snd (i, a) ^ 2) *
          (‖(𝓕 f) x‖₊ : ℝ≥0∞) ^ 2 := by
      apply lintegral_congr
      intro x
      rw [hnorm]
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i : Fin M, ∑ a : Fin 3, ∫⁻ x : QuantumConfiguration N M,
        ENNReal.ofReal ((2 * Real.pi) ^ 2) * ENNReal.ofReal (x.snd (i, a) ^ 2) *
          (‖(𝓕 f) x‖₊ : ℝ≥0∞) ^ 2 := by
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [lintegral_finsetSum]
        intro a _
        fun_prop
      · intro i _
        fun_prop
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      exact (hderiv i a).symm

theorem quantumElectronKineticEnergy_schwartz_lt_top {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    quantumElectronKineticEnergy (f.toLp 2 volume) < ⊤ := by
  rw [quantumElectronKineticEnergy_schwartz]
  exact ENNReal.sum_lt_top.mpr (fun _ _ =>
    ENNReal.sum_lt_top.mpr (fun _ _ => schwartz_lintegral_fderiv_lt_top f _))

theorem quantumNuclearKineticEnergy_schwartz_lt_top {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    quantumNuclearKineticEnergy (f.toLp 2 volume) < ⊤ := by
  rw [quantumNuclearKineticEnergy_schwartz]
  exact ENNReal.sum_lt_top.mpr (fun _ _ =>
    ENNReal.sum_lt_top.mpr (fun _ _ => schwartz_lintegral_fderiv_lt_top f _))

end LiebThirring

end
