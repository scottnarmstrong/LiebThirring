/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.FourierCharacterization
public import LiebThirring.Sobolev.FormGraph
public import LiebThirring.Defs.KineticEnergy
import LiebThirring.Kinetic.DensityBasic
import LiebThirring.Sobolev.WeightedDensity

/-!
# Weak derivatives and the Fourier kinetic energy

This module identifies the Fourier kinetic energy with the sum of the squared L² norms of
all weak coordinate derivatives.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal FourierTransform

namespace LiebThirring.Sobolev

theorem nnnorm_frequencySymbol_smul_sq {N q : ℕ} (a : Fin N × Fin 3)
    (ξ : Configuration N) (v : SpinAmplitudes N q) :
    (‖frequencySymbol a ξ • v‖₊ : ℝ≥0∞) ^ 2 =
      ENNReal.ofReal ((2 * Real.pi) ^ 2) * ENNReal.ofReal (ξ a ^ 2) *
        (‖v‖₊ : ℝ≥0∞) ^ 2 := by
  rw [nnnorm_smul, ENNReal.coe_mul, mul_pow]
  change ‖frequencySymbol a ξ‖ₑ ^ 2 * ‖v‖ₑ ^ 2 = _
  rw [← ofReal_norm]
  congr 1
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hc : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, h2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [frequencySymbol, norm_mul, norm_mul, Complex.norm_I, mul_one, hc,
    Complex.norm_real, Real.norm_eq_abs,
    ← ENNReal.ofReal_pow (mul_nonneg (le_of_lt (mul_pos (by norm_num) Real.pi_pos)) (abs_nonneg _)),
    mul_pow, ENNReal.ofReal_mul (sq_nonneg _), sq_abs]

theorem weakDerivative_nnnorm_sq {N q : ℕ} {a : Fin N × Fin 3} {u g : State N q}
    (h : HasWeakDerivative a u g) :
    (‖g‖₊ : ℝ≥0∞) ^ 2 = ∫⁻ ξ : Configuration N,
      ENNReal.ofReal ((2 * Real.pi) ^ 2) * ENNReal.ofReal (ξ a ^ 2) *
        (‖(𝓕 u) ξ‖₊ : ℝ≥0∞) ^ 2 := by
  have hnorm : (‖𝓕 g‖₊ : ℝ≥0∞) = (‖g‖₊ : ℝ≥0∞) := by
    apply congrArg (fun z : ℝ≥0 ↦ (z : ℝ≥0∞))
    apply NNReal.eq
    exact Lp.norm_fourier_eq g
  rw [← hnorm, ← lintegral_state_norm_sq (𝓕 g)]
  apply lintegral_congr_ae
  filter_upwards [(hasWeakDerivative_iff_fourier_eq_symbol a u g).mp h] with ξ hξ
  rw [hξ, nnnorm_frequencySymbol_smul_sq]

theorem kineticEnergy_eq_sum_weakDerivative_nnnorm_sq {N q : ℕ}
    (u : State N q) (g : (Fin N × Fin 3) → State N q)
    (hg : ∀ a, HasWeakDerivative a u (g a)) :
    kineticEnergy u = ∑ a : Fin N × Fin 3, (‖g a‖₊ : ℝ≥0∞) ^ 2 := by
  rw [kineticEnergy]
  simp_rw [weakDerivative_nnnorm_sq (hg _)]
  rw [← lintegral_finsetSum]
  · apply lintegral_congr
    intro ξ
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    congr 1
    change ENNReal.ofReal ((2 * Real.pi) ^ 2) * ‖ξ‖ₑ ^ 2 = _
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg ξ),
      EuclideanSpace.real_norm_sq_eq,
      ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _), Finset.mul_sum]
  · intro a _
    exact ((measurable_const.mul
      ((PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 ↦ ℝ) a).measurable.pow_const 2
        |>.ennreal_ofReal)).mul
      ((Lp.stronglyMeasurable (𝓕 u)).measurable.nnnorm.coe_nnreal_ennreal.pow_const 2))

theorem exists_weakDerivatives_of_kineticEnergy_lt_top {N q : ℕ} (u : State N q)
    (hu : kineticEnergy u < ⊤) :
    ∃ g : (Fin N × Fin 3) → State N q, ∀ a, HasWeakDerivative a u (g a) := by
  let fu := 𝓕 u
  have hmem (a : Fin N × Fin 3) :
      MemLp (fun ξ : Configuration N ↦ frequencySymbol a ξ • fu ξ) 2 volume := by
    apply memLp_two_of_lintegral_norm_sq
    · exact (continuous_frequencySymbol a).aestronglyMeasurable.smul (Lp.aestronglyMeasurable fu)
    · apply lt_of_le_of_lt _ hu
      unfold kineticEnergy
      apply lintegral_mono
      intro ξ
      change (‖frequencySymbol a ξ • (𝓕 u) ξ‖₊ : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
          (‖(𝓕 u) ξ‖₊ : ℝ≥0∞) ^ 2
      rw [nnnorm_frequencySymbol_smul_sq]
      gcongr
      change ENNReal.ofReal (ξ a ^ 2) ≤ ‖ξ‖ₑ ^ 2
      rw [← sq_abs (ξ a), ENNReal.ofReal_pow (abs_nonneg (ξ a)), ← ofReal_norm]
      apply ENNReal.pow_le_pow_left
      apply ENNReal.ofReal_le_ofReal
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ a
  let multiplier (a : Fin N × Fin 3) : State N q :=
    (hmem a).toLp (fun ξ ↦ frequencySymbol a ξ • fu ξ)
  let g (a : Fin N × Fin 3) : State N q :=
    (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)).symm (multiplier a)
  refine ⟨g, fun a ↦ (hasWeakDerivative_iff_fourier_eq_symbol a u (g a)).mpr ?_⟩
  have hfourier : 𝓕 (g a) = multiplier a := by
    exact (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)).apply_symm_apply _
  filter_upwards [(hmem a).coeFn_toLp] with ξ hξ
  rw [hfourier]
  exact hξ

theorem kineticEnergy_lt_top_iff_exists_weakDerivatives {N q : ℕ} (u : State N q) :
    kineticEnergy u < ⊤ ↔
      ∃ g : (Fin N × Fin 3) → State N q, ∀ a, HasWeakDerivative a u (g a) := by
  constructor
  · exact exists_weakDerivatives_of_kineticEnergy_lt_top u
  · rintro ⟨g, hg⟩
    rw [kineticEnergy_eq_sum_weakDerivative_nnnorm_sq u g hg]
    exact ENNReal.sum_lt_top.mpr fun a _ ↦
      ENNReal.pow_lt_top (ENNReal.coe_lt_top : (‖g a‖₊ : ℝ≥0∞) < ⊤)

theorem kineticEnergy_eq_formGraph_derivatives {N q : ℕ} (v : formGraph N q) :
    kineticEnergy ((v : FormGraphAmbient N q) none) =
      ∑ a : Fin N × Fin 3,
        (‖(v : FormGraphAmbient N q) (some a)‖₊ : ℝ≥0∞) ^ 2 := by
  apply kineticEnergy_eq_sum_weakDerivative_nnnorm_sq
  intro a
  exact (mem_formGraph.mp v.property) a

theorem kineticEnergy_toReal_eq_sum_weakDerivative_norm_sq {N q : ℕ}
    (u : State N q) (g : (Fin N × Fin 3) → State N q)
    (hg : ∀ a, HasWeakDerivative a u (g a)) :
    (kineticEnergy u).toReal = ∑ a : Fin N × Fin 3, ‖g a‖ ^ 2 := by
  rw [kineticEnergy_eq_sum_weakDerivative_nnnorm_sq u g hg,
    ENNReal.toReal_sum (fun _ _ ↦ ENNReal.pow_ne_top ENNReal.coe_ne_top)]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.toReal_pow]
  norm_cast

theorem formGraph_norm_sq_eq_mass_add_kineticEnergy {N q : ℕ} (v : formGraph N q) :
    ‖v‖ ^ 2 = ‖(v : FormGraphAmbient N q) none‖ ^ 2 +
      (kineticEnergy ((v : FormGraphAmbient N q) none)).toReal := by
  rw [formGraph_norm_sq]
  congr 1
  symm
  apply kineticEnergy_toReal_eq_sum_weakDerivative_norm_sq
  intro a
  exact (mem_formGraph.mp v.property) a

end LiebThirring.Sobolev

end
