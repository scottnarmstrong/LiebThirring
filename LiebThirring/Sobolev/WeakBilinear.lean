/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.FourierCharacterization

/-! # The polarized Dirichlet identity for finite-energy states -/

public section

open MeasureTheory
open scoped FourierTransform ComplexConjugate

namespace LiebThirring.Sobolev

/-- The derivative symbol has the physical squared magnitude. -/
theorem star_mul_frequencySymbol {N : ℕ} (a : Fin N × Fin 3) (ξ : Configuration N) :
    star (frequencySymbol a ξ) * frequencySymbol a ξ =
      (((2 * Real.pi) ^ 2 * (ξ a) ^ 2 : ℝ) : ℂ) := by
  rw [star_frequencySymbol]
  simp only [frequencySymbol, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  calc
    _ = -(2 * (Real.pi : ℂ) * Complex.I * (ξ a : ℂ)) ^ 2 := by ring
    _ = _ := by
      rw [mul_pow, mul_pow, mul_pow, Complex.I_sq]
      ring

/-- A pointwise coordinate sum of polarized derivative symbols is the radial weight. -/
theorem sum_inner_frequencySymbol {N q : ℕ} (ξ : Configuration N)
    (v u : SpinAmplitudes N q) :
    (∑ a : Fin N × Fin 3, inner ℂ (frequencySymbol a ξ • v) (frequencySymbol a ξ • u)) =
      (((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * inner ℂ v u := by
  have hterm (a : Fin N × Fin 3) :
      inner ℂ (frequencySymbol a ξ • v) (frequencySymbol a ξ • u) =
        (((2 * Real.pi) ^ 2 * (ξ a) ^ 2 : ℝ) : ℂ) * inner ℂ v u := by
    rw [inner_smul_left, inner_smul_right, ← mul_assoc, starRingEnd_apply,
      star_mul_frequencySymbol]
  simp only [hterm]
  rw [← Finset.sum_mul]
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Complex.ofReal_sum]

/-- Weak derivatives identify the radial Fourier integrand with a finite sum of L² pairings. -/
theorem fourier_inner_eq_sum_weakDerivatives_ae {N q : ℕ} (u v : State N q)
    (du dv : (Fin N × Fin 3) → State N q)
    (hu : ∀ a, HasWeakDerivative a u (du a)) (hv : ∀ a, HasWeakDerivative a v (dv a)) :
    ∀ᵐ ξ, (((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * inner ℂ ((𝓕 v) ξ) ((𝓕 u) ξ) =
      ∑ a : Fin N × Fin 3, inner ℂ ((𝓕 (dv a)) ξ) ((𝓕 (du a)) ξ) := by
  have hu' : ∀ᵐ ξ, ∀ a, (𝓕 (du a)) ξ = frequencySymbol a ξ • (𝓕 u) ξ := by
    rw [ae_all_iff]
    exact fun a => (hasWeakDerivative_iff_fourier_eq_symbol a u (du a)).mp (hu a)
  have hv' : ∀ᵐ ξ, ∀ a, (𝓕 (dv a)) ξ = frequencySymbol a ξ • (𝓕 v) ξ := by
    rw [ae_all_iff]
    exact fun a => (hasWeakDerivative_iff_fourier_eq_symbol a v (dv a)).mp (hv a)
  filter_upwards [hu', hv'] with ξ huξ hvξ
  simp only [huξ, hvξ]
  exact (sum_inner_frequencySymbol ξ ((𝓕 v) ξ) ((𝓕 u) ξ)).symm

/-- The polarized Fourier kinetic integrand is absolutely integrable on the weak graph domain. -/
theorem integrable_fourier_inner_of_weakDerivatives {N q : ℕ} (u v : State N q)
    (du dv : (Fin N × Fin 3) → State N q)
    (hu : ∀ a, HasWeakDerivative a u (du a)) (hv : ∀ a, HasWeakDerivative a v (dv a)) :
    Integrable (fun ξ => (((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
      inner ℂ ((𝓕 v) ξ) ((𝓕 u) ξ)) := by
  exact ((integrable_finsetSum Finset.univ (fun a _ =>
    L2.integrable_inner (𝕜 := ℂ) (𝓕 (dv a)) (𝓕 (du a)))).congr
      (by
        filter_upwards [fourier_inner_eq_sum_weakDerivatives_ae u v du dv hu hv] with ξ hξ
        exact hξ.symm))

/-- The physical Fourier kinetic pairing is the sum of weak derivative L² pairings. -/
theorem integral_fourier_inner_eq_sum_weakDerivatives {N q : ℕ} (u v : State N q)
    (du dv : (Fin N × Fin 3) → State N q)
    (hu : ∀ a, HasWeakDerivative a u (du a)) (hv : ∀ a, HasWeakDerivative a v (dv a)) :
    (∫ ξ, (((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * inner ℂ ((𝓕 v) ξ) ((𝓕 u) ξ)) =
      ∑ a : Fin N × Fin 3, inner ℂ (dv a) (du a) := by
  rw [integral_congr_ae (fourier_inner_eq_sum_weakDerivatives_ae u v du dv hu hv),
    integral_finsetSum Finset.univ (fun a _ =>
      L2.integrable_inner (𝕜 := ℂ) (𝓕 (dv a)) (𝓕 (du a)))]
  simp only [← L2.inner_def, Lp.inner_fourier_eq]

end LiebThirring.Sobolev

end
