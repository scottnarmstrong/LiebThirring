/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.WeakDerivative
public import LiebThirring.Fourier.Schwartz
public import LiebThirring.Sobolev.SchwartzFundamental

/-!
# Fourier characterization of weak coordinate derivatives

With the configuration carrier and the physical `2π` Fourier convention.
-/

public section

open MeasureTheory LineDeriv
open scoped SchwartzMap FourierTransform ContDiff ComplexConjugate

namespace LiebThirring.Sobolev

/-- The Fourier symbol of a coordinate derivative for the physical phase convention. -/
@[expose] noncomputable def frequencySymbol {N : ℕ} (a : Fin N × Fin 3)
    (ξ : Configuration N) : ℂ :=
  (2 * Real.pi : ℂ) * Complex.I * (ξ a : ℂ)

/-- The derivative symbol is continuous in frequency. -/
theorem continuous_frequencySymbol {N : ℕ} (a : Fin N × Fin 3) :
    Continuous (frequencySymbol a) := by
  exact continuous_const.mul (Complex.continuous_ofReal.comp
    (PiLp.continuous_apply 2 (fun _ : Fin N × Fin 3 => ℝ) a))

/-- Pairing a Schwartz function with an L² state agrees with the Hilbert inner product. -/
theorem integral_inner_schwartz_state {N q : ℕ}
    (η : 𝓢(Configuration N, SpinAmplitudes N q)) (u : State N q) :
    (∫ x, inner ℂ (η x) (u x)) = inner ℂ (η.toLp 2 volume) u := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [η.coeFn_toLp 2 volume] with x hx
  rw [hx]

/-- Plancherel for a Schwartz test against an arbitrary L² state. -/
theorem integral_inner_fourier_schwartz_state {N q : ℕ}
    (η : 𝓢(Configuration N, SpinAmplitudes N q)) (u : State N q) :
    (∫ ξ, inner ℂ ((𝓕 η) ξ) ((𝓕 u) ξ)) = ∫ x, inner ℂ (η x) (u x) := by
  rw [integral_inner_schwartz_state, integral_inner_schwartz_state,
    ← SchwartzMap.toLp_fourier_eq, Lp.inner_fourier_eq]

/-- The Fourier transform of the Schwartz coordinate derivative has the expected symbol. -/
theorem fourier_lineDeriv_coordinate {N q : ℕ}
    (η : 𝓢(Configuration N, SpinAmplitudes N q)) (a : Fin N × Fin 3)
    (ξ : Configuration N) :
    (𝓕 (lineDerivOp (coordinateVector a) η)) ξ = frequencySymbol a ξ • (𝓕 η) ξ := by
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  have hg : (fun ξ : Configuration N => inner ℝ ξ (coordinateVector a)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (coordinateVector a)).hasTemperateGrowth
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg]
  simp only [coordinateVector, EuclideanSpace.inner_basisFun_real, frequencySymbol]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), ← mul_smul]
  ext s
  simp only [PiLp.smul_apply]
  simp only [SchwartzMap.fourier_coe]
  rfl

/-- The derivative symbol is purely imaginary. -/
theorem star_frequencySymbol {N : ℕ} (a : Fin N × Fin 3) (ξ : Configuration N) :
    star (frequencySymbol a ξ) = -frequencySymbol a ξ := by
  simp only [frequencySymbol, star_mul, Complex.star_def, Complex.conj_ofReal, map_ofNat,
    Complex.conj_I]
  ring

/-- Moving the derivative symbol across the complex inner product changes the sign. -/
theorem inner_frequencySymbol {N q : ℕ} (a : Fin N × Fin 3) (ξ : Configuration N)
    (v w : SpinAmplitudes N q) :
    inner ℂ (frequencySymbol a ξ • v) w = -inner ℂ v (frequencySymbol a ξ • w) := by
  rw [inner_smul_left, inner_smul_right]
  change star (frequencySymbol a ξ) * inner ℂ v w = -(frequencySymbol a ξ * inner ℂ v w)
  rw [star_frequencySymbol, neg_mul]

/-- Schwartz weak identities imply equality of Fourier inner pairings. -/
theorem integral_symbol_eq_of_schwartz_tests {N q : ℕ} (a : Fin N × Fin 3)
    (u g : State N q)
    (h : ∀ η : 𝓢(Configuration N, SpinAmplitudes N q),
      (∫ x, inner ℂ (η x) (g x)) =
        -(∫ x, inner ℂ ((lineDerivOp (coordinateVector a) η) x) (u x)))
    (τ : 𝓢(Configuration N, SpinAmplitudes N q)) :
      (∫ ξ, inner ℂ (τ ξ) ((𝓕 g) ξ)) =
        ∫ ξ, inner ℂ (τ ξ) (frequencySymbol a ξ • (𝓕 u) ξ) := by
  calc
    _ = ∫ x, inner ℂ ((𝓕⁻ τ) x) (g x) := by
      simpa only [FourierTransform.fourier_fourierInv_eq] using
        integral_inner_fourier_schwartz_state (𝓕⁻ τ) g
    _ = -(∫ x, inner ℂ ((lineDerivOp (coordinateVector a) (𝓕⁻ τ)) x) (u x)) := h _
    _ = -(∫ ξ, inner ℂ ((𝓕 (lineDerivOp (coordinateVector a) (𝓕⁻ τ))) ξ) ((𝓕 u) ξ)) := by
      rw [integral_inner_fourier_schwartz_state]
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [fourier_lineDeriv_coordinate, FourierTransform.fourier_fourierInv_eq,
        inner_frequencySymbol, neg_neg]

/-- Schwartz weak test identities force the Fourier multiplier identity almost everywhere. -/
theorem fourier_eq_symbol_of_schwartz_tests {N q : ℕ} (a : Fin N × Fin 3)
    (u g : State N q)
    (h : ∀ η : 𝓢(Configuration N, SpinAmplitudes N q),
      (∫ x, inner ℂ (η x) (g x)) =
        -(∫ x, inner ℂ ((lineDerivOp (coordinateVector a) η) x) (u x))) :
    ∀ᵐ ξ, (𝓕 g) ξ = frequencySymbol a ξ • (𝓕 u) ξ := by
  have hlu : LocallyIntegrable (fun ξ => frequencySymbol a ξ • (𝓕 u) ξ) :=
    ((Lp.memLp (𝓕 u)).locallyIntegrable (by norm_num)).continuous_smul
      (continuous_frequencySymbol a)
  have hlg : LocallyIntegrable (fun ξ => (𝓕 g) ξ) :=
    (Lp.memLp (𝓕 g)).locallyIntegrable (by norm_num)
  exact ae_eq_of_schwartz_inner_eq hlg hlu (integral_symbol_eq_of_schwartz_tests a u g h)

/-- The Fourier multiplier identity implies every Schwartz weak derivative identity. -/
theorem schwartz_tests_of_fourier_eq_symbol {N q : ℕ} (a : Fin N × Fin 3)
    (u g : State N q) (h : ∀ᵐ ξ, (𝓕 g) ξ = frequencySymbol a ξ • (𝓕 u) ξ)
    (η : 𝓢(Configuration N, SpinAmplitudes N q)) :
    (∫ x, inner ℂ (η x) (g x)) =
      -(∫ x, inner ℂ ((lineDerivOp (coordinateVector a) η) x) (u x)) := by
  calc
    _ = ∫ ξ, inner ℂ ((𝓕 η) ξ) ((𝓕 g) ξ) :=
      (integral_inner_fourier_schwartz_state η g).symm
    _ = ∫ ξ, inner ℂ ((𝓕 η) ξ) (frequencySymbol a ξ • (𝓕 u) ξ) := by
      apply integral_congr_ae
      filter_upwards [h] with ξ hξ
      rw [hξ]
    _ = -(∫ ξ, inner ℂ ((𝓕 (lineDerivOp (coordinateVector a) η)) ξ) ((𝓕 u) ξ)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [fourier_lineDeriv_coordinate, inner_frequencySymbol, neg_neg]
    _ = _ := by rw [integral_inner_fourier_schwartz_state]

/-- The Fourier multiplier identity implies the compact smooth weak derivative identity. -/
theorem hasWeakDerivative_of_fourier_eq_symbol {N q : ℕ} (a : Fin N × Fin 3)
    (u g : State N q) (h : ∀ᵐ ξ, (𝓕 g) ξ = frequencySymbol a ξ • (𝓕 u) ξ) :
    HasWeakDerivative a u g := by
  intro η hηK hη
  let τ := hηK.toSchwartzMap hη
  have ht : (τ : Configuration N → SpinAmplitudes N q) = η := by
    funext x
    exact HasCompactSupport.toSchwartzMap_toFun _ _ x
  have hs := schwartz_tests_of_fourier_eq_symbol a u g h τ
  simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, ht] using hs

end LiebThirring.Sobolev

end
