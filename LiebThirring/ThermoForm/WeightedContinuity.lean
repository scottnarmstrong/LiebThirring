/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.Algebra
import LiebThirring.Variational.FormIntegralBounds

/-! # Continuity estimates for weighted quadratic expectations

Argument thermodynamic confined form estimates. Polarized Cauchy–Schwarz controls differences
of expectations, and applies to both kinetic and Coulomb weights.
-/

public section

open MeasureTheory
open Filter
open scoped ENNReal NNReal Topology

namespace LiebThirring

theorem abs_lintegral_weight_sq_sub_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] {μ : Measure α}
    (p : α → ℝ≥0∞) (hp : AEMeasurable p μ) (u v : Lp E 2 μ)
    (hu : (∫⁻ x, p x * (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤)
    (hv : (∫⁻ x, p x * (‖v x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤)
    (hd : (∫⁻ x, p x * (‖(u - v) x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤) :
    |(∫⁻ x, p x * (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal -
      (∫⁻ x, p x * (‖v x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal| ≤
      Real.sqrt (∫⁻ x, p x * (‖(u - v) x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal *
        (Real.sqrt (∫⁻ x, p x * (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal +
          Real.sqrt (∫⁻ x, p x * (‖v x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal) := by
  have huu := integrable_weight_inner hp (Lp.aestronglyMeasurable u)
    (Lp.aestronglyMeasurable u) hu hu
  have hvv := integrable_weight_inner hp (Lp.aestronglyMeasurable v)
    (Lp.aestronglyMeasurable v) hv hv
  have hdu := integrable_weight_inner hp (Lp.aestronglyMeasurable (u - v))
    (Lp.aestronglyMeasurable u) hd hu
  have hvd := integrable_weight_inner hp (Lp.aestronglyMeasurable v)
    (Lp.aestronglyMeasurable (u - v)) hv hd
  have he :
      (((∫⁻ x, p x * (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal -
        (∫⁻ x, p x * (‖v x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal : ℝ) : ℂ) =
      (∫ x, ((p x).toReal : ℂ) * inner ℂ ((u - v) x) (u x) ∂μ) +
        ∫ x, ((p x).toReal : ℂ) * inner ℂ (v x) ((u - v) x) ∂μ := by
    rw [Complex.ofReal_sub,
      ← integral_weight_inner_self hp (Lp.aestronglyMeasurable u) hu,
      ← integral_weight_inner_self hp (Lp.aestronglyMeasurable v) hv,
      ← integral_sub huu hvv, ← integral_add hdu hvd]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub u v] with x hx
    dsimp only [Pi.sub_apply, Pi.add_apply] at hx ⊢
    rw [hx, inner_sub_left, inner_sub_right]
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, he]
  calc
    _ ≤ ‖∫ x, ((p x).toReal : ℂ) * inner ℂ ((u - v) x) (u x) ∂μ‖ +
        ‖∫ x, ((p x).toReal : ℂ) * inner ℂ (v x) ((u - v) x) ∂μ‖ :=
      norm_add_le _ _
    _ ≤ _ := (add_le_add
      (norm_integral_weight_inner_le hp (Lp.aestronglyMeasurable (u - v))
        (Lp.aestronglyMeasurable u) hd hu)
      (norm_integral_weight_inner_le hp (Lp.aestronglyMeasurable v)
        (Lp.aestronglyMeasurable (u - v)) hv hd)).trans_eq (by ring)

theorem tendsto_lintegral_weight_sq_of_difference {α E β : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] {μ : Measure α} {l : Filter β}
    (p : α → ℝ≥0∞) (hp : Measurable p) (u : Lp E 2 μ) (v : β → Lp E 2 μ)
    (hu : (∫⁻ x, p x * (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤)
    (hv : ∀ n, (∫⁻ x, p x * (‖v n x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤)
    (hd : ∀ n, (∫⁻ x, p x * (‖(v n - u) x‖₊ : ℝ≥0∞) ^ 2 ∂μ) < ⊤)
    (hlim : Tendsto (fun n =>
      (∫⁻ x, p x * (‖(v n - u) x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal) l (𝓝 0)) :
    Tendsto (fun n => (∫⁻ x, p x * (‖v n x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal)
      l (𝓝 (∫⁻ x, p x * (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal) := by
  let W (f : Lp E 2 μ) := ∫⁻ x, p x * (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ
  have htri (n : β) : (W (v n)).toReal ≤ 2 * ((W (v n - u)).toReal + (W u).toReal) := by
    have h := lintegral_weight_add_sq_le p hp (v n - u) u
    rw [sub_add_cancel] at h
    have hfin : 2 * (W (v n - u) + W u) < ⊤ :=
      ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hd n, hu⟩)
    have ht := ENNReal.toReal_mono hfin.ne h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_add (hd n).ne hu.ne] at ht
  have hbound (n : β) : |(W (v n)).toReal - (W u).toReal| ≤
      Real.sqrt (W (v n - u)).toReal *
        (Real.sqrt (2 * ((W (v n - u)).toReal + (W u).toReal)) + Real.sqrt (W u).toReal) := by
    exact (abs_lintegral_weight_sq_sub_le p hp.aemeasurable (v n) u (hv n) hu (hd n)).trans
      (mul_le_mul_of_nonneg_left (add_le_add (Real.sqrt_le_sqrt (htri n)) le_rfl)
        (Real.sqrt_nonneg _))
  have hright : Tendsto (fun n => Real.sqrt (W (v n - u)).toReal *
      (Real.sqrt (2 * ((W (v n - u)).toReal + (W u).toReal)) + Real.sqrt (W u).toReal))
      l (𝓝 0) := by
    have h := hlim.sqrt.mul (((hlim.add_const (W u).toReal).const_mul 2).sqrt.add_const
      (Real.sqrt (W u).toReal))
    simpa only [Real.sqrt_zero, zero_mul] using h
  have habs : Tendsto (fun n => |(W (v n)).toReal - (W u).toReal|) l (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) hbound hright
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr (by
    simpa only [Real.norm_eq_abs] using habs)

end LiebThirring

end
