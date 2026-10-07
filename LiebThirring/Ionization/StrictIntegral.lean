/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Strict expectations against a probability density -/

public section
open MeasureTheory Filter
namespace LiebThirring

/-- A strict a.e. lower bound remains strict when integrated against a unit density. -/
theorem const_lt_integral_mul_of_ae_lt {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {d r : α → ℝ} {c : ℝ}
    (hd : Integrable d μ) (hdn : ∀ x, 0 ≤ d x) (hm : ∫ x, d x ∂μ = 1)
    (hi : Integrable (fun x => r x * d x) μ) (hs : ∀ᵐ x ∂μ, c < r x) :
    c < ∫ x, r x * d x ∂μ := by
  have hle : (fun x => c * d x) ≤ᵐ[μ] (fun x => r x * d x) :=
    hs.mono (fun x hx => mul_le_mul_of_nonneg_right hx.le (hdn x))
  have hcd : Integrable (fun x => c * d x) μ := hd.const_mul c
  have hmass : ∫ x, c * d x ∂μ = c := by rw [integral_const_mul, hm, mul_one]
  have hbound : c ≤ ∫ x, r x * d x ∂μ := by
    rw [← hmass]
    exact integral_mono_ae hcd hi hle
  apply lt_of_le_of_ne hbound
  intro he
  have he' : ∫ x, c * d x ∂μ = ∫ x, r x * d x ∂μ := hmass.trans he
  have hae := (integral_eq_iff_of_ae_le hcd hi hle).mp he'
  have hz : d =ᵐ[μ] 0 := by
    filter_upwards [hae, hs] with x hx hsx
    change d x = 0
    by_contra hn
    have hpos : 0 < d x := lt_of_le_of_ne (hdn x) (Ne.symm hn)
    have hgt := mul_lt_mul_of_pos_right hsx hpos
    rw [hx] at hgt
    exact lt_irrefl _ hgt
  have hz' : ∫ x, d x ∂μ = 0 := by rw [integral_congr_ae hz]; simp only [Pi.zero_apply, integral_zero]
  rw [hm] at hz'
  exact one_ne_zero hz'

/-- Summing strict lower bounds over a nonempty finite set gives a strict bound. -/
theorem card_lt_sum_of_one_lt {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (hs : s.Nonempty) (hf : ∀ i ∈ s, 1 < f i) : (s.card : ℝ) < ∑ i ∈ s, f i := by
  have hh := Finset.sum_lt_sum (s := s) (f := fun _ => (1 : ℝ))
    (fun i hi => (hf i hi).le) (by obtain ⟨i, hi⟩ := hs; exact ⟨i, hi, hf i hi⟩)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hh

end LiebThirring
end
