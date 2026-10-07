/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormIntegral

/-! # Algebra of absolutely integrable weighted L² inner products -/

public section
open MeasureTheory
open scoped ComplexConjugate ENNReal NNReal
namespace LiebThirring
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Additivity in the second slot of an integrable weighted L² pairing. -/
theorem integral_mul_inner_add_right (a : α → ℂ) (f g h : Lp E 2 μ)
    (hfg : Integrable (fun x => a x * inner ℂ (f x) (g x)) μ)
    (hfh : Integrable (fun x => a x * inner ℂ (f x) (h x)) μ) :
    (∫ x, a x * inner ℂ (f x) ((g + h) x) ∂μ) =
      (∫ x, a x * inner ℂ (f x) (g x) ∂μ) +
        (∫ x, a x * inner ℂ (f x) (h x) ∂μ) := by
  rw [← integral_add hfg hfh]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add g h] with x hx
  dsimp only [Pi.add_apply] at hx ⊢
  rw [hx, inner_add_right, mul_add]

/-- Linearity in the second slot of a weighted L² pairing. -/
theorem integral_mul_inner_smul_right (a : α → ℂ) (c : ℂ) (f g : Lp E 2 μ) :
    (∫ x, a x * inner ℂ (f x) ((c • g) x) ∂μ) =
      c * (∫ x, a x * inner ℂ (f x) (g x) ∂μ) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c g] with x hx
  dsimp only [Pi.smul_apply] at hx ⊢
  rw [hx, inner_smul_right]
  ring

/-- Conjugation of a weighted inner-product pairing with real coefficients. -/
theorem integral_ofReal_mul_inner_conj (a : α → ℝ) (f g : Lp E 2 μ) :
    conj (∫ x, (a x : ℂ) * inner ℂ (f x) (g x) ∂μ) =
      ∫ x, (a x : ℂ) * inner ℂ (g x) (f x) ∂μ := by
  rw [← integral_conj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [map_mul, Complex.conj_ofReal, inner_conj_symm]

end LiebThirring
end
