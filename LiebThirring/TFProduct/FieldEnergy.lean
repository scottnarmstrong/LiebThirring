/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.FieldParseval

/-!
# Weighted energy assembly for Hilbert-valued L² fields

A scalar weighted form identity for every fiber coefficient is summed over a
complete fiber basis.  Nonnegativity supplies Tonelli summability of the double
series.
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace

namespace LiebThirring.TFProduct

variable {X H ι κ A : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure X) [Countable κ] [Fintype A]

/-- Assemble nonnegative scalar weighted identities into a Hilbert-valued
field identity. -/
theorem hasSum_weighted_fieldEnergy
    (B : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (C : HilbertBasis κ ℂ H)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (u : Lp H 2 μ) (g : A → Lp H 2 μ)
    (hcoefficient : ∀ j, HasSum
      (fun i => w i * ‖inner ℂ (B i) (fieldCoefficient μ (C j) u)‖ ^ 2)
      (∑ a : A, ‖fieldCoefficient μ (C j) (g a)‖ ^ 2)) :
    HasSum (fun p : ι × κ =>
      w p.1 * ‖inner ℂ (fieldTensor μ (B p.1) (C p.2)) u‖ ^ 2)
      (∑ a : A, ‖g a‖ ^ 2) := by
  let f : κ × ι → ℝ := fun p =>
    w p.2 * ‖inner ℂ (B p.2) (fieldCoefficient μ (C p.1) u)‖ ^ 2
  let G : κ → ℝ := fun j => ∑ a : A, ‖fieldCoefficient μ (C j) (g a)‖ ^ 2
  have houter : HasSum G (∑ a : A, ‖g a‖ ^ 2) := by
    simpa only [G] using
      (hasSum_sum fun a _ => hasSum_norm_sq_fieldCoefficient μ B C (g a))
  have hfiber (j : κ) : HasSum (fun i => f (j, i)) (G j) := by
    simpa only [f, G] using hcoefficient j
  have hnonneg : ∀ p, 0 ≤ f p := by
    intro p
    exact mul_nonneg (hw p.2) (sq_nonneg _)
  have hdoubleSummable : Summable f := by
    apply (summable_prod_of_nonneg hnonneg).mpr
    refine ⟨fun j => (hfiber j).summable, ?_⟩
    have heq : (fun j => ∑' i, f (j, i)) = G := by
      funext j
      exact (hfiber j).tsum_eq
    rw [heq]
    exact houter.summable
  have hdouble : HasSum f (∑ a : A, ‖g a‖ ^ 2) := by
    have h := hdoubleSummable.hasSum
    have hsummed : HasSum G (∑' p, f p) := h.prod_fiberwise hfiber
    rw [hsummed.unique houter] at h
    exact h
  have hreindexed : HasSum (fun p : ι × κ => f (p.2, p.1))
      (∑ a : A, ‖g a‖ ^ 2) :=
    ((Equiv.prodComm ι κ).hasSum_iff (f := f)).mpr hdouble
  simpa only [f, inner_fieldTensor] using hreindexed

end LiebThirring.TFProduct

end
