/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Conditional probabilities on a countable partition

The reference probability supplies the conditional law on a null event. The
weighted conditional law is always the literal restricted original measure.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped ENNReal
namespace LiebThirring.TFSectors

variable {X : Type*} [MeasurableSpace X]

/-- Normalize a restricted measure, with an explicit reference on null events. -/
noncomputable def conditionalMeasure (μ : Measure X) (s : Set X) (σ : Measure X) :
    Measure X :=
  if μ s = 0 then σ else (μ s)⁻¹ • μ.restrict s

theorem isProbabilityMeasure_conditionalMeasure (μ : Measure X)
    [IsFiniteMeasure μ] (s : Set X) (σ : Measure X) [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (conditionalMeasure μ s σ) := by
  by_cases hs : μ s = 0
  · simpa [conditionalMeasure, hs] using (inferInstance : IsProbabilityMeasure σ)
  · constructor
    simp only [conditionalMeasure, hs, ite_false, Measure.smul_apply,
      Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hs (measure_ne_top μ s)

theorem measure_smul_conditionalMeasure (μ : Measure X) [IsFiniteMeasure μ]
    (s : Set X) (σ : Measure X) :
    μ s • conditionalMeasure μ s σ = μ.restrict s := by
  by_cases hs : μ s = 0
  · simp [conditionalMeasure, hs, Measure.restrict_eq_zero.mpr hs]
  · simp only [conditionalMeasure, hs, ite_false, smul_smul]
    rw [ENNReal.mul_inv_cancel hs (measure_ne_top μ s), one_smul]

theorem weighted_lintegral_conditionalMeasure (μ : Measure X) [IsFiniteMeasure μ]
    (s : Set X) (σ : Measure X) (f : X → ℝ≥0∞) :
    (μ s).toReal * (∫⁻ x, f x ∂conditionalMeasure μ s σ).toReal =
      (∫⁻ x in s, f x ∂μ).toReal := by
  rw [← measure_smul_conditionalMeasure μ s σ, lintegral_smul_measure,
    smul_eq_mul, ENNReal.toReal_mul]

/-- Nonnegative expectations with finite total integral decompose in real values. -/
theorem hasSum_weighted_conditional_lintegral {I : Type*} [Countable I]
    (μ : Measure X) [IsFiniteMeasure μ] (s : I → Set X) (σ : I → Measure X)
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hu : (⋃ i, s i) = univ) (f : X → ℝ≥0∞) (hf : (∫⁻ x, f x ∂μ) ≠ ⊤) :
    HasSum (fun i => (μ (s i)).toReal *
      (∫⁻ x, f x ∂conditionalMeasure μ (s i) (σ i)).toReal)
      (∫⁻ x, f x ∂μ).toReal := by
  have heq : (∑' i, ∫⁻ x in s i, f x ∂μ) = ∫⁻ x, f x ∂μ := by
    simpa [hu] using (lintegral_iUnion (μ := μ) hm hd f).symm
  have hfinite : (∑' i, ∫⁻ x in s i, f x ∂μ) ≠ ⊤ := by rwa [heq]
  simp_rw [weighted_lintegral_conditionalMeasure]
  rw [← heq, ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hfinite)]
  exact (ENNReal.summable_toReal hfinite).hasSum

/-- Probabilities of a countable measurable partition sum to one. -/
theorem hasSum_partition_probability {I : Type*} [Countable I]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : I → Set X)
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hu : (⋃ i, s i) = univ) : HasSum (fun i => (μ (s i)).toReal) 1 := by
  have hi := hasSum_integral_iUnion (μ := μ) (f := fun _ : X => (1 : ℝ)) hm hd
    (by simp [hu])
  simpa [hu, integral_const, measureReal_def] using hi

theorem ae_conditionalMeasure (μ : Measure X) (s : Set X) (σ : Measure X)
    {P : X → Prop} (hσ : ∀ᵐ x ∂σ, P x) (hμ : ∀ᵐ x ∂μ.restrict s, P x) :
    ∀ᵐ x ∂conditionalMeasure μ s σ, P x := by
  unfold conditionalMeasure
  split
  · exact hσ
  · exact Measure.ae_smul_measure hμ _

theorem lintegral_conditionalMeasure_ne_top (μ : Measure X) [IsFiniteMeasure μ]
    (s : Set X) (σ : Measure X) (f : X → ℝ≥0∞)
    (hσ : (∫⁻ x, f x ∂σ) ≠ ⊤) (hμ : (∫⁻ x, f x ∂μ) ≠ ⊤) :
    (∫⁻ x, f x ∂conditionalMeasure μ s σ) ≠ ⊤ := by
  unfold conditionalMeasure
  split
  · exact hσ
  next hs =>
    rw [lintegral_smul_measure, smul_eq_mul]
    exact ENNReal.mul_ne_top (by simpa using hs)
      (ne_top_of_le_ne_top hμ (lintegral_mono' Measure.restrict_le_self le_rfl))

end LiebThirring.TFSectors
end
