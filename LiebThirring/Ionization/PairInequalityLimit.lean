/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.WeightedRadial
public import LiebThirring.Kinetic.DensityBasic

/-!
# Passage to the unbounded pair weight

Fixed-cutoff integrability and estimates are inputs from cutoff pair estimate.
The limiting integrability is proved by monotone convergence, without a spatial
moment assumption. Real division assigns zero on the collision set.
-/

public section
open MeasureTheory Filter
open scoped Topology

namespace LiebThirring

/-- The unordered pairs of particle labels, using the `i < j` convention. -/
@[expose] def ionizationPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 < p.2)

/-- The regularized pair ratio. -/
@[expose] noncomputable def ionizationPairCutoff {N : ℕ} (ε : ℝ)
    (i j : Fin N) (X : Configuration N) : ℝ :=
  (ionizationWeight ε ‖particlePosition X i‖ +
    ionizationWeight ε ‖particlePosition X j‖) /
      ‖particlePosition X i - particlePosition X j‖

/-- The limiting pair ratio. -/
@[expose] noncomputable def ionizationPairRatio {N : ℕ}
    (i j : Fin N) (X : Configuration N) : ℝ :=
  (‖particlePosition X i‖ + ‖particlePosition X j‖) /
      ‖particlePosition X i - particlePosition X j‖

theorem ionizationPairCutoff_nonneg {N : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (i j : Fin N) (X : Configuration N) : 0 ≤ ionizationPairCutoff ε i j X :=
  div_nonneg (add_nonneg (ionizationWeight_nonneg hε (norm_nonneg _))
    (ionizationWeight_nonneg hε (norm_nonneg _))) (norm_nonneg _)

theorem ionizationPairRatio_nonneg {N : ℕ} (i j : Fin N) (X : Configuration N) :
    0 ≤ ionizationPairRatio i j X :=
  div_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

theorem measurable_ionizationPairRatio {N : ℕ} (i j : Fin N) :
    Measurable (ionizationPairRatio i j) :=
  ((measurable_particlePosition i).norm.add (measurable_particlePosition j).norm).div
    ((measurable_particlePosition i).sub (measurable_particlePosition j)).norm

/-- The reciprocal regularization weights increase along εₙ=1/(n+1). -/
theorem monotone_ionizationWeight_sequence {r : ℝ} (hr : 0 ≤ r) :
    Monotone (fun n : ℕ => ionizationWeight (1 / ((n : ℝ) + 1)) r) := by
  intro m n hmn
  unfold ionizationWeight
  apply div_le_div_of_nonneg_left hr (by positivity)
  have he : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    simpa only [add_comm] using add_le_add_right (Nat.cast_le.mpr hmn : (m : ℝ) ≤ n) 1
  simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_right he hr) 1

theorem tendsto_ionizationWeight_sequence (r : ℝ) :
    Tendsto (fun n : ℕ => ionizationWeight (1 / ((n : ℝ) + 1)) r)
      atTop (𝓝 r) := by
  have hd := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const r)
  convert (tendsto_const_nhds (x := r)).div hd
    (by norm_num : (1 : ℝ) + 0 * r ≠ 0) using 1
  · funext n; rfl
  · simp only [zero_mul, add_zero, div_one]

/-- Bounded monotone integrals establish integrability of the limiting function. -/
theorem integrable_limit_of_monotone_integral_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ} {B : ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hm : AEStronglyMeasurable F μ)
    (hn : ∀ n x, 0 ≤ f n x) (hF : ∀ x, 0 ≤ F x)
    (hmono : ∀ x, Monotone (fun n => f n x))
    (ht : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x)))
    (hb : ∀ n, ∫ x, f n x ∂μ ≤ B) :
    Integrable F μ ∧ ∫ x, F x ∂μ ≤ B := by
  have ht' := lintegral_tendsto_of_tendsto_of_monotone
    (fun n => ENNReal.measurable_ofReal.comp_aemeasurable (hf n).1.aemeasurable)
    (Eventually.of_forall (fun x => fun m n hmn => ENNReal.ofReal_le_ofReal (hmono x hmn)))
    (Eventually.of_forall (fun x => ENNReal.continuous_ofReal.continuousAt.tendsto.comp (ht x)))
  have hb' : ∀ n, (∫⁻ x, ENNReal.ofReal (f n x) ∂μ) ≤ ENNReal.ofReal B := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hf n) (Eventually.of_forall (hn n))]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hfin : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) < ⊤ :=
    (le_of_tendsto ht' (Eventually.of_forall hb')).trans_lt ENNReal.ofReal_lt_top
  have hi : Integrable F μ :=
    ⟨hm, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hF)).mpr hfin⟩
  refine ⟨hi, le_of_tendsto (x := atTop) ?_ (Eventually.of_forall hb)⟩
  exact integral_tendsto_of_tendsto_of_monotone hf hi
    (Eventually.of_forall hmono) (Eventually.of_forall ht)

/-- The product-filter and nested-sum presentations of unordered pairs agree. -/
theorem sum_ionizationPairs {N : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin N → Fin N → A) :
    ∑ p ∈ ionizationPairs N, f p.1 p.2 =
      ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j := by
  simp only [ionizationPairs, Finset.sum_filter, Finset.sum_product]

/-- Cutoff pair estimate's fixed-cutoff bounds imply a finite bound for the limiting total pair integral. -/
theorem integral_ionizationPairRatio_le_of_cutoff {N q : ℕ} (u : State N q) (B : ℝ)
    (hi : ∀ ε : ℝ, 0 < ε → ∀ i j : Fin N, i < j →
      Integrable (fun X => ionizationPairCutoff ε i j X * ‖u X‖ ^ 2))
    (hb : ∀ ε : ℝ, 0 < ε →
      (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ∫ X, ionizationPairCutoff ε i j X * ‖u X‖ ^ 2) ≤ B) :
    Integrable (fun X => ∑ p ∈ ionizationPairs N,
      ionizationPairRatio p.1 p.2 X * ‖u X‖ ^ 2) ∧
    (∫ X, ∑ p ∈ ionizationPairs N,
      ionizationPairRatio p.1 p.2 X * ‖u X‖ ^ 2) ≤ B := by
  let ε := fun n : ℕ => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  apply integrable_limit_of_monotone_integral_bound
    (f := fun n X => ∑ p ∈ ionizationPairs N,
      ionizationPairCutoff (ε n) p.1 p.2 X * ‖u X‖ ^ 2)
  · intro n
    apply integrable_finsetSum
    intro p hp
    exact hi (ε n) (hε n) p.1 p.2 (Finset.mem_filter.mp hp).2
  · apply Measurable.aestronglyMeasurable
    apply Finset.measurable_sum
    intro p _
    exact (measurable_ionizationPairRatio p.1 p.2).mul
      ((Lp.stronglyMeasurable u).measurable.norm.pow_const 2)
  · intro n X
    exact Finset.sum_nonneg (fun p _ => mul_nonneg
      (ionizationPairCutoff_nonneg (hε n).le p.1 p.2 X) (sq_nonneg _))
  · intro X
    exact Finset.sum_nonneg (fun p _ => mul_nonneg
      (ionizationPairRatio_nonneg p.1 p.2 X) (sq_nonneg _))
  · intro X m n hmn
    apply Finset.sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    exact add_le_add (monotone_ionizationWeight_sequence (norm_nonneg _) hmn)
      (monotone_ionizationWeight_sequence (norm_nonneg _) hmn)
  · intro X
    apply tendsto_finsetSum
    intro p _
    have h := ((tendsto_ionizationWeight_sequence ‖particlePosition X p.1‖).add
      (tendsto_ionizationWeight_sequence ‖particlePosition X p.2‖)).div_const
        ‖particlePosition X p.1 - particlePosition X p.2‖
    simpa only [Pi.mul_apply, Pi.div_apply, Pi.add_apply, ionizationPairCutoff,
      ionizationPairRatio] using h.mul_const (‖u X‖ ^ 2)
  · intro n
    rw [integral_finsetSum (ionizationPairs N) (fun p hp =>
      hi (ε n) (hε n) p.1 p.2 (Finset.mem_filter.mp hp).2)]
    rw [sum_ionizationPairs (fun i j => ∫ X, ionizationPairCutoff (ε n) i j X * ‖u X‖ ^ 2)]
    exact hb (ε n) (hε n)

end LiebThirring
end
