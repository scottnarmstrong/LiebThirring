/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormFinite

/-! # Small relative bounds for electron repulsion

Hardy estimates: unordered pairs are counted once. No symmetry or normalization is used.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring
open Assembly

/-- Reindex the literal unordered-pair sum by ordered pairs with increasing indices. -/
theorem sum_unordered_pairs {N : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin N → Fin N → A) :
    (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j) =
      ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin N × Fin N => p.1 < p.2),
        f p.1 p.2 := by
  rw [Finset.sum_filter, Finset.sum_product]
  simp only [Finset.sum_filter]

/-- Repulsion is the sum of its unordered-pair expectations. -/
theorem lintegral_electronRepulsion_eq_sum {N q : ℕ} (ψ : State N q) :
    (∫⁻ X : Configuration N, electronRepulsion X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) =
      ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin N × Fin N => p.1 < p.2),
        ∫⁻ X : Configuration N,
          coulombKernel (particlePosition X p.1) (particlePosition X p.2) *
            (‖ψ X‖₊ : ℝ≥0∞) ^ 2 := by
  unfold electronRepulsion
  simp_rw [Finset.sum_mul]
  rw [lintegral_finsetSum]
  · rw [← sum_unordered_pairs (fun i j => ∫⁻ X : Configuration N,
      coulombKernel (particlePosition X i) (particlePosition X j) * (‖ψ X‖₊ : ℝ≥0∞) ^ 2)]
    apply Finset.sum_congr rfl
    intro i _
    exact lintegral_finsetSum _ (fun j _ =>
      (measurable_coulombKernel.comp
        ((measurable_particlePosition i).prodMk (measurable_particlePosition j))).mul
          (measurable_state_norm_sq ψ))
  · intro i _
    exact Finset.measurable_sum _ (fun j _ =>
      (measurable_coulombKernel.comp
        ((measurable_particlePosition i).prodMk (measurable_particlePosition j))).mul
          (measurable_state_norm_sq ψ))

/-- Sharp deliberately nonoptimal total pair bound, with `N.choose 2` unordered pairs. -/
theorem lintegral_electronRepulsion_toReal_le_sqrt {N q : ℕ} (ψ : State N q)
    (hT : kineticEnergy ψ < ⊤) :
    (∫⁻ X : Configuration N, electronRepulsion X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2).toReal ≤
      2 * (N.choose 2 : ℝ) * Real.sqrt (‖ψ‖ ^ 2 * (kineticEnergy ψ).toReal) := by
  classical
  let P := (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin N × Fin N => p.1 < p.2)
  have hij (p : Fin N × Fin N) (hp : p ∈ P) : p.1 ≠ p.2 :=
    ne_of_lt (Finset.mem_filter.mp hp).2
  rw [lintegral_electronRepulsion_eq_sum, ENNReal.toReal_sum (fun p hp =>
    (lintegral_pair_coulomb_le_sqrt p.1 p.2 (hij p hp) ψ hT).1.ne)]
  calc
    _ ≤ ∑ p ∈ P, 2 * Real.sqrt (‖ψ‖ ^ 2 * (particleFourierEnergy ψ p.1).toReal) :=
      Finset.sum_le_sum (fun p hp =>
        (lintegral_pair_coulomb_le_sqrt p.1 p.2 (hij p hp) ψ hT).2)
    _ ≤ ∑ _p ∈ P, 2 * Real.sqrt (‖ψ‖ ^ 2 * (kineticEnergy ψ).toReal) :=
      Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
          (ENNReal.toReal_mono hT.ne (realForm_particleFourierEnergy_le p.1 ψ))
            (sq_nonneg _))) (by norm_num))
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc : P.card = N.choose 2 := by
        simpa only [P, Finset.card_univ, Fintype.card_fin] using
          (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin N))))
      rw [hc]
      ring

/-- Repulsion has an arbitrarily small relative kinetic coefficient. -/
theorem lintegral_electronRepulsion_toReal_le {N q : ℕ} (ψ : State N q)
    (hT : kineticEnergy ψ < ⊤) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ X : Configuration N, electronRepulsion X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2).toReal ≤
      δ * (kineticEnergy ψ).toReal + ((N.choose 2 : ℝ) ^ 2 / δ) * ‖ψ‖ ^ 2 :=
  (lintegral_electronRepulsion_toReal_le_sqrt ψ hT).trans
    (two_mul_sqrt_mul_le (sq_nonneg _) ENNReal.toReal_nonneg hδ)

end LiebThirring
end
