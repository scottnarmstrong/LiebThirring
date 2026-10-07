/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SpectatorMultiplier
public import LiebThirring.Variational.SpectatorReindex

/-! # Selected and spectator weak-gradient assembly -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring.Variational

open Sobolev

/-- The Bochner representative of a state has squared norm integral equal to its L² norm. -/
theorem integral_state_norm_sq {N q : ℕ} (v : State N q) :
    (∫ X : Configuration N, ‖v X‖ ^ 2) = ‖v‖ ^ 2 := by
  have hfin : (∫⁻ X : Configuration N, (1 : ℝ≥0∞) * ‖v X‖ₑ ^ 2) < ⊤ := by
    simp only [one_mul, lintegral_l2_enorm_sq]
    exact ENNReal.pow_lt_top ENNReal.coe_lt_top
  have h := LiebThirring.integral_weight_norm_sq
    (p := fun _ : Configuration N => (1 : ℝ≥0∞)) (f := fun X => v X)
    measurable_const.aemeasurable (Lp.aestronglyMeasurable v) hfin
  simp only [ENNReal.toReal_one, one_mul] at h
  change (∫ X : Configuration N, ‖v X‖ ^ 2) =
    (∫⁻ X : Configuration N, ‖v X‖ₑ ^ 2).toReal at h
  rw [lintegral_l2_enorm_sq, ENNReal.toReal_pow] at h
  exact h

/-- A bounded nonnegative selected-coordinate weight converts a derivative L² pairing into the
weighted residual-slice mass. -/
theorem re_inner_lipschitzBoundedSMul_eq_residual {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (v : State N q)
    (b : Position → ℝ) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) (hb0 : ∀ x, 0 ≤ b x)
    (C : ℝ≥0) (hb : LipschitzWith C b) :
    (inner ℂ
      (lipschitzBoundedSMul (fun X : Configuration N => b (particlePosition X i)) B
        (fun X => hB (particlePosition X i)) (lipschitzWith_selected_multiplier i b C hb) v)
      v).re =
      ∫ x : Position, ∑ s : Fin q, ∫ y : Configuration k,
        b x * ‖residualParticleSlice i e v x s y‖ ^ 2 := by
  let p : Position × Configuration k → ℝ≥0∞ := fun z => ENNReal.ofReal (b z.1)
  have hp : Measurable p :=
    ENNReal.measurable_ofReal.comp (hb.continuous.measurable.comp measurable_fst)
  have hbase : (∫⁻ X : Configuration N, (1 : ℝ≥0∞) * ‖v X‖ₑ ^ 2) < ⊤ := by
    simp only [one_mul, lintegral_l2_enorm_sq]
    exact ENNReal.pow_lt_top ENNReal.coe_lt_top
  have hfin : (∫⁻ X : Configuration N,
      p (particlePosition X i, residualProjection i e X) * ‖v X‖ₑ ^ 2) < ⊤ := by
    simpa only [p, mul_one] using LiebThirring.lintegral_bounded_weight_lt_top
      (fun X : Configuration N => b (particlePosition X i)) B
      (fun X => hB (particlePosition X i)) (fun _ => (1 : ℝ≥0∞)) (fun X => v X) hbase
  have hdis := integral_spectator_reindex_joint_real i e v p hp hfin
  have hcoe := lipschitzBoundedSMul_coeFn
    (fun X : Configuration N => b (particlePosition X i)) B
    (fun X => hB (particlePosition X i)) (lipschitzWith_selected_multiplier i b C hb) v
  rw [L2.inner_def]
  rw [show (∫ X : Configuration N,
      inner ℂ
        ((lipschitzBoundedSMul (fun X : Configuration N => b (particlePosition X i)) B
          (fun X => hB (particlePosition X i)) (lipschitzWith_selected_multiplier i b C hb) v) X)
        (v X)) =
      ∫ X : Configuration N, (b (particlePosition X i) : ℂ) * inner ℂ (v X) (v X) by
        apply integral_congr_ae
        filter_upwards [hcoe] with X hX
        rw [hX, inner_smul_left, Complex.conj_ofReal]]
  have hint : Integrable (fun X : Configuration N =>
      (b (particlePosition X i) : ℂ) * inner ℂ (v X) (v X)) :=
    (L2.integrable_inner (𝕜 := ℂ)
      (lipschitzBoundedSMul (fun X : Configuration N => b (particlePosition X i)) B
        (fun X => hB (particlePosition X i)) (lipschitzWith_selected_multiplier i b C hb) v) v).congr
      (by filter_upwards [hcoe] with X hX
          rw [hX, inner_smul_left, Complex.conj_ofReal])
  calc
    _ = ∫ X : Configuration N,
        (↑(b (particlePosition X i)) * inner ℂ (v X) (v X)).re := (integral_re hint).symm
    _ = ∫ X : Configuration N, b (particlePosition X i) * ‖v X‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with X
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      congr 1
      change RCLike.re (inner ℂ (v X) (v X)) = _
      exact (norm_sq_eq_re_inner (v X)).symm
    _ = _ := by simpa only [p, ENNReal.toReal_ofReal (hb0 _)] using hdis

/-- The preceding weighted identity with the residual fibers expressed by their L² norms. -/
theorem re_inner_lipschitzBoundedSMul_eq_residual_norm {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (v : State N q)
    (b : Position → ℝ) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) (hb0 : ∀ x, 0 ≤ b x)
    (C : ℝ≥0) (hb : LipschitzWith C b) :
    (inner ℂ
      (lipschitzBoundedSMul (fun X : Configuration N => b (particlePosition X i)) B
        (fun X => hB (particlePosition X i)) (lipschitzWith_selected_multiplier i b C hb) v)
      v).re =
      ∫ x : Position, b x * ∑ s : Fin q, ‖residualParticleSlice i e v x s‖ ^ 2 := by
  rw [re_inner_lipschitzBoundedSMul_eq_residual i e v b B hB hb0 C hb]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_const_mul, integral_state_norm_sq]

/-- The weak-gradient pairing for a selected-coordinate multiplier splits into its selected
derivatives and the weighted L² mass of all reindexed spectator derivatives. -/
theorem re_sum_inner_weakDerivatives_selected_multiplier {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (g G : (Fin N × Fin 3) → State N q) (hg : ∀ c, HasWeakDerivative c u (g c))
    (b : Position → ℝ) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B) (hb0 : ∀ x, 0 ≤ b x)
    (C : ℝ≥0) (hb : LipschitzWith C b)
    (hG : ∀ c, HasWeakDerivative c
      (lipschitzBoundedSMul (fun X : Configuration N => b (particlePosition X i)) B
        (fun X => hB (particlePosition X i)) (lipschitzWith_selected_multiplier i b C hb) u)
      (G c)) :
    (∑ c, inner ℂ (G c) (g c)).re =
      (∑ a : Fin 3, inner ℂ (G (i, a)) (g (i, a))).re +
      ∫ x : Position, b x * ∑ s : Fin q, ∑ j : Fin k, ∑ a : Fin 3,
        ‖residualParticleSlice i e (g ((e j).1, a)) x s‖ ^ 2 := by
  have hsplit (f : Fin N → ℂ) :
      ∑ j, f j = f i + ∑ j : Fin k, f (e j).1 := by
    have hc : (∑ x ∈ Finset.univ.erase i, f x) = ∑ j : Fin k, f (e j).1 := by
      apply Finset.sum_bij (fun x hx => e.symm ⟨x, by simpa using hx⟩)
      · simp
      · intro x hx y hy hxy
        have h := congrArg (fun z : Fin k => (e z).1) hxy
        simpa using h
      · intro j hj
        refine ⟨(e j).1, ?_, ?_⟩
        · simpa using (e j).2
        · exact e.symm_apply_apply j
      · intro x hx
        simp
    rw [← hc, ← Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)]
    ac_rfl
  have hother (j : Fin k) (a : Fin 3) :
      G ((e j).1, a) =
        lipschitzBoundedSMul (fun X : Configuration N => b (particlePosition X i)) B
          (fun X => hB (particlePosition X i))
          (lipschitzWith_selected_multiplier i b C hb) (g ((e j).1, a)) := by
    apply HasWeakDerivative.unique (hG ((e j).1, a))
    exact LiebThirring.hasWeakDerivative_selected_multiplier_other i (e j).1 (e j).2 a u g hg
      b B hB C (lipschitzWith_selected_multiplier i b C hb)
  rw [Fintype.sum_prod_type, hsplit (fun j => ∑ a : Fin 3, inner ℂ (G (j, a)) (g (j, a))),
    Complex.add_re]
  congr 1
  change Complex.reCLM (∑ j : Fin k, ∑ a : Fin 3,
    inner ℂ (G ((e j).1, a)) (g ((e j).1, a))) = _
  rw [map_sum Complex.reCLM]
  simp_rw [map_sum Complex.reCLM]
  simp_rw [Complex.reCLM_apply]
  simp_rw [hother]
  simp_rw [re_inner_lipschitzBoundedSMul_eq_residual_norm i e _ b B hB hb0 C hb]
  have hint (j : Fin k) (a : Fin 3) : Integrable (fun x : Position =>
      b x * ∑ s : Fin q, ‖residualParticleSlice i e (g ((e j).1, a)) x s‖ ^ 2) := by
    let p : Position × Configuration k → ℝ≥0∞ := fun z => ENNReal.ofReal (b z.1)
    have hp : Measurable p :=
      ENNReal.measurable_ofReal.comp (hb.continuous.measurable.comp measurable_fst)
    have hbase : (∫⁻ X : Configuration N,
        (1 : ℝ≥0∞) * ‖g ((e j).1, a) X‖ₑ ^ 2) < ⊤ := by
      simp only [one_mul, lintegral_l2_enorm_sq]
      exact ENNReal.pow_lt_top ENNReal.coe_lt_top
    have hfin : (∫⁻ X : Configuration N,
        p (particlePosition X i, residualProjection i e X) *
          ‖g ((e j).1, a) X‖ₑ ^ 2) < ⊤ := by
      simpa only [p, mul_one] using LiebThirring.lintegral_bounded_weight_lt_top
        (fun X : Configuration N => b (particlePosition X i)) B
        (fun X => hB (particlePosition X i)) (fun _ => (1 : ℝ≥0∞))
        (fun X => g ((e j).1, a) X) hbase
    have hraw := integrable_spectator_reindex_joint_real i e (g ((e j).1, a)) p hp hfin
    apply hraw.congr
    filter_upwards [] with x
    simp only [p, ENNReal.toReal_ofReal (hb0 _)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [integral_const_mul, integral_state_norm_sq]
  calc
    _ = ∑ j : Fin k, ∫ x : Position, ∑ a : Fin 3,
        b x * ∑ s : Fin q, ‖residualParticleSlice i e (g ((e j).1, a)) x s‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact (integral_finsetSum Finset.univ (fun a _ => hint j a)).symm
    _ = ∫ x : Position, ∑ j : Fin k, ∑ a : Fin 3,
        b x * ∑ s : Fin q, ‖residualParticleSlice i e (g ((e j).1, a)) x s‖ ^ 2 :=
      (integral_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun a _ => hint j a))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Finset.mul_sum]
      calc
        (∑ j : Fin k, ∑ a : Fin 3, ∑ s : Fin q,
            b x * ‖residualParticleSlice i e (g ((e j).1, a)) x s‖ ^ 2) =
            ∑ j : Fin k, ∑ s : Fin q, ∑ a : Fin 3,
              b x * ‖residualParticleSlice i e (g ((e j).1, a)) x s‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm

end LiebThirring.Variational

end
