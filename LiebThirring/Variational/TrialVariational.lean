/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.TrialConstruction
public import LiebThirring.Variational.TrialEnergy
public import LiebThirring.Variational.TrialScaling

/-! # The finite infimum and the unnormalized variational inequality -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- The variational infimum is finite. -/
theorem trial_groundStateEnergy_finite (q : ℕ) (hq : 1 ≤ q)
    (N M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R) :
    groundStateEnergy N q M z R hR ≠ ⊤ ∧ groundStateEnergy N q M z R hR ≠ ⊥ := by
  obtain ⟨ψ, hψ⟩ := exists_normalized_formDomain_trial q hq N
  exact ⟨groundStateEnergy_ne_top_of_trial z R hR ψ hψ,
    groundStateEnergy_ne_bot q hq N M z R hR⟩

/-- The real value of the infimum bounds every normalized trial. -/
theorem groundStateEnergy_toReal_le_realEnergy (q : ℕ) (hq : 1 ≤ q)
    (N M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (u : FormDomain N q) (hu : ‖(u : State N q)‖ = 1) :
    (groundStateEnergy N q M z R hR).toReal ≤ realEnergy z R hR u := by
  have hf := trial_groundStateEnergy_finite q hq N M z R hR
  apply EReal.coe_le_coe_iff.mp
  rw [EReal.coe_toReal hf.1 hf.2]
  let v : {ψ : FormDomain N q // ‖(ψ : State N q)‖ = 1} := ⟨u, hu⟩
  exact iInf_le (fun v : {ψ : FormDomain N q // ‖(ψ : State N q)‖ = 1} =>
    (realEnergy z R hR v.val : EReal)) v

/-- Positive error tolerances admit normalized form-domain near-minimizers. -/
theorem exists_normalized_realEnergy_lt (q : ℕ) (hq : 1 ≤ q)
    (N M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : FormDomain N q, ‖(u : State N q)‖ = 1 ∧
      realEnergy z R hR u < (groundStateEnergy N q M z R hR).toReal + ε := by
  have hf := trial_groundStateEnergy_finite q hq N M z R hR
  have hlt : groundStateEnergy N q M z R hR <
      ((groundStateEnergy N q M z R hR).toReal + ε : ℝ) := by
    rw [← EReal.coe_toReal hf.1 hf.2]
    exact EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right _ hε)
  obtain ⟨u, hu⟩ := iInf_lt_iff.mp hlt
  exact ⟨u.val, u.property, EReal.coe_lt_coe_iff.mp hu⟩

/-- A zero form-domain state has zero quadratic energy. -/
theorem realEnergy_eq_zero_of_state_eq_zero {N q M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (u : FormDomain N q) (hu : (u : State N q) = 0) : realEnergy z R hR u = 0 := by
  have heq : trialFormDomainSmul 0 u = u := Subtype.ext (by
    change (0 : ℂ) • u.val = u.val
    rw [zero_smul, hu])
  rw [← heq, realEnergy_trialFormDomainSmul]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]

/-- Scalar normalization extends the variational bound to every unnormalized state,
including the zero state. -/
theorem groundStateEnergy_toReal_mul_norm_sq_le_realEnergy (q : ℕ) (hq : 1 ≤ q)
    (N M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (u : FormDomain N q) :
    (groundStateEnergy N q M z R hR).toReal * ‖(u : State N q)‖ ^ 2 ≤
      realEnergy z R hR u := by
  by_cases hu : (u : State N q) = 0
  · rw [hu, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
      realEnergy_eq_zero_of_state_eq_zero z R hR u hu]
  · let c : ℂ := (‖(u : State N q)‖⁻¹ : ℝ)
    have hn : ‖(u : State N q)‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have hc : ‖c‖ = ‖(u : State N q)‖⁻¹ := by
      exact Complex.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))
    have hv : ‖((trialFormDomainSmul c u) : State N q)‖ = 1 := by
      change ‖c • u.val‖ = 1
      rw [norm_smul, hc]
      exact inv_mul_cancel₀ hn
    have hb := groundStateEnergy_toReal_le_realEnergy q hq N M z R hR
      (trialFormDomainSmul c u) hv
    rw [realEnergy_trialFormDomainSmul, hc] at hb
    have hscaled := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖(u : State N q)‖)
    have heq : (‖(u : State N q)‖⁻¹ ^ 2 * realEnergy z R hR u) *
        ‖(u : State N q)‖ ^ 2 = realEnergy z R hR u := by
      rw [mul_right_comm, ← mul_pow, inv_mul_cancel₀ hn, one_pow, one_mul]
    exact heq ▸ hscaled

end LiebThirring

end
