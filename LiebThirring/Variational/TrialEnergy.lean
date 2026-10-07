/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.GroundStateEnergy
import LiebThirring.Theorems.StabilityOfMatterReal

/-! # Variational bounds for normalized trial energies -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- Fixed finite nuclear data give a uniform real lower bound on normalized trial energies. -/
theorem exists_lower_bound_normalized_realEnergy (q : ℕ) (hq : 1 ≤ q)
    (N M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (hR : Function.Injective R) :
    ∃ B : ℝ, ∀ ψ : FormDomain N q, ‖(ψ : State N q)‖ = 1 →
      B ≤ realEnergy z R hR ψ := by
  classical
  obtain ⟨C, _, hC⟩ := stability_of_matter_real q hq (∑ k, z k)
  refine ⟨-(C : ℝ) * ((N + M : ℕ) : ℝ), ?_⟩
  intro ψ hψ
  have hz (k : Fin M) : z k ≤ ∑ j, z j :=
    Finset.single_le_sum (fun j _ => (zero_le : 0 ≤ z j)) (Finset.mem_univ k)
  have hbound := (hC N M z R ψ.val hz hR ψ.property.1 hψ ψ.property.2).2.2.2
  simpa only [realEnergy, hψ, one_pow, mul_one] using hbound

/-- Stability excludes negative infinity even before a normalized trial has been constructed. -/
theorem groundStateEnergy_ne_bot (q : ℕ) (hq : 1 ≤ q)
    (N M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (hR : Function.Injective R) : groundStateEnergy N q M z R hR ≠ ⊥ := by
  obtain ⟨B, hB⟩ := exists_lower_bound_normalized_realEnergy q hq N M z R hR
  have hlow : (B : EReal) ≤ groundStateEnergy N q M z R hR := by
    apply le_iInf
    intro ψ
    exact EReal.coe_le_coe_iff.mpr (hB ψ.val ψ.property)
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot B) hlow

/-- Any normalized form-domain trial excludes positive infinity. -/
theorem groundStateEnergy_ne_top_of_trial {q N M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (ψ : FormDomain N q) (hψ : ‖(ψ : State N q)‖ = 1) :
    groundStateEnergy N q M z R hR ≠ ⊤ := by
  have hupper : groundStateEnergy N q M z R hR ≤ (realEnergy z R hR ψ : EReal) :=
    by
      let u : {ψ : FormDomain N q // ‖(ψ : State N q)‖ = 1} := ⟨ψ, hψ⟩
      exact iInf_le (fun u : {ψ : FormDomain N q // ‖(ψ : State N q)‖ = 1} =>
        (realEnergy z R hR u.val : EReal)) u
  exact (lt_of_le_of_lt hupper (EReal.coe_lt_top _)).ne

end LiebThirring

end
