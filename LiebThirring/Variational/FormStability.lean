/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormPolarization
import LiebThirring.Theorems.StabilityOfMatterReal

/-! # Stability for unnormalized antisymmetric form-domain states

Form polarization: normalization is used only inside the proof, with the nuclear term scaled
by the full mass exactly as in the `realEnergy` definition.
-/

public section
open MeasureTheory
open scoped ComplexConjugate ENNReal NNReal
namespace LiebThirring

/-- Zero has zero real energy. -/
@[simp] theorem realEnergy_zero {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) :
    realEnergy (N := N) (q := q) z R hR 0 = 0 := by
  have h := realEnergy_smul z R hR (0 : ℂ) (0 : FormDomain N q)
  simpa only [zero_smul, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul] using h

/-- Real stability with the same uniform constant as the normalized theorem. -/
theorem stability_of_matter_real_unnormalized (q : ℕ) (hq : 1 ≤ q) (Z : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (N M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position)
        (hR : Function.Injective R) (ψ : FormDomain N q),
        (∀ k, z k ≤ Z) →
          -(C : ℝ) * ((N + M : ℕ) : ℝ) * ‖(ψ : State N q)‖ ^ 2 ≤ realEnergy z R hR ψ := by
  obtain ⟨C, hC, hbound⟩ := stability_of_matter_real q hq Z
  refine ⟨C, hC, ?_⟩
  intro N M z R hR ψ hz
  by_cases hψ : (ψ : State N q) = 0
  · have hzero : ψ = 0 := Subtype.ext hψ
    rw [hzero, formDomain_coe_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero, realEnergy_zero]
  have hn : ‖(ψ : State N q)‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  let c : ℂ := (‖(ψ : State N q)‖ : ℂ)⁻¹
  let v : FormDomain N q := c • ψ
  have hv : ‖(v : State N q)‖ = 1 := by
    dsimp only [v]
    rw [formDomain_coe_smul, norm_smul]
    dsimp only [c]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ hn]
  have h := (hbound N M z R (v : State N q) hz hR v.property.1 hv v.property.2).2.2.2
  have hreal : -(C : ℝ) * ((N + M : ℕ) : ℝ) ≤ realEnergy z R hR v := by
    unfold realEnergy
    rw [hv, one_pow, mul_one]
    exact h
  rw [show v = c • ψ from rfl, realEnergy_smul] at hreal
  have hc : ‖c‖ ^ 2 = (‖(ψ : State N q)‖ ^ 2)⁻¹ := by
    dsimp only [c]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), inv_pow]
  rw [hc, ← div_eq_inv_mul] at hreal
  exact (le_div_iff₀ (sq_pos_of_ne_zero hn)).mp hreal

end LiebThirring
end
