/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.TrialExists

/-! # Conditional lower finiteness of confined energy

Argument thermodynamic confined form estimates and quantum stability. This file isolates the exact lower-bound
input as an explicit hypothesis.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

theorem confinedGroundStateEnergy_ne_bot_of_quantum_lower_bound {N M q z : ℕ}
    {m : {m : ℝ≥0 // 0 < m}} {L : {L : ℝ // 0 < L}} (C : ℝ≥0)
    (hC : ∀ ψ : QuantumFormDomain N M q,
      -(C : ℝ) * ((N + M : ℕ) : ℝ) * ‖ψ.val‖ ^ 2 +
        (nuclearKineticCoefficient m : ℝ) *
          (quantumNuclearKineticEnergy ψ.val).toReal ≤ quantumEnergy z m ψ) :
    confinedGroundStateEnergy N M q z m L ≠ ⊥ := by
  apply confinedGroundStateEnergy_ne_bot_of_lower_bound (-(C : ℝ) * (N + M : ℕ))
  intro ψ hψ
  have hnonneg : 0 ≤ (nuclearKineticCoefficient m : ℝ) *
      (quantumNuclearKineticEnergy ψ.val.val).toReal :=
    mul_nonneg (nuclearKineticCoefficient m).coe_nonneg ENNReal.toReal_nonneg
  have h := (le_add_of_nonneg_right hnonneg).trans (hC ψ.val)
  simpa only [hψ, one_pow, mul_one] using h

/-- Conditional assembly only. -/
theorem confinedGroundStateEnergy_ne_top_ne_bot_of_quantum_lower_bound
    (N M q : ℕ) (hq : 1 ≤ q) (z : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) (C : ℝ≥0)
    (hC : ∀ ψ : QuantumFormDomain N M q,
      -(C : ℝ) * ((N + M : ℕ) : ℝ) * ‖ψ.val‖ ^ 2 +
        (nuclearKineticCoefficient m : ℝ) *
          (quantumNuclearKineticEnergy ψ.val).toReal ≤ quantumEnergy z m ψ) :
    confinedGroundStateEnergy N M q z m L ≠ ⊤ ∧
      confinedGroundStateEnergy N M q z m L ≠ ⊥ :=
  ⟨confinedGroundStateEnergy_ne_top N M q hq z m L,
    confinedGroundStateEnergy_ne_bot_of_quantum_lower_bound C hC⟩

end LiebThirring

end
