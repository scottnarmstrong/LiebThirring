/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.ConfinedGroundStateEnergy

/-! # Order properties of the confined variational infimum

The upper bound uses a normalized trial. The lower-bound helper is explicitly
conditional on the extensive quantum-stability bound.
-/

public section

open scoped NNReal

namespace LiebThirring

theorem confinedGroundStateEnergy_le_trial {N M q z : ℕ}
    {m : {m : ℝ≥0 // 0 < m}} {L : {L : ℝ // 0 < L}}
    (ψ : DirichletBallFormDomain N M q m L) (hψ : ‖ψ.val.val‖ = 1) :
    confinedGroundStateEnergy N M q z m L ≤ (quantumEnergy z m ψ.val : EReal) := by
  unfold confinedGroundStateEnergy
  exact iInf_le (fun u : {u : DirichletBallFormDomain N M q m L // ‖u.val.val‖ = 1} =>
    (quantumEnergy z m u.val.val : EReal)) ⟨ψ, hψ⟩

theorem confinedGroundStateEnergy_ne_top_of_trial {N M q z : ℕ}
    {m : {m : ℝ≥0 // 0 < m}} {L : {L : ℝ // 0 < L}}
    (ψ : DirichletBallFormDomain N M q m L) (hψ : ‖ψ.val.val‖ = 1) :
    confinedGroundStateEnergy N M q z m L ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (confinedGroundStateEnergy_le_trial ψ hψ)

/-- An ordinary conditional helper, not a proof of the finite-energy theorem. -/
theorem confinedGroundStateEnergy_ne_bot_of_lower_bound {N M q z : ℕ}
    {m : {m : ℝ≥0 // 0 < m}} {L : {L : ℝ // 0 < L}} (B : ℝ)
    (hB : ∀ ψ : DirichletBallFormDomain N M q m L,
      ‖ψ.val.val‖ = 1 → B ≤ quantumEnergy z m ψ.val) :
    confinedGroundStateEnergy N M q z m L ≠ ⊥ := by
  have hlow : (B : EReal) ≤ confinedGroundStateEnergy N M q z m L := by
    apply le_iInf
    intro ψ
    exact EReal.coe_le_coe_iff.mpr (hB ψ.val ψ.property)
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot B) hlow

end LiebThirring

end
