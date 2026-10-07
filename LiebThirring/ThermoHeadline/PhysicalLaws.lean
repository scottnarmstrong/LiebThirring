/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoHeadline.PhysicalEnergy
public import LiebThirring.ThermoClusters.DirichletMotion

/-!
# The real extensive and domain laws for physical neutral energy

Quantum stability follows from proved quantum stability with `A = C * (z + 1)`.
rigid-motion and domain-inclusion identities follows from the exact region infimum's inclusion and rigid-motion
laws. Real order is transported only after proving finite EReal values.
-/

public section

open Metric Set
open scoped NNReal ENNReal

namespace LiebThirring.ThermoHeadline

/-- The real extensive bound shares one positive constant over all neutral
counts, masses, and nonempty open regions. -/
theorem exists_physicalNeutralEnergy_extensive_lower_bound
    (q : ℕ) (hq : 1 ≤ q) (z : ℕ) (hz : 1 ≤ z) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (mass : {m : ℝ≥0 // 0 < m}) (Ω : Set Position) (n : ℕ),
        IsOpen Ω → Ω.Nonempty → -A * (n : ℝ) ≤ physicalNeutralEnergy q z mass Ω n := by
  obtain ⟨C, hCpos, hC⟩ := exists_dirichletRegionGroundStateEnergy_lower_bound q hq z hz
  refine ⟨(C : ℝ) * ((z : ℝ) + 1), mul_pos (by exact_mod_cast hCpos) (by positivity), ?_⟩
  intro mass Ω n hopen hne
  have htop := dirichletRegionGroundStateEnergy_ne_top (z * n) n q hq z mass Ω hopen hne
  have hreal := EReal.toReal_le_toReal (hC (z * n) n mass Ω) (EReal.coe_ne_bot _) htop
  simp only [← EReal.coe_neg, ← EReal.coe_mul, EReal.toReal_coe] at hreal
  have heq : -(C : ℝ) * (((z * n + n : ℕ) : ℝ)) =
      -((C : ℝ) * ((z : ℝ) + 1)) * (n : ℝ) := by
    push_cast
    ring
  rw [heq] at hreal
  exact hreal

/-- The centered-ball version of quantum stability used by the arbitrary-radius engine. -/
theorem exists_physicalNeutralEnergy_ball_lower_bound
    (q : ℕ) (hq : 1 ≤ q) (z : ℕ) (hz : 1 ≤ z)
    (mass : {m : ℝ≥0 // 0 < m}) :
    ∃ A : ℝ, 0 < A ∧ ∀ (L : ℝ) (n : ℕ), 0 < L →
      -A * (n : ℝ) ≤ physicalNeutralEnergy q z mass (ball (0 : Position) L) n := by
  obtain ⟨A, hA, hbound⟩ := exists_physicalNeutralEnergy_extensive_lower_bound q hq z hz
  exact ⟨A, hA, fun L n hL => hbound mass _ n isOpen_ball (nonempty_ball.mpr hL)⟩

/-- Enlarging a nonempty open domain decreases its physical real energy. -/
theorem physicalNeutralEnergy_antitone (q : ℕ) (hq : 1 ≤ q) (z : ℕ) (hz : 1 ≤ z)
    (mass : {m : ℝ≥0 // 0 < m}) {Ω Ω' : Set Position}
    (hopen : IsOpen Ω) (hne : Ω.Nonempty) (hopen' : IsOpen Ω') (hne' : Ω'.Nonempty)
    (hsub : Ω ⊆ Ω') (n : ℕ) :
    physicalNeutralEnergy q z mass Ω' n ≤ physicalNeutralEnergy q z mass Ω n := by
  obtain ⟨_, hbot'⟩ :=
    dirichletRegionGroundStateEnergy_ne_top_ne_bot (z * n) n q hq z hz mass Ω' hopen' hne'
  have htop := dirichletRegionGroundStateEnergy_ne_top (z * n) n q hq z mass Ω hopen hne
  exact EReal.toReal_le_toReal (dirichletRegionGroundStateEnergy_antitone hsub) hbot' htop

/-- A translated positive-radius ball has exactly the centered-ball energy. -/
theorem physicalNeutralEnergy_ball_center (q z : ℕ) (mass : {m : ℝ≥0 // 0 < m})
    (c : Position) (R : ℝ) (hR : 0 < R) (n : ℕ) :
    physicalNeutralEnergy q z mass (ball c R) n =
      physicalNeutralEnergy q z mass (ball (0 : Position) R) n := by
  unfold physicalNeutralEnergy
  rw [dirichletRegionGroundStateEnergy_ball_center (z * n) n q z c mass ⟨R, hR⟩,
    dirichletRegionGroundStateEnergy_ball (z * n) n q z mass ⟨R, hR⟩]

end LiebThirring.ThermoHeadline

end
