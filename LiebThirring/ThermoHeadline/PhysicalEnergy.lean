/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.Domains
public import LiebThirring.Thermodynamic.QuantumStability
public import LiebThirring.Thermodynamic.ConfinedTrialExists
import LiebThirring.ThermoClusters.DirichletMotion
import LiebThirring.ThermoForm.Infimum

/-!
# Physical neutral energies and finite real values

The neutral energy is the real value of the literal region variational infimum.
Quantum stability bounds that infimum from below; a translated small-ball
trial bounds it from above on every nonempty open bounded region. The proof
uses confined form estimates and rigid-motion and domain-inclusion identities.
-/

public section

open Metric Set
open scoped NNReal ENNReal

namespace LiebThirring.ThermoHeadline

/-- The physical real neutral energy, with `z * n` electrons and `n` nuclei. -/
@[expose] noncomputable def physicalNeutralEnergy (q z : ℕ)
    (mass : {m : ℝ≥0 // 0 < m}) (Ω : Set Position) (n : ℕ) : ℝ :=
  (dirichletRegionGroundStateEnergy (z * n) n q z mass Ω).toReal

/-- The exact extensive lower bound on every spatial variational infimum,
conditional on the unnormalized quantum stability inequality. -/
theorem dirichletRegionGroundStateEnergy_lower_bound {N M q z : ℕ}
    (mass : {m : ℝ≥0 // 0 < m}) (Ω : Set Position) (C : ℝ≥0)
    (hC : ∀ ψ : QuantumFormDomain N M q,
      -(C : ℝ) * ((N + M : ℕ) : ℝ) * ‖ψ.val‖ ^ 2 +
        (nuclearKineticCoefficient mass : ℝ) *
          (quantumNuclearKineticEnergy ψ.val).toReal ≤ quantumEnergy z mass ψ) :
    (-(C : ℝ) * ((N + M : ℕ) : ℝ) : EReal) ≤
      dirichletRegionGroundStateEnergy N M q z mass Ω := by
  apply le_iInf
  intro ψ
  apply EReal.coe_le_coe_iff.mpr
  have hnonneg : 0 ≤ (nuclearKineticCoefficient mass : ℝ) *
      (quantumNuclearKineticEnergy ψ.val.val.val).toReal :=
    mul_nonneg (nuclearKineticCoefficient mass).coe_nonneg ENNReal.toReal_nonneg
  have h := (le_add_of_nonneg_right hnonneg).trans (hC ψ.val.val)
  simpa only [ψ.property, one_pow, mul_one] using h

/-- The stability constant is shared by every sector, mass and spatial region. -/
theorem exists_dirichletRegionGroundStateEnergy_lower_bound
    (q : ℕ) (hq : 1 ≤ q) (z : ℕ) (hz : 1 ≤ z) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (N M : ℕ) (mass : {m : ℝ≥0 // 0 < m}) (Ω : Set Position),
        (-(C : ℝ) * ((N + M : ℕ) : ℝ) : EReal) ≤
          dirichletRegionGroundStateEnergy N M q z mass Ω := by
  obtain ⟨C, hCpos, hC⟩ := quantum_stability q hq z hz
  exact ⟨C, hCpos, fun N M mass Ω =>
    dirichletRegionGroundStateEnergy_lower_bound mass Ω C (hC N M mass)⟩

/-- A ball inside a nonempty open region supplies a finite-energy upper trial. -/
theorem dirichletRegionGroundStateEnergy_ne_top (N M q : ℕ) (hq : 1 ≤ q)
    (z : ℕ) (mass : {m : ℝ≥0 // 0 < m}) (Ω : Set Position)
    (hopen : IsOpen Ω) (hne : Ω.Nonempty) :
    dirichletRegionGroundStateEnergy N M q z mass Ω ≠ ⊤ := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp hopen c hc
  let L : {L : ℝ // 0 < L} := ⟨R, hR⟩
  obtain ⟨ψ, hψ⟩ := exists_normalized_dirichlet_ball_form_domain N M q hq mass L
  have hball : confinedGroundStateEnergy N M q z mass L ≠ ⊤ :=
    confinedGroundStateEnergy_ne_top_of_trial ψ hψ
  have hle := dirichletRegionGroundStateEnergy_antitone
    (N := N) (M := M) (q := q) (z := z) (m := mass) hsub
  rw [dirichletRegionGroundStateEnergy_ball_center N M q z c mass L] at hle
  exact ne_top_of_le_ne_top hball hle

/-- The physical region infimum is finite on every nonempty open region.
Boundedness is unnecessary for this finiteness statement. -/
theorem dirichletRegionGroundStateEnergy_ne_top_ne_bot (N M q : ℕ) (hq : 1 ≤ q)
    (z : ℕ) (hz : 1 ≤ z) (mass : {m : ℝ≥0 // 0 < m}) (Ω : Set Position)
    (hopen : IsOpen Ω) (hne : Ω.Nonempty) :
    dirichletRegionGroundStateEnergy N M q z mass Ω ≠ ⊤ ∧
      dirichletRegionGroundStateEnergy N M q z mass Ω ≠ ⊥ := by
  obtain ⟨C, _, hC⟩ := exists_dirichletRegionGroundStateEnergy_lower_bound q hq z hz
  exact ⟨dirichletRegionGroundStateEnergy_ne_top N M q hq z mass Ω hopen hne,
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hC N M mass Ω)⟩

/-- Finiteness makes the real neutral energy an exact representation of the
physical region infimum; `toReal` loses no information here. -/
theorem coe_physicalNeutralEnergy (q : ℕ) (hq : 1 ≤ q) (z : ℕ) (hz : 1 ≤ z)
    (mass : {m : ℝ≥0 // 0 < m}) (Ω : Set Position) (n : ℕ)
    (hopen : IsOpen Ω) (hne : Ω.Nonempty) :
    (physicalNeutralEnergy q z mass Ω n : EReal) =
      dirichletRegionGroundStateEnergy (z * n) n q z mass Ω := by
  obtain ⟨htop, hbot⟩ :=
    dirichletRegionGroundStateEnergy_ne_top_ne_bot (z * n) n q hq z hz mass Ω hopen hne
  exact EReal.coe_toReal htop hbot

end LiebThirring.ThermoHeadline

end
