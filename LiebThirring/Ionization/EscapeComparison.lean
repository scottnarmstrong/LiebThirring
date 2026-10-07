/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapeCore
public import LiebThirring.Ionization.EscapeTrial
import LiebThirring.Variational.TrialVacuum

/-! # The variational escape comparison -/

public section

open MeasureTheory
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- The proved compact form core and explicit normalized wedge give the successor-sector
escape inequality, without any density, trial, or minimizer premise. -/
theorem escape_atomicGroundStateEnergy_succ_le (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0) :
    atomicGroundStateEnergy (N + 1) q Z ≤ atomicGroundStateEnergy N q Z := by
  have hreal : (atomicGroundStateEnergy (N + 1) q Z).toReal ≤
      (atomicGroundStateEnergy N q Z).toReal := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨f, hf, hc, hn, hnear⟩ := escape_exists_normalized_compact_near_minimizer
      q hq N Z (ε / 2) (half_pos hε)
    obtain ⟨u, hu, he⟩ := escape_exists_trial_energy_lt q hq Z f hc hf hn
      (ε / 2) (half_pos hε)
    have hvar := groundStateEnergy_toReal_le_realEnergy q hq (N + 1) 1
      (fun _ => Z) (fun _ => 0) (fun _ _ _ => Subsingleton.elim _ _) u hu
    have heq := escapeAtomicSchwartzEnergy_eq_realEnergy Z f (escapeSchwartzForm f hf) rfl
    rw [heq] at he
    change (atomicGroundStateEnergy (N + 1) q Z).toReal ≤
      realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (fun _ _ _ => Subsingleton.elim _ _) u at hvar
    linarith only [hnear, he, hvar]
  have hN := trial_groundStateEnergy_finite q hq N 1 (fun _ => Z)
    (fun _ => 0) (fun _ _ _ => Subsingleton.elim _ _)
  have hsucc := trial_groundStateEnergy_finite q hq (N + 1) 1 (fun _ => Z)
    (fun _ => 0) (fun _ _ _ => Subsingleton.elim _ _)
  change atomicGroundStateEnergy N q Z ≠ ⊤ ∧ atomicGroundStateEnergy N q Z ≠ ⊥ at hN
  change atomicGroundStateEnergy (N + 1) q Z ≠ ⊤ ∧
    atomicGroundStateEnergy (N + 1) q Z ≠ ⊥ at hsucc
  rw [← EReal.coe_toReal hN.1 hN.2, ← EReal.coe_toReal hsucc.1 hsucc.2]
  exact EReal.coe_le_coe_iff.mpr hreal

/-- Iterating escape monotonicity compares every pair of particle sectors. -/
theorem atomicGroundStateEnergy_antitone (q : ℕ) (hq : 1 ≤ q) (Z : ℝ≥0) :
    Antitone (fun N => atomicGroundStateEnergy N q Z) := by
  exact antitone_nat_of_succ_le (fun N => escape_atomicGroundStateEnergy_succ_le q hq N Z)

end LiebThirring

end
