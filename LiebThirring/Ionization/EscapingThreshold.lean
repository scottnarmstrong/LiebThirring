/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapeMonotonicity
public import LiebThirring.Variational.TrialVariational

/-! # Atomic threshold comparisons for every smaller particle sector

The iteration of escape monotonicity is the threshold comparison used in
including the vacuum sector.
-/

public section

open scoped NNReal

namespace LiebThirring

/-- Atomic ground energies decrease with the number of electrons. -/
theorem atomicGroundStateEnergy_antitone (q : ℕ) (hq : 1 ≤ q) (Z : ℝ≥0) :
    Antitone (fun N => atomicGroundStateEnergy N q Z) := by
  apply antitone_nat_of_succ_le
  intro N
  simpa only [Nat.add_sub_cancel] using atomicGroundStateEnergy_le_pred q hq (N + 1) Z

/-- Every smaller sector lies above the one-electron removal threshold. -/
theorem atomicGroundStateEnergy_pred_le_of_lt (q : ℕ) (hq : 1 ≤ q)
    (Z : ℝ≥0) {k N : ℕ} (hk : k < N) :
    atomicGroundStateEnergy (N - 1) q Z ≤ atomicGroundStateEnergy k q Z :=
  atomicGroundStateEnergy_antitone q hq Z (by omega)

/-- The same comparison on the finite real energy values. -/
theorem atomicGroundStateEnergy_toReal_pred_le_of_lt (q : ℕ) (hq : 1 ≤ q)
    (Z : ℝ≥0) {k N : ℕ} (hk : k < N) :
    (atomicGroundStateEnergy (N - 1) q Z).toReal ≤
      (atomicGroundStateEnergy k q Z).toReal := by
  have hpred := trial_groundStateEnergy_finite q hq (N - 1) 1
    (fun _ => Z) (fun _ => 0) (fun _ _ _ => Subsingleton.elim _ _)
  have hkfin := trial_groundStateEnergy_finite q hq k 1
    (fun _ => Z) (fun _ => 0) (fun _ _ _ => Subsingleton.elim _ _)
  exact EReal.toReal_le_toReal (atomicGroundStateEnergy_pred_le_of_lt q hq Z hk)
    hpred.2 hkfin.1

end LiebThirring
end
