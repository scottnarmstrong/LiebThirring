/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.AtomicGroundStateEnergy
public import LiebThirring.Variational.WeakGroundState
import LiebThirring.Ionization.EigenBound
import LiebThirring.Ionization.EscapeMonotonicity
import LiebThirring.Variational.MinimizerEulerLagrange

/-!
# Atomic ionization for weak ground states

Weighted kinetic positivity and pair geometry give the strict electron-count
bound for a normalized weak ground state at or below the removal threshold.
Source: Lieb (1984), Theorem 1, equations (2.9), (2.11) and (4.1)–(4.5).
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.Proofs

/-- Assembly of weak-eigenfunction estimate, minimizer equation and the proved escape monotonicity, with the exact type. -/
theorem electron_count_lt_of_atomic_weak_ground_state (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0) (hZ : 0 < Z) (ψ : FormDomain N q)
    (hψ : is_weak_ground_state (fun _ : Fin 1 => Z) (fun _ : Fin 1 => 0)
      (fun _ _ _ => Subsingleton.elim _ _) ψ) :
    (N : ℝ) < 2 * (Z : ℝ) + 1 := by
  have hatt := weak_ground_state_attains_infimum (fun _ : Fin 1 => Z)
    (fun _ : Fin 1 => 0) (fun _ _ _ => Subsingleton.elim _ _) ψ hψ
  obtain ⟨hu, E, henergy, heig⟩ := hψ
  have hreal : E = realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
      (fun _ _ _ => Subsingleton.elim _ _) ψ :=
    EReal.coe_injective (henergy.symm.trans hatt)
  have hf := trial_groundStateEnergy_finite q hq (N - 1) 1
    (fun _ : Fin 1 => Z) (fun _ => 0) (fun _ _ _ => Subsingleton.elim _ _)
  have hescape := atomicGroundStateEnergy_le_pred q hq N Z
  have hfinite : atomicGroundStateEnergy N q Z ≠ ⊥ := by
    rw [atomicGroundStateEnergy, henergy]
    exact EReal.coe_ne_bot E
  have hthreshold := EReal.toReal_le_toReal hescape hfinite hf.1
  have hvalue : (atomicGroundStateEnergy N q Z).toReal = E := by
    rw [atomicGroundStateEnergy, hatt, EReal.toReal_coe, ← hreal]
  rw [hvalue] at hthreshold
  exact electron_count_lt_of_atomic_weak_eigenfunction Z hZ E ψ hu heig hthreshold

end LiebThirring.Proofs
end
