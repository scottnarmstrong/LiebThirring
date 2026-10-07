/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.AtomicGroundStateEnergy
public import LiebThirring.Variational.WeakGroundState
import LiebThirring.Proofs.BindingGroundStateExists

/-! # Existence below the atomic escape threshold -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- Strict binding produces a normalized weak ground state; existence is a conclusion. -/
theorem exists_atomic_weak_ground_state_of_lt (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0) (hZ : 0 < Z)
    (hbind : atomicGroundStateEnergy N q Z < atomicGroundStateEnergy (N - 1) q Z) :
    ∃ ψ : FormDomain N q,
      is_weak_ground_state (fun _ : Fin 1 => Z) (fun _ : Fin 1 => 0)
        (fun _ _ _ => Subsingleton.elim _ _) ψ :=
  by exact LiebThirring.Proofs.exists_atomic_weak_ground_state_of_lt q hq N Z hZ hbind

end LiebThirring

end
