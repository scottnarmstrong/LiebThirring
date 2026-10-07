/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.ExistenceBinding

/-!
# Weak ground states from atomic binding

All-sector localization makes normalized minimizing sequences tight.
Compact extraction attains the variational infimum and gives a weak ground state.
Source: Lieb (1984), the strict-binding discussion following equation (2.9).
-/

public section

open scoped NNReal

namespace LiebThirring.Proofs

/-- Strict atomic binding yields a weak ground state. -/
theorem exists_atomic_weak_ground_state_of_lt (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0) (_hZ : 0 < Z)
    (hbind : atomicGroundStateEnergy N q Z < atomicGroundStateEnergy (N - 1) q Z) :
    ∃ ψ : FormDomain N q,
      is_weak_ground_state (fun _ : Fin 1 => Z) (fun _ : Fin 1 => 0)
        (fun _ _ _ => Subsingleton.elim _ _) ψ :=
  exists_atomic_weak_ground_state_of_binding q hq N Z hbind

end LiebThirring.Proofs
end
