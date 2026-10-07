/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.AtomicGroundStateEnergy
public import LiebThirring.Variational.WeakGroundState
import LiebThirring.Proofs.WeakGroundStateBound

/-! # Lieb bound for normalized weak atomic ground states -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- Every normalized weak atomic ground state has fewer than `2 Z + 1` electrons. -/
theorem electron_count_lt_of_atomic_weak_ground_state (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0) (hZ : 0 < Z) (ψ : FormDomain N q)
    (hψ : is_weak_ground_state (fun _ : Fin 1 => Z) (fun _ : Fin 1 => 0)
      (fun _ _ _ => Subsingleton.elim _ _) ψ) :
    (N : ℝ) < 2 * (Z : ℝ) + 1 :=
  by exact LiebThirring.Proofs.electron_count_lt_of_atomic_weak_ground_state q hq N Z hZ ψ hψ

end LiebThirring

end
