/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.AtomicGroundStateEnergy
import LiebThirring.Ionization.BindingGroundStateExists
import LiebThirring.Ionization.WeakGroundStateBound

/-!
# Atomic ionization under strict binding

Strict removal binding gives a weak ground state by localization and compactness.
The weak-ground-state estimate then gives fewer than 2 Z + 1 electrons.
Source: Lieb (1984), Theorem 1 and equation (2.9).
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring.Proofs

theorem electron_count_lt_of_atomic_binding (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0) (hZ : 0 < Z)
    (hbind : atomicGroundStateEnergy N q Z < atomicGroundStateEnergy (N - 1) q Z) :
    (N : ℝ) < 2 * (Z : ℝ) + 1 := by
  obtain ⟨ψ, hψ⟩ := LiebThirring.exists_atomic_weak_ground_state_of_lt q hq N Z hZ hbind
  exact LiebThirring.electron_count_lt_of_atomic_weak_ground_state q hq N Z hZ ψ hψ

end LiebThirring.Proofs

end
