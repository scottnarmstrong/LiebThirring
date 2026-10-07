/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.AtomicGroundStateEnergy
import LiebThirring.Proofs.BindingBound

/-! # Lieb bound from strict atomic binding -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- Strict binding alone forces fewer than `2 Z + 1` electrons. -/
theorem electron_count_lt_of_atomic_binding (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0) (hZ : 0 < Z)
    (hbind : atomicGroundStateEnergy N q Z < atomicGroundStateEnergy (N - 1) q Z) :
    (N : ℝ) < 2 * (Z : ℝ) + 1 :=
  by exact LiebThirring.Proofs.electron_count_lt_of_atomic_binding q hq N Z hZ hbind

end LiebThirring

end
