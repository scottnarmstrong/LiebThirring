/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.AtomicGroundStateEnergy
import LiebThirring.Proofs.EscapeMonotonicity

/-! # Escape monotonicity for atomic energies -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- Sending one electron to infinity cannot increase the atomic ground energy. -/
theorem atomicGroundStateEnergy_le_pred (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (Z : ℝ≥0) :
    atomicGroundStateEnergy N q Z ≤ atomicGroundStateEnergy (N - 1) q Z :=
  by exact LiebThirring.Proofs.atomicGroundStateEnergy_le_pred q hq N Z

end LiebThirring

end
