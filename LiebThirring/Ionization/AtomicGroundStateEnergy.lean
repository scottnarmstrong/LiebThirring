/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.GroundStateEnergy

/-! # Atomic ground energy -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- One nucleus of charge `Z` at the origin, in the approved `-Δ` convention. -/
@[expose] noncomputable def atomicGroundStateEnergy (N q : ℕ) (Z : ℝ≥0) : EReal :=
  groundStateEnergy N q 1 (fun _ => Z) (fun _ => 0)
    (fun _ _ _ => Subsingleton.elim _ _)

end LiebThirring

end
