/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.ConfinedGroundStateEnergy
import LiebThirring.Proofs.ConfinedVacuumEnergy

/-! # Vacuum normalization and energy -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

theorem confinedGroundStateEnergy_vacuum (q z : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) :
    confinedGroundStateEnergy 0 0 q z m L = 0 :=
  by exact LiebThirring.Proofs.confinedGroundStateEnergy_vacuum q z m L

end LiebThirring

end
