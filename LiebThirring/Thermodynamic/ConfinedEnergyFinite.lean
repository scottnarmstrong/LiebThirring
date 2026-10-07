/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.ConfinedGroundStateEnergy
import LiebThirring.Proofs.ConfinedEnergyFinite

/-! # Finite confined ground energy -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

theorem confinedGroundStateEnergy_ne_top_ne_bot
    (N M q : ℕ) (hq : 1 ≤ q) (z : ℕ) (hz : 1 ≤ z)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) :
    confinedGroundStateEnergy N M q z m L ≠ ⊤ ∧
      confinedGroundStateEnergy N M q z m L ≠ ⊥ :=
  by exact LiebThirring.Proofs.confinedGroundStateEnergy_ne_top_ne_bot N M q hq z hz m L

end LiebThirring

end
