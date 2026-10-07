/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.ConfinedGroundStateEnergy
import LiebThirring.ThermoForm.FiniteConditional
import LiebThirring.Thermodynamic.QuantumStability

/-!
# Finite Dirichlet ball ground energy

A normalized compact trial bounds the infimum above, and quantum stability
bounds it below, so the Dirichlet ball ground energy is a finite real value.
-/

public section

open scoped ENNReal NNReal

namespace LiebThirring.Proofs

theorem confinedGroundStateEnergy_ne_top_ne_bot
    (N M q : ℕ) (hq : 1 ≤ q) (z : ℕ) (hz : 1 ≤ z)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) :
    confinedGroundStateEnergy N M q z m L ≠ ⊤ ∧
      confinedGroundStateEnergy N M q z m L ≠ ⊥ := by
  obtain ⟨C, _hC, hbound⟩ := LiebThirring.quantum_stability q hq z hz
  exact LiebThirring.confinedGroundStateEnergy_ne_top_ne_bot_of_quantum_lower_bound
    N M q hq z m L C (hbound N M m)

end LiebThirring.Proofs

end
