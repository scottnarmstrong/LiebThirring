/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.GroundStateEnergy
import LiebThirring.Variational.TrialConstruction
import LiebThirring.Variational.TrialEnergy

/-! # Finite variational ground energy -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring.Proofs

/-- The quantum ground-state energy is finite. -/
theorem groundStateEnergy_ne_top_ne_bot (q : ℕ) (hq : 1 ≤ q)
    (N M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (hR : Function.Injective R) :
    groundStateEnergy N q M z R hR ≠ ⊤ ∧
      groundStateEnergy N q M z R hR ≠ ⊥ := by
  obtain ⟨ψ, hψ⟩ := LiebThirring.exists_normalized_formDomain_trial q hq N
  exact ⟨groundStateEnergy_ne_top_of_trial z R hR ψ hψ,
    groundStateEnergy_ne_bot q hq N M z R hR⟩

end LiebThirring.Proofs

end
