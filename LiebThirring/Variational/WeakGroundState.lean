/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.GroundStateEnergy
public import LiebThirring.Variational.WeakEigenfunction

/-! # Normalized weak ground states -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- A unit weak eigenfunction whose real eigenvalue equals the variational infimum. -/
@[expose] def is_weak_ground_state {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R)
    (ψ : FormDomain N q) : Prop :=
  ‖(ψ : State N q)‖ = 1 ∧
    ∃ E : ℝ, groundStateEnergy N q M z R hR = (E : EReal) ∧
      is_weak_eigenfunction z R hR E ψ

end LiebThirring

end
