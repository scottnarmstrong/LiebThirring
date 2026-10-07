/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.GroundStateEnergy

/-! # Electronic quantum variational infimum -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- Electronic energy T+B−A, omitting the nuclear constant, on the form domain. -/
@[expose] noncomputable def electronicGroundStateEnergy (N q M : ℕ)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) : EReal :=
  ⨅ ψ : {ψ : FormDomain N q // ‖(ψ : State N q)‖ = 1},
    (((kineticEnergy (ψ.val : State N q)).toReal +
      (∫⁻ x : Configuration N,
        electronRepulsion x * (‖(ψ.val : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal -
      (∫⁻ x : Configuration N,
        attraction z R x * (‖(ψ.val : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal : ℝ) : EReal)

end LiebThirring

end
