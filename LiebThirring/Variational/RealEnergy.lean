/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormDomain
public import LiebThirring.Defs.Coulomb

/-! # Real Coulomb energy on the form domain -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- The real quadratic energy for distinct fixed nuclei, without normalization. -/
@[expose] noncomputable def realEnergy {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (_hR : Function.Injective R) (ψ : FormDomain N q) : ℝ :=
  (kineticEnergy (ψ : State N q)).toReal +
    (∫⁻ x : Configuration N,
      electronRepulsion x * (‖(ψ : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal +
    (nuclearRepulsion z R).toReal * ‖(ψ : State N q)‖ ^ 2 -
    (∫⁻ x : Configuration N,
      attraction z R x * (‖(ψ : State N q) x‖₊ : ℝ≥0∞) ^ 2).toReal

end LiebThirring

end
