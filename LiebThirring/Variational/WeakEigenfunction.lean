/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.EnergyForm

/-! # Weak eigenfunctions of the Coulomb form -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- A nonzero form-domain state satisfying the weak equation at a real eigenvalue. -/
@[expose] def is_weak_eigenfunction {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R)
    (E : ℝ) (ψ : FormDomain N q) : Prop :=
  (ψ : State N q) ≠ 0 ∧
    ∀ φ : FormDomain N q,
      energyForm z R hR φ ψ = (E : ℂ) * inner ℂ (φ : State N q) (ψ : State N q)

end LiebThirring

end
