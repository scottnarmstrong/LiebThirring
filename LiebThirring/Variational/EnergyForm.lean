/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormDomain
public import LiebThirring.Defs.Coulomb
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Hermitian Coulomb energy form -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- The literal Coulomb form, conjugate-linear in the first state. -/
@[expose] noncomputable def energyForm {N q M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (_hR : Function.Injective R)
    (φ ψ : FormDomain N q) : ℂ :=
  (∫ ξ : Configuration N, (((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
    inner ℂ
      ((Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)
        (φ : State N q)) ξ)
      ((Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)
        (ψ : State N q)) ξ)) +
    (∫ x : Configuration N,
      (((electronRepulsion x).toReal - (attraction z R x).toReal : ℝ) : ℂ) *
        inner ℂ ((φ : State N q) x) ((ψ : State N q) x)) +
    ((nuclearRepulsion z R).toReal : ℂ) *
      inner ℂ (φ : State N q) (ψ : State N q)

end LiebThirring

end
