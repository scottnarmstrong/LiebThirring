/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.FourierWeak
public import LiebThirring.Sobolev.SchwartzCutoffWeak

/-! # Compact-test weak derivatives and Fourier coordinate multipliers -/

public section

open MeasureTheory LineDeriv
open scoped SchwartzMap FourierTransform

namespace LiebThirring.Sobolev

/-- A weak coordinate derivative is exactly the `2πiξₐ` L² Fourier multiplier. -/
theorem hasWeakDerivative_iff_fourier_eq_symbol {N q : ℕ} (a : Fin N × Fin 3)
    (u g : State N q) :
    HasWeakDerivative a u g ↔
      ∀ᵐ ξ, (𝓕 g) ξ = frequencySymbol a ξ • (𝓕 u) ξ := by
  constructor
  · intro h
    apply fourier_eq_symbol_of_schwartz_tests a u g
    intro η
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using h.schwartz_test η
  · exact hasWeakDerivative_of_fourier_eq_symbol a u g

end LiebThirring.Sobolev

end
