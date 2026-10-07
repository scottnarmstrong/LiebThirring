/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Antisymmetric
public import LiebThirring.Defs.KineticEnergy

/-! # Antisymmetric finite-kinetic-energy form domain -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- Unnormalized antisymmetric states with finite Fourier kinetic energy. -/
@[expose] def FormDomain (N q : ℕ) : Type :=
  {ψ : State N q // antisymmetric ψ ∧ kineticEnergy ψ < ⊤}

attribute [reducible] FormDomain

end LiebThirring

end
