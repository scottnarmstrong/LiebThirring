/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.QuantumAntisymmetric
public import LiebThirring.Thermodynamic.NuclearSymmetric
public import LiebThirring.Thermodynamic.QuantumElectronKineticEnergy
public import LiebThirring.Thermodynamic.QuantumNuclearKineticEnergy

/-! # Joint finite kinetic form domain -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- Unnormalized joint H¹ states with the two species statistics. -/
@[expose] def QuantumFormDomain (N M q : ℕ) : Type :=
  {ψ : QuantumState N M q //
    quantum_antisymmetric ψ ∧ nuclear_symmetric ψ ∧
      quantumElectronKineticEnergy ψ < ⊤ ∧ quantumNuclearKineticEnergy ψ < ⊤}

attribute [reducible] QuantumFormDomain

end LiebThirring

end
