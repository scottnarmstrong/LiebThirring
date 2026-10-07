/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.QuantumFormDomain
public import LiebThirring.Thermodynamic.QuantumRepulsionEnergy
public import LiebThirring.Thermodynamic.QuantumAttractionEnergy

/-! # Real joint Coulomb form -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- Both expectations are finite on this finite-kinetic carrier by pair Hardy bounds. -/
@[expose] noncomputable def quantumCoulombEnergy {N M q : ℕ}
    (z : ℕ) (ψ : QuantumFormDomain N M q) : ℝ :=
  (quantumRepulsionEnergy z ψ.val).toReal -
    (quantumAttractionEnergy z ψ.val).toReal

end LiebThirring

end
