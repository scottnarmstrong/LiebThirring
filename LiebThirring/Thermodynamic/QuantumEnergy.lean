/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.QuantumCoulombEnergy
public import LiebThirring.Thermodynamic.NuclearKineticCoefficient

/-! # Unnormalized quantum Coulomb energy -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- Full joint energy; no fixed-nucleus minimization occurs. -/
@[expose] noncomputable def quantumEnergy {N M q : ℕ}
    (z : ℕ) (m : {m : ℝ≥0 // 0 < m}) (ψ : QuantumFormDomain N M q) : ℝ :=
  (quantumElectronKineticEnergy ψ.val).toReal +
    (nuclearKineticCoefficient m : ℝ) * (quantumNuclearKineticEnergy ψ.val).toReal +
    quantumCoulombEnergy z ψ

end LiebThirring

end
