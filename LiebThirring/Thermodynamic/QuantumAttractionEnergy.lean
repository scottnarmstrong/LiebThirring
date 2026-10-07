/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.QuantumState
public import LiebThirring.Defs.Coulomb

/-! # Joint attractive Coulomb expectation -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- Electron-nucleus attraction with constant integer nuclear charge. -/
@[expose] noncomputable def quantumAttractionEnergy {N M q : ℕ}
    (z : ℕ) (ψ : QuantumState N M q) : ℝ≥0∞ :=
  ∫⁻ X : QuantumConfiguration N M,
    attraction (fun _ : Fin M => (z : ℝ≥0))
      (fun k => particlePosition X.snd k) X.fst * (‖ψ X‖₊ : ℝ≥0∞) ^ 2

end LiebThirring

end
