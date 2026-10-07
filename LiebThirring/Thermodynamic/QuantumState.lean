/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.QuantumConfiguration

/-! # Correlated joint quantum states -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- Spin labels belong only to the electrons; nuclei are spinless. -/
@[expose] def QuantumState (N M q : ℕ) : Type :=
  Lp (SpinAmplitudes N q) 2 (volume : Measure (QuantumConfiguration N M))

attribute [reducible] QuantumState

end LiebThirring

end
