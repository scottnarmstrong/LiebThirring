/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Configuration
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Joint Euclidean electron and nucleus configuration -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- The Euclidean product, with its L² spatial norm and Lebesgue volume. -/
@[expose] def QuantumConfiguration (N M : ℕ) : Type :=
  WithLp 2 (Configuration N × Configuration M)

attribute [reducible] QuantumConfiguration

end LiebThirring

end
