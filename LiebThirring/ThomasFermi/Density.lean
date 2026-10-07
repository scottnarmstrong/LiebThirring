/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Configuration
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Thomas–Fermi trial densities -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- Nonnegative a.e. classes in L¹ ∩ L^{5/3}, with no quantum representability restriction. -/
@[expose] def TFDensity : Type :=
  {ρ : Lp ℝ ((5 : ℝ≥0∞) / 3) (volume : Measure Position) //
    (∀ᵐ x ∂(volume : Measure Position), 0 ≤ ρ x) ∧
      Integrable (fun x : Position => ρ x) volume}

end LiebThirring

end
