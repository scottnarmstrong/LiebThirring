/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.Density

/-! # Thomas–Fermi density mass -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- The Lebesgue mass of a Thomas–Fermi density. -/
@[expose] noncomputable def tfMass (ρ : TFDensity) : ℝ :=
  ∫ x : Position, ρ.val x

end LiebThirring

end
