/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.DensityMeasure
public import LiebThirring.Electrostatics.Basic

/-! # Thomas–Fermi mutual Coulomb energy -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- The mutual Coulomb form, including the factor one half. -/
@[expose] noncomputable def tfCoulombEnergy (ρ σ : TFDensity) : ℝ :=
  (coulombEnergy (tfDensityMeasure ρ) (tfDensityMeasure σ)).toReal / 2

end LiebThirring

end
