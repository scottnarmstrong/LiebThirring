/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.Density
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Measure associated with a TF density -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- The absolutely continuous positive measure ρ dx. -/
@[expose] noncomputable def tfDensityMeasure (ρ : TFDensity) : Measure Position :=
  volume.withDensity (fun x : Position => ENNReal.ofReal (ρ.val x))

end LiebThirring

end
