/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Kinetic.Encoding
public import LiebThirring.Kinetic.DensityBasic
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Spaces and slice integrability for one-particle currying

The Hilbert space of the remaining spatial and spin coordinates (currying).

The singled-out spin components with values in the remaining-state space (currying).
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- The Hilbert space of the remaining spatial and spin coordinates (currying). -/
noncomputable abbrev RestState {N : ℕ} (i : Fin N) (q : ℕ) :=
  Lp (EuclideanSpace ℂ (OtherSpinLabels i q)) 2
    (volume : Measure (OtherConfiguration i))

/-- The singled-out spin components with values in the remaining-state space (currying). -/
abbrev OneParticleFiber {N : ℕ} (i : Fin N) (q : ℕ) :=
  PiLp 2 (fun _ : Fin q => RestState i q)

end LiebThirring

end
