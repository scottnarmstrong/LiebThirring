/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.CoulombEnergy
public import LiebThirring.ThomasFermi.NuclearPotential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Electronic Thomas–Fermi functional -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- The electronic TF functional; a is the entire positive kinetic coefficient. -/
@[expose] noncomputable def tfFunctional {M : ℕ} (a : {a : ℝ // 0 < a})
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ : TFDensity) : ℝ :=
  a.val * (∫ x : Position, (ρ.val x) ^ ((5 : ℝ) / 3)) -
    (∫ x : Position, tfNuclearPotential z R x * ρ.val x) +
    tfCoulombEnergy ρ ρ

end LiebThirring

end
