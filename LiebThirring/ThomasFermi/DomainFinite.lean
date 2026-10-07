/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.Functional
import LiebThirring.Proofs.DomainFinite

/-! # Finiteness on the entire TF carrier -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- No finite-Coulomb or nuclear-integrability premise is part of the density carrier. -/
theorem tfDensity_integrals_finite {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ σ : TFDensity) :
    coulombEnergy (tfDensityMeasure ρ) (tfDensityMeasure σ) < ⊤ ∧
      Integrable (fun x : Position => tfNuclearPotential z R x * ρ.val x) volume ∧
      Integrable (fun x : Position => (ρ.val x) ^ ((5 : ℝ) / 3)) volume :=
  by exact LiebThirring.Proofs.tfDensity_integrals_finite z R ρ σ

end LiebThirring

end
