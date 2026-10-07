/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.DomainFinite

/-!
# Finite Thomas–Fermi density integrals

Hölder estimates near the nuclei and the bounded far-field kernel prove
finiteness of attraction and Coulomb energy for nonnegative L¹ ∩ L⁵ᐟ³ densities.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.Proofs

theorem tfDensity_integrals_finite {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (ρ σ : TFDensity) :
    coulombEnergy (tfDensityMeasure ρ) (tfDensityMeasure σ) < ⊤ ∧
      Integrable (fun x : Position => tfNuclearPotential z R x * ρ.val x) volume ∧
      Integrable (fun x : Position => (ρ.val x) ^ ((5 : ℝ) / 3)) volume :=
  TFFunctional.tfDensity_integrals_finite_library z R ρ σ

end LiebThirring.Proofs

end
