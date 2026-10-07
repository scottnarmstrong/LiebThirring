/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFilled.MeshDensity
public import LiebThirring.TFLattice.KineticScaling
public import LiebThirring.TFUpper.Approximate

/-! # Consumption of filled-density convergence by the Slater upper bound

Filled-density convergence supplies the actual density and both strong limits. The adapters consume the
remaining cube spectral theory orbital representation explicitly. The final adapter discharges
sharp eigenvalue sums using its proved finite-mesh limit; the earlier, separately named conditional
helper retains the external-limit interface. Neither input occurs in the density
convergence theorems. Proof: filled-density convergence–Slater upper bound, Lieb–Simon (1977) III.14 pp.69–71 and III.5 pp.72–73.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace LiebThirring.TFFilled
open TFUpper

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨one_le_five_thirds⟩

/-- Conditional cube spectral theory adapter: literal mode-density representation supplies the all-j
orbital density equation used by TFUpper, including zero occupation. -/
theorem tfDensitySMul_normalizedMeshDensity_slater_ae_of_representation
    {B : ℕ} (q : ℕ) (hq : 0 < q) (g : CubeMesh B) (a : ℝ≥0)
    (u : Fin (occupationCount a g.mass) → State 1 q)
    (hu : slaterOrbitalDensity u =ᵐ[volume] meshFilledDensity q hq g a) :
    (TFFunctional.tfDensitySMul a (normalizedMeshDensity q hq g a)).val =ᵐ[volume]
      slaterOrbitalDensity u :=
  (tfDensitySMul_normalizedMeshDensity_ae q hq g a).trans hu.symm

end LiebThirring.TFFilled
end
