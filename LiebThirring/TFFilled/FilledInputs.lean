/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFilled.OrbitalDensity
public import LiebThirring.TFFilled.UpperInputs

/-! # filled-density convergence consumer inputs for the actual filled orbitals

These results instantiate the analytic limits with the literal enumerated,
zero-extended sine-product orbitals. The filled-density convergence input uses actual
one-particle states at the exact floor count. Source: Lieb–Simon (1977) III.14 (68)–(71), pp.69–71;
III.5 (74)–(78), pp.72–73.
-/

public section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace LiebThirring.TFFilled
open TFUpper

/-- Literal filled-density convergence density reconstruction for every charge, including zero. -/
theorem tfDensitySMul_normalizedMeshDensity_filledCubeOrbitals_ae
    {B : ℕ} (q : {q : ℕ // 1 ≤ q}) (g : CubeMesh B) (a : ℝ≥0) :
    (TFFunctional.tfDensitySMul a (normalizedMeshDensity q.val q.property g a)).val
      =ᵐ[volume] slaterOrbitalDensity (filledCubeOrbitals q g a) :=
  tfDensitySMul_normalizedMeshDensity_slater_ae_of_representation
    q.val q.property g a (filledCubeOrbitals q g a)
    (slaterOrbitalDensity_filledCubeOrbitals_ae q g a)

end LiebThirring.TFFilled
end
