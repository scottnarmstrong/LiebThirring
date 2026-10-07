/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.FilledOrbitals
public import LiebThirring.TFUpper.DirichletKinetic

/-! # The kinetic energy of the occupied cube family

The exact one-particle identity is summed over the selected positive lattice
modes, including their spin labels. This is a finite-family identity and does
not use completeness. Source: Lieb–Simon (1977) III.11/III.13, the cube spectral theory/Slater upper bound.
-/

public section
open scoped NNReal
namespace LiebThirring.TFUpper

theorem occupiedPositiveMode_eigenvalue {B : ℕ} (q : ℕ) (hq : 0 < q)
    (g : CubeMesh B) (α : ℝ≥0) (i : OccupiedModeIndex q hq g α) :
    TFCubes.dirichletCubeEigenvalue g.side (occupiedPositiveMode q hq g α i) =
      TFLattice.cubeEigenvalue g.side i.2.val := by
  rw [TFCubes.dirichletCubeEigenvalue_eq]
  have h := congrArg Prod.fst (occupiedPositiveMode_coe q hq g α i)
  change (fun a => ((occupiedPositiveMode q hq g α i).1 a : ℕ)) = i.2.val.1 at h
  rw [h]
  rfl

theorem kineticEnergy_cubeTrialOrbitals_lt_top {B : ℕ}
    (q : {q : ℕ // 1 ≤ q}) (g : CubeMesh B) (α : ℝ≥0)
    (i : Fin (occupationCount α g.mass)) :
    kineticEnergy (cubeTrialOrbitals q g α i) < ⊤ :=
  kineticEnergy_dirichletCubeOrbital_lt_top g.side _ _

theorem kineticEnergy_cubeTrialOrbitals_toReal {B : ℕ}
    (q : {q : ℕ // 1 ≤ q}) (g : CubeMesh B) (α : ℝ≥0)
    (i : Fin (occupationCount α g.mass)) :
    (kineticEnergy (cubeTrialOrbitals q g α i)).toReal =
      TFLattice.cubeEigenvalue g.side
        (occupiedModeEquiv q.val q.property g α i).2.val := by
  change (kineticEnergy (dirichletCubeOrbital g.side _ _)).toReal = _
  rw [kineticEnergy_dirichletCubeOrbital_toReal]
  exact occupiedPositiveMode_eigenvalue q.val q.property g α _

/-- Exact classical kinetic sum at the literal floored particle count. -/
theorem sum_kineticEnergy_cubeTrialOrbitals {B : ℕ}
    (q : {q : ℕ // 1 ≤ q}) (g : CubeMesh B) (α : ℝ≥0) :
    (∑ i, (kineticEnergy (cubeTrialOrbitals q g α i)).toReal) =
      occupiedCubeKinetic q.val q.property g.side α g.mass := by
  simp_rw [kineticEnergy_cubeTrialOrbitals_toReal]
  exact sum_occupiedModeEquiv_eigenvalue q.val q.property g α

end LiebThirring.TFUpper
end
