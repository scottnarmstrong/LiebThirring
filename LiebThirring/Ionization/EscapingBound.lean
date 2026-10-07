/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapingSectorEnergy

/-! # All escaping sectors lie above the atomic removal threshold

Including all proper inside subsets and the vacuum sector.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- The exact estimate lower bound for every normalized antisymmetric finite-energy state. -/
theorem atomic_realEnergy_ge_inside_mass (q : ℕ) (hq : 1 ≤ q) (N : ℕ) (Z : ℝ≥0)
    {R : ℝ} (hR : 0 < R) (u : FormDomain N q) (hu : ‖(u : State N q)‖ = 1) :
    (atomicGroundStateEnergy N q Z).toReal * imsInsideMass hR (u : State N q) +
      (atomicGroundStateEnergy (N - 1) q Z).toReal * (1 - imsInsideMass hR (u : State N q)) -
      (N : ℝ) * (Z : ℝ) / R - (N : ℝ) * Real.pi ^ 2 / (4 * R ^ 2) ≤
      realEnergy (fun _ : Fin 1 => Z) (fun _ => 0)
        (fun _ _ _ => Subsingleton.elim _ _) u :=
  atomic_realEnergy_ge_inside_mass_of_sector_bounds hq Z hR u hu
    (fun S hS => fullRealEnergy_imsRampSector_ge_pred hq Z hR u S hS)

end LiebThirring
end
