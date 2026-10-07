/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.LocalPartition

/-!
# Mass and physical energy across the null assignment boundary

Only numerical masses and gradient energies of actual global restrictions are
transported. No identification of weak form graphs from a.e. set equality is
assumed: the global physical graph independently restricts into each local form.
-/

@[expose] public section
open MeasureTheory
open LiebThirring.TFCubes LiebThirring.Sobolev
namespace LiebThirring.TFSectors

theorem norm_sq_openAssignmentRestriction_eq {N q : ℕ} (ℓ : ℝ)
    (b : Fin N → LatticeIndex) (u : State N q) :
    ‖regionRestrictL2 volume (openAssignmentCell ℓ b) u‖ ^ 2 =
      ‖regionRestrictL2 volume (assignmentCell ℓ b) u‖ ^ 2 := by
  rw [norm_sq_regionRestrictL2_eq_integral, norm_sq_regionRestrictL2_eq_integral]
  exact setIntegral_congr_set (openAssignmentCell_ae_eq_assignmentCell ℓ b)

theorem sectorProbability_eq_norm_sq_openRestriction {N q : ℕ} (ℓ : ℝ)
    (u : State N q) (b : Fin N → LatticeIndex) :
    sectorProbability ℓ u b = ‖regionRestrictL2 volume (openAssignmentCell ℓ b) u‖ ^ 2 := by
  rw [norm_sq_openAssignmentRestriction_eq, sectorProbability_eq_norm_sq_restriction]

theorem localGradientEnergy_openAssignmentRestriction_eq {N q : ℕ} (ℓ : ℝ)
    (v : formGraph N q) (b : Fin N → LatticeIndex) :
    localGradientEnergy (restrictFormGraph (openAssignmentCell ℓ b) v :
      LocalFormGraphAmbient N q (openAssignmentCell ℓ b)) =
        assignmentGradientEnergy ℓ v b := by
  unfold localGradientEnergy assignmentGradientEnergy
  apply Finset.sum_congr rfl
  intro a _
  exact norm_sq_openAssignmentRestriction_eq ℓ b ((v : FormGraphAmbient N q) (some a))

end LiebThirring.TFSectors
end
