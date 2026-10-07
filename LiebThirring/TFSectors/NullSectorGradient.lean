/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.LocalPartition

/-!
# Gradient energy of a null assignment sector

An assignment sector carrying no state mass also carries no weak-gradient
energy. The proof passes to the open cell, uses uniqueness of weak derivatives
there, and returns across the null boundary.
-/

@[expose] public section

open MeasureTheory
open LiebThirring.TFCubes LiebThirring.Sobolev

namespace LiebThirring.TFSectors

theorem assignmentGradientEnergy_eq_zero_of_sectorProbability_eq_zero
    {N q : ℕ} (ℓ : ℝ) (v : formGraph N q) (b : Fin N → LatticeIndex)
    (hp : sectorProbability ℓ ((v : FormGraphAmbient N q) none) b = 0) :
    assignmentGradientEnergy ℓ v b = 0 := by
  let u : State N q := (v : FormGraphAmbient N q) none
  let Ω := openAssignmentCell ℓ b
  let C := assignmentCell ℓ b
  have hae : Ω =ᵐ[(volume : Measure (Configuration N))] C :=
    openAssignmentCell_ae_eq_assignmentCell ℓ b
  have hC : ‖regionRestrictL2 volume C u‖ ^ 2 = 0 := by
    rw [← sectorProbability_eq_norm_sq_restriction ℓ u b]
    exact hp
  have hΩint : (∫ x in Ω, ‖u x‖ ^ 2) = 0 := by
    rw [setIntegral_congr_set hae, ← norm_sq_regionRestrictL2_eq_integral C u]
    exact hC
  have hΩnorm : ‖regionRestrictL2 volume Ω u‖ = 0 := by
    have hs : ‖regionRestrictL2 volume Ω u‖ ^ 2 = 0 := by
      rw [norm_sq_regionRestrictL2_eq_integral]
      exact hΩint
    exact (sq_eq_zero_iff).mp hs
  let w : localFormGraph N q Ω := restrictFormGraph Ω v
  have hwstate : (w : LocalFormGraphAmbient N q Ω) none = 0 := by
    apply norm_eq_zero.mp
    change ‖regionRestrictL2 volume Ω u‖ = 0
    exact hΩnorm
  have hw : w = 0 := by
    apply localFormGraph_ext_state (isOpen_openAssignmentCell ℓ b)
    change (w : LocalFormGraphAmbient N q Ω) none = (0 : ConfigurationRegionState N q Ω)
    exact hwstate
  have hwenergy : localGradientEnergy (w : LocalFormGraphAmbient N q Ω) = 0 := by
    rw [hw]
    simp [localGradientEnergy]
  calc
    assignmentGradientEnergy ℓ v b =
        localGradientEnergy (w : LocalFormGraphAmbient N q Ω) := by
      unfold assignmentGradientEnergy localGradientEnergy
      apply Finset.sum_congr rfl
      intro a _
      rw [show (restrictFormGraph C v : LocalFormGraphAmbient N q C) (some a) =
          regionRestrictL2 volume C ((v : FormGraphAmbient N q) (some a)) by rfl,
        show (w : LocalFormGraphAmbient N q Ω) (some a) =
          regionRestrictL2 volume Ω ((v : FormGraphAmbient N q) (some a)) by rfl,
        norm_sq_regionRestrictL2_eq_integral,
        norm_sq_regionRestrictL2_eq_integral,
        setIntegral_congr_set hae.symm]
    _ = 0 := hwenergy

end LiebThirring.TFSectors

end
