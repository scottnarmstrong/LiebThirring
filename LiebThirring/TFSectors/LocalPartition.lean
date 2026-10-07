/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.StateMeasure
public import LiebThirring.TFCubes.PhysicalFormRestriction

/-! # Exact splitting of physical L² mass and weak-gradient energy -/

@[expose] public section
open MeasureTheory Set Function
open LiebThirring.TFCubes LiebThirring.Sobolev
namespace LiebThirring.TFSectors

theorem norm_sq_state_eq_integral {N q : ℕ} (u : State N q) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) u u)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => (norm_sq_eq_re_inner (𝕜 := ℂ) (u x)).symm)

theorem norm_sq_regionRestrictL2_eq_integral {N q : ℕ}
    (Ω : Set (Configuration N)) (u : State N q) :
    ‖regionRestrictL2 volume Ω u‖ ^ 2 = ∫ x in Ω, ‖u x‖ ^ 2 := by
  rw [norm_sq_configurationRegionState]
  exact integral_congr_ae ((regionRestrictL2_ae volume Ω u).fun_comp (fun y => ‖y‖ ^ 2))

theorem sectorProbability_eq_norm_sq_restriction {N q : ℕ}
    (ℓ : ℝ) (u : State N q) (b : Fin N → LatticeIndex) :
    sectorProbability ℓ u b = ‖regionRestrictL2 volume (assignmentCell ℓ b) u‖ ^ 2 := by
  rw [sectorProbability, stateMeasure,
    withDensity_apply _ (measurableSet_assignmentCell ℓ b), norm_sq_regionRestrictL2_eq_integral,
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x => sq_nonneg ‖u x‖))
      ((Lp.memLp u).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).restrict.aestronglyMeasurable]
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]

theorem hasSum_assignment_mass {N q : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (u : State N q) :
    HasSum (fun b : Fin N → LatticeIndex =>
      ‖regionRestrictL2 volume (assignmentCell ℓ b) u‖ ^ 2) (‖u‖ ^ 2) := by
  simp_rw [norm_sq_regionRestrictL2_eq_integral]
  rw [norm_sq_state_eq_integral]
  simpa [iUnion_assignmentCell hℓ] using
    hasSum_integral_iUnion (measurableSet_assignmentCell ℓ)
      (fun _ _ h => assignmentCell_disjoint hℓ h)
      ((Lp.memLp u).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integrableOn

/-- Raw local physical gradient energy, before normalizing a sector state. -/
noncomputable def assignmentGradientEnergy {N q : ℕ} (ℓ : ℝ)
    (v : formGraph N q) (b : Fin N → LatticeIndex) : ℝ :=
  localGradientEnergy (restrictFormGraph (assignmentCell ℓ b) v :
    LocalFormGraphAmbient N q (assignmentCell ℓ b))

/-- The countable physical form split is exact; it loses no boundary energy. -/
theorem hasSum_assignmentGradientEnergy {N q : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (v : formGraph N q) :
    HasSum (assignmentGradientEnergy ℓ v)
      (kineticEnergy ((v : FormGraphAmbient N q) none)).toReal := by
  rw [kineticEnergy_toReal_eq_sum_weakDerivative_norm_sq
    ((v : FormGraphAmbient N q) none) (fun a => (v : FormGraphAmbient N q) (some a))
    (fun a => v.property a)]
  exact hasSum_sum (fun a _ => hasSum_assignment_mass hℓ
    ((v : FormGraphAmbient N q) (some a)))

end LiebThirring.TFSectors
end
