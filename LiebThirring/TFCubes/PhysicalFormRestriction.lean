/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.LocalFormGraph
public import LiebThirring.TFCubes.PhysicalRestriction
public import LiebThirring.Sobolev.WeakFormDensity

/-!
# Physical restriction into the local Neumann form domain

State and derivative slots are restricted together. The graph norm and
gradient energy contract. Finite Fourier kinetic energy supplies
the global weak derivatives, rather than assuming a local spectral form.
-/

@[expose] public section

open MeasureTheory Filter
open scoped SchwartzMap Topology
open LiebThirring.Sobolev

namespace LiebThirring.TFCubes

/-- Restriction of all physical graph slots as a linear map. -/
noncomputable def physicalGraphRestrictLinear {N q : ℕ} (Ω : Set (Configuration N)) :
    FormGraphAmbient N q →ₗ[ℂ] LocalFormGraphAmbient N q Ω where
  toFun := fun v ↦ WithLp.toLp 2 (fun i ↦ regionRestrictL2 volume Ω (v i))
  map_add' := by
    intro v w
    apply PiLp.ext
    intro i
    exact (regionRestrictL2Linear (𝕜 := ℂ) volume Ω).map_add (v i) (w i)
  map_smul' := by
    intro c v
    apply PiLp.ext
    intro i
    exact (regionRestrictL2Linear (𝕜 := ℂ) volume Ω).map_smul c (v i)

theorem norm_physicalGraphRestrictLinear_le {N q : ℕ} (Ω : Set (Configuration N))
    (v : FormGraphAmbient N q) : ‖physicalGraphRestrictLinear Ω v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro i _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (norm_regionRestrictL2_le volume Ω (v i))

/-- Continuous linear restriction of the state and every physical derivative. -/
noncomputable def physicalGraphRestrictAmbient {N q : ℕ} (Ω : Set (Configuration N)) :
    FormGraphAmbient N q →L[ℂ] LocalFormGraphAmbient N q Ω :=
  (physicalGraphRestrictLinear Ω).mkContinuous 1 (fun v ↦ by
    simpa only [one_mul] using norm_physicalGraphRestrictLinear_le Ω v)

theorem physicalGraphRestrictAmbient_mem {N q : ℕ} (Ω : Set (Configuration N))
    (v : formGraph N q) :
    physicalGraphRestrictAmbient Ω (v : FormGraphAmbient N q) ∈ localFormGraph N q Ω := by
  intro a
  exact (v.property a).restrict_region Ω

/-- Restriction from the global physical form graph into the full local Neumann graph. -/
noncomputable def restrictFormGraph {N q : ℕ} (Ω : Set (Configuration N)) :
    formGraph N q →L[ℂ] localFormGraph N q Ω :=
  ((physicalGraphRestrictAmbient Ω).comp (formGraph N q).subtypeL).codRestrict
    (localFormGraph N q Ω) (physicalGraphRestrictAmbient_mem Ω)

end LiebThirring.TFCubes

end
