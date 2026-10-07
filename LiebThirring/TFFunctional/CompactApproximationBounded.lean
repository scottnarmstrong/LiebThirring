/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.DensityBasic

/-! # Compact continuous approximation of bounded nonnegative densities -/

public section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace LiebThirring.TFFunctional

/-- Clamping a compactly supported continuous approximation preserves its L1 error
against a function taking values in the same nonnegative interval. -/
theorem exists_compact_nonneg_eLpNorm_one_approximation
    (u : Position → ℝ) (hu : Integrable u volume) (C : ℝ) (hC : 0 ≤ C)
    (hu0 : ∀ᵐ x ∂volume, 0 ≤ u x) (huC : ∀ᵐ x ∂volume, u x ≤ C)
    (δ : ℝ≥0∞) (hδ : δ ≠ 0) :
    ∃ f : Position → ℝ, (∀ x, 0 ≤ f x) ∧ Continuous f ∧ HasCompactSupport f ∧
      eLpNorm (f - u) 1 volume ≤ δ ∧ (∀ x, f x ≤ C) := by
  obtain ⟨g, hgcomp, hgerr, hgcont, hgint⟩ :=
    (memLp_one_iff_integrable.mpr hu).exists_hasCompactSupport_eLpNorm_sub_le
      ENNReal.one_ne_top hδ
  rw [eLpNorm_sub_comm] at hgerr
  let f : Position → ℝ := fun x => (projIcc 0 C hC (g x)).val
  have hfcont : Continuous f := continuous_subtype_val.comp (continuous_projIcc.comp hgcont)
  have hfcomp : HasCompactSupport f := by
    change HasCompactSupport ((fun y : ℝ => (projIcc 0 C hC y).val) ∘ g)
    apply hgcomp.comp_left
    simp
  have hferr : eLpNorm (f - u) 1 volume ≤ δ := by
    apply (eLpNorm_mono_ae ((hfcont.aestronglyMeasurable.sub hu.aestronglyMeasurable)) ?_).trans hgerr
    filter_upwards [hu0, huC] with x hx0 hxC
    change ‖f x - u x‖ ≤ ‖g x - u x‖
    have hlip := (LipschitzWith.projIcc hC).dist_le_mul (g x) (u x)
    rw [projIcc_of_mem hC ⟨hx0, hxC⟩] at hlip
    simpa only [f, NNReal.coe_one, one_mul, Real.dist_eq, Subtype.dist_eq,
      Real.norm_eq_abs] using hlip
  exact ⟨f, fun x => (projIcc 0 C hC (g x)).property.1, hfcont, hfcomp, hferr,
    fun x => (projIcc 0 C hC (g x)).property.2⟩

end LiebThirring.TFFunctional

end
