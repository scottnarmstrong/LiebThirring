/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.Dilation

/-! # Measure transport for dilated Thomas--Fermi densities -/

public section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace LiebThirring
theorem tfDensityMeasure_tfDensityDilation (β A : ℝ) (hβ : 0 < β) (hA : 0 ≤ A)
    (ρ : TFDensity) :
    tfDensityMeasure (tfDensityDilation β A hβ hA ρ) =
      (ENNReal.ofReal A * ENNReal.ofReal ((β ^ 3)⁻¹)) •
        (tfDensityMeasure ρ).map (fun x : Position => β⁻¹ • x) := by
  apply Measure.ext
  intro s hs
  rw [tfDensityMeasure, withDensity_apply _ hs,
    Measure.smul_apply, Measure.map_apply (measurable_const_smul β⁻¹) hs,
    tfDensityMeasure, withDensity_apply _
      (hs.preimage (measurable_const_smul β⁻¹))]
  have hm : Measure.map (fun x : Position => β • x) volume =
      ENNReal.ofReal ((β ^ 3)⁻¹) • volume := by
    simpa only [Position, finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hβ 3))]
      using Measure.map_addHaar_smul (volume : Measure Position) hβ.ne'
  let g : Position → ℝ≥0∞ := fun y => ((fun x : Position => β⁻¹ • x) ⁻¹' s).indicator (fun y => ENNReal.ofReal (ρ.val y)) y
  have hgvol : AEMeasurable g volume :=
    ((Lp.memLp ρ.val).aestronglyMeasurable.aemeasurable.ennreal_ofReal.indicator (hs.preimage (measurable_const_smul β⁻¹)))
  have hgmap : AEMeasurable g (Measure.map (fun x : Position => β • x) volume) := by
    rw [hm]
    exact (aemeasurable_smul_measure_iff (by positivity)).2 hgvol
  have hmap := lintegral_map' hgmap (measurable_const_smul β).aemeasurable
  rw [hm, lintegral_smul_measure] at hmap
  rw [← lintegral_indicator hs, ← lintegral_indicator
    (hs.preimage (measurable_const_smul β⁻¹))]
  calc
    _ = ENNReal.ofReal A * ∫⁻ x, s.indicator (fun x => ENNReal.ofReal (ρ.val (β • x))) x := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr_ae
      filter_upwards [tfDensityDilation_coe_ae β A hβ hA ρ,
        (Measure.quasiMeasurePreserving_smul (volume : Measure Position) hβ.ne').ae
          ρ.property.1] with x hx hρ
      by_cases hxs : x ∈ s
      · simp [hxs]
        rw [hx]
        simp only [tfDensityDilationFn, ENNReal.ofReal_mul hA]
      · simp [hxs]
    _ = ENNReal.ofReal A * (ENNReal.ofReal ((β^3)⁻¹) * ∫⁻ y, g y) := by
      congr 1
      calc
        _ = ∫⁻ x, g (β • x) := by
          apply lintegral_congr
          intro x
          dsimp only [g]
          by_cases hx : x ∈ s
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem]
            simpa only [Set.mem_preimage, smul_smul, inv_mul_cancel₀ hβ.ne', one_smul]
              using hx
          · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
            simpa only [Set.mem_preimage, smul_smul, inv_mul_cancel₀ hβ.ne', one_smul]
              using hx
        _ = _ := by simpa only [smul_eq_mul] using hmap.symm
    _ = (ENNReal.ofReal A * ENNReal.ofReal ((β^3)⁻¹)) *
        ∫⁻ a, ((fun x : Position => β⁻¹ • x) ⁻¹' s).indicator
          (fun a => ENNReal.ofReal (ρ.val a)) a := by
      simp only [g, mul_assoc]
end LiebThirring

end
