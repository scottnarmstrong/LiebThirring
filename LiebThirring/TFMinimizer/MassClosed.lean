/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.DensityBasic

/-! # Closed relaxed mass constraint in the TF Lp carrier

An almost everywhere subsequence and Fatou reconstruct the integrable limit.
strong-Cauchy adaptation (direct proof).
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LiebThirring.TFMinimizer

open TFFunctional

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

/-- A strong L5/3 limit of nonnegative densities with bounded mass is an actual
TF density with the same mass cap; mass convergence is not asserted. -/
theorem exists_tfDensity_of_tendsto_mass_le (ν : ℝ≥0) (f : ℕ → TFDensity)
    (hcap : ∀ j, tfMass (f j) ≤ (ν : ℝ))
    (g : Lp ℝ ((5 : ℝ≥0∞) / 3) (volume : Measure Position))
    (hg : Tendsto (fun j => (f j).val) atTop (𝓝 g)) :
    ∃ ρ : TFDensity, ρ.val = g ∧ tfMass ρ ≤ (ν : ℝ) := by
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae
  have hn : ∀ᵐ x ∂(volume : Measure Position), 0 ≤ g x := by
    filter_upwards [hae, ae_all_iff.mpr (fun j => tfDensity_ae_nonneg (f (ns j)))]
      with x hx hnonneg
    exact ge_of_tendsto' hx hnonneg
  have hl : (∫⁻ x : Position, ENNReal.ofReal (g x)) ≤ ENNReal.ofReal (ν : ℝ) := by
    calc
      _ = ∫⁻ x : Position, liminf (fun j => ENNReal.ofReal ((f (ns j)).val x)) atTop := by
        apply lintegral_congr_ae
        filter_upwards [hae] with x hx
        exact ((ENNReal.continuous_ofReal.tendsto (g x)).comp hx).liminf_eq.symm
      _ ≤ liminf (fun j => ∫⁻ x : Position,
          ENNReal.ofReal ((f (ns j)).val x)) atTop :=
        lintegral_liminf_le' (fun j => (Lp.aestronglyMeasurable (f (ns j)).val).aemeasurable.ennreal_ofReal)
      _ ≤ limsup (fun j => ∫⁻ x : Position,
          ENNReal.ofReal ((f (ns j)).val x)) atTop := liminf_le_limsup
      _ ≤ _ := by
        apply limsup_le_of_le (by isBoundedDefault)
        apply Eventually.of_forall
        intro j
        rw [← ofReal_integral_eq_lintegral_ofReal (integrable_tfDensity (f (ns j)))
          (tfDensity_ae_nonneg (f (ns j)))]
        exact ENNReal.ofReal_le_ofReal (hcap (ns j))
  have hi : Integrable (fun x : Position => g x) volume :=
    (lintegral_ofReal_ne_top_iff_integrable (Lp.aestronglyMeasurable g) hn).mp
      (ne_of_lt (lt_of_le_of_lt hl ENNReal.ofReal_lt_top))
  refine ⟨⟨g, hn, hi⟩, rfl, ?_⟩
  change (∫ x : Position, g x) ≤ (ν : ℝ)
  apply (ENNReal.ofReal_le_ofReal_iff ν.property).mp
  rwa [ofReal_integral_eq_lintegral_ofReal hi hn]

end LiebThirring.TFMinimizer

end
