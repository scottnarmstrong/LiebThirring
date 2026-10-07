/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCoulomb.RegularDiscrete
import LiebThirring.TFFunctional.DensityBasic

/-! # Approximation of the capped potential by cube suprema

Uniform error `√3 Z₀ ℓ/δ²` and honest attraction integrals on
the entire TF density carrier.
-/

public section

open MeasureTheory
open scoped NNReal

namespace LiebThirring.TFCoulomb

theorem boxCappedPotential_sub_bounds {M : ℕ} {δ ℓ : ℝ}
    (hδ : 0 < δ) (hℓ : 0 < ℓ) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (x : Position) :
    0 ≤ boxCappedPotential δ ℓ z R x - tfCappedNuclearPotential δ z R x ∧
      boxCappedPotential δ ℓ z R x - tfCappedNuclearPotential δ z R x ≤
        Real.sqrt 3 * (∑ k : Fin M, (z k : ℝ)) * ℓ / δ ^ 2 := by
  constructor
  · exact sub_nonneg.mpr (tfCappedNuclearPotential_le_boxCappedPotential hδ hℓ z R x)
  · apply sub_le_iff_le_add.mpr
    apply csSup_le (cubeCappedPotentialValues_nonempty hℓ.le δ z R _)
    rintro v ⟨y, hy, rfl⟩
    have hl := abs_tfCappedNuclearPotential_sub_le hδ z R y x
    have hd := dist_le_lattice_diameter hℓ.le hy
      (latticeCell_subset_closedCell _ _ (mem_latticeCell_label hℓ x))
    have hz : 0 ≤ (∑ k : Fin M, (z k : ℝ)) / δ ^ 2 := by positivity
    have h := (le_abs_self (tfCappedNuclearPotential δ z R y -
      tfCappedNuclearPotential δ z R x)).trans
        (hl.trans (mul_le_mul_of_nonneg_left hd hz))
    have he : ((∑ k : Fin M, (z k : ℝ)) / δ ^ 2) * (Real.sqrt 3 * ℓ) =
        Real.sqrt 3 * (∑ k : Fin M, (z k : ℝ)) * ℓ / δ ^ 2 := by ring
    rw [he] at h
    linarith only [h]

theorem measurable_boxCappedPotential {M : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (δ : ℝ) (z : Fin M → ℝ≥0) (R : Fin M → Position) :
    Measurable (boxCappedPotential δ ℓ z R) :=
  (measurable_of_countable (cubeSupCappedPotential δ ℓ z R)).comp
    (measurable_latticeLabel hℓ)

theorem integrable_boxCappedPotential_mul_tfDensity {M : ℕ} {δ ℓ : ℝ}
    (hδ : 0 < δ) (hℓ : 0 < ℓ) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ρ : TFDensity) : Integrable (fun x : Position => boxCappedPotential δ ℓ z R x * ρ.val x) :=
  (TFFunctional.integrable_tfDensity ρ).bdd_mul
    (measurable_boxCappedPotential hℓ δ z R).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (boxCappedPotential_nonneg hδ hℓ z R x)]
      exact boxCappedPotential_le hδ hℓ z R x)

theorem integrable_tfCappedNuclearPotential_mul_tfDensity {M : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ : TFDensity) :
    Integrable (fun x : Position => tfCappedNuclearPotential δ z R x * ρ.val x) :=
  (TFFunctional.integrable_tfDensity ρ).bdd_mul
    (continuous_tfCappedNuclearPotential hδ z R).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tfCappedNuclearPotential_nonneg hδ z R x)]
      exact tfCappedNuclearPotential_le hδ z R x)

/-- The attraction error is bounded by the uniform potential error times mass. -/
theorem box_attraction_sub_bounds {M : ℕ} {δ ℓ : ℝ}
    (hδ : 0 < δ) (hℓ : 0 < ℓ) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ρ : TFDensity) :
    0 ≤ (∫ x : Position, boxCappedPotential δ ℓ z R x * ρ.val x) -
      (∫ x : Position, tfCappedNuclearPotential δ z R x * ρ.val x) ∧
    (∫ x : Position, boxCappedPotential δ ℓ z R x * ρ.val x) -
      (∫ x : Position, tfCappedNuclearPotential δ z R x * ρ.val x) ≤
        (Real.sqrt 3 * (∑ k : Fin M, (z k : ℝ)) * ℓ / δ ^ 2) * tfMass ρ := by
  have hb := integrable_boxCappedPotential_mul_tfDensity hδ hℓ z R ρ
  have hv := integrable_tfCappedNuclearPotential_mul_tfDensity hδ z R ρ
  rw [← integral_sub hb hv]
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [TFFunctional.tfDensity_ae_nonneg ρ] with x hx
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right
      (tfCappedNuclearPotential_le_boxCappedPotential hδ hℓ z R x) hx)
  · rw [tfMass, ← integral_const_mul]
    apply integral_mono_ae (hb.sub hv) ((TFFunctional.integrable_tfDensity ρ).const_mul _)
    filter_upwards [TFFunctional.tfDensity_ae_nonneg ρ] with x hx
    simp only [Pi.sub_apply]
    rw [← sub_mul]
    exact mul_le_mul_of_nonneg_right (boxCappedPotential_sub_bounds hδ hℓ z R x).2 hx

end LiebThirring.TFCoulomb

end
