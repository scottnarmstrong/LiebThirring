/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Screening.Exterior
import all LiebThirring.Electrostatics.Basic

/-!
# Coulomb integrability under uniform separation

Finite positive measures separated by a positive distance have an integrable
real Coulomb kernel. This supplies the integrability needed for the four terms
obtained by expanding the mutual energy of two finite signed measures.

-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LiebThirring

/-- The inverse-distance kernel is integrable between finite measures supported
on opposite sides of a positive-width spherical gap. -/
theorem integrable_inverse_norm_prod_of_ball_separation (c : Position)
    (μ ν : Measure Position) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {r ε : ℝ} (hε : 0 < ε) (hs : ∀ᵐ x ∂μ, ‖x-c‖ ≤ r)
    (hy : ∀ᵐ y ∂ν, r + ε ≤ ‖y-c‖) :
    Integrable (fun p : Position × Position => ‖p.1-p.2‖⁻¹) (ν.prod μ) := by
  have hm : Measurable (fun p : Position × Position => ‖p.1-p.2‖⁻¹) := by
    exact (continuous_fst.sub continuous_snd).norm.measurable.inv
  apply Integrable.mono' (integrable_const (ε⁻¹ : ℝ)) hm.aestronglyMeasurable
  have hset : MeasurableSet {p : Position × Position | ε ≤ ‖p.1-p.2‖} :=
    measurableSet_le measurable_const (continuous_fst.sub continuous_snd).norm.measurable
  have hsep : ∀ᵐ p ∂ν.prod μ, ε ≤ ‖p.1-p.2‖ := (Measure.ae_prod_iff_ae_ae hset).2 (by
    filter_upwards [hy] with y hy'
    exact ae_distance_le_of_ball_separation c y μ hs hy'
  )
  filter_upwards [hsep] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact (inv_le_inv₀ (hε.trans_le hp) hε).2 hp

end LiebThirring

end
