/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.TrialDensities
public import LiebThirring.TFFunctional.DensityBasic

/-! # A linear minimum over the nonnegative mass cap

The elementary multiplier argument for the TF equation. Normalized indicator
tests determine the lower bound of the first variation; its weighted equality
and complementary slackness follow from a comparison with zero. The mass cap,
rather than the possibly zero minimizer mass, is the denominator.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LiebThirring.TFMinimizer

open TFFunctional

theorem integral_pair_tfIndicatorDensity (g : Position → ℝ) (s : Set Position)
    (hs : MeasurableSet s) (hv : volume s ≠ ⊤) (b : ℝ≥0) :
    (∫ x : Position, g x * (tfIndicatorDensity s hs hv b).val x) =
      (b : ℝ) * ∫ x in s, g x := by
  calc
    _ = ∫ x : Position, (b : ℝ) * s.indicator g x := by
      apply integral_congr_ae
      filter_upwards [tfIndicatorDensity_coeFn s hs hv b] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs, mul_comm]
    _ = _ := by rw [integral_const_mul, integral_indicator hs]

theorem integrableOn_of_integrable_tfIndicator_pair (g : Position → ℝ)
    (s : Set Position) (hs : MeasurableSet s) (hv : volume s ≠ ⊤)
    (hg : Integrable (fun x : Position => g x * (tfIndicatorDensity s hs hv 1).val x)
      volume) : IntegrableOn g s volume := by
  apply (integrable_indicator_iff hs).mp
  apply hg.congr
  filter_upwards [tfIndicatorDensity_coeFn s hs hv 1] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- KKT data for a linear functional minimized on the TF mass cap. -/
theorem linear_mass_minimum (ν : ℝ≥0) (hν : 0 < ν) (g : Position → ℝ)
    (hpair : ∀ σ : TFDensity, Integrable (fun x : Position => g x * σ.val x) volume)
    (ρ : TFDensity) (hmass : tfMass ρ ≤ (ν : ℝ))
    (hlinear : ∀ σ : TFDensity, tfMass σ ≤ (ν : ℝ) →
      (∫ x : Position, g x * ρ.val x) ≤ ∫ x : Position, g x * σ.val x)
    (hself : (∫ x : Position, g x * ρ.val x) ≤ 0) :
    ∃ μ : ℝ≥0, (∀ᵐ x ∂(volume : Measure Position),
      -(μ : ℝ) ≤ g x ∧ (g x + (μ : ℝ)) * ρ.val x = 0) ∧
      (μ : ℝ) * ((ν : ℝ) - tfMass ρ) = 0 := by
  let I : ℝ := ∫ x : Position, g x * ρ.val x
  let ℓ : ℝ := I / (ν : ℝ)
  have hνr : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hℓ : ℓ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hself hνr.le
  have hℓν : ℓ * (ν : ℝ) = I := div_mul_cancel₀ I hνr.ne'
  have hge : ∀ᵐ x ∂(volume : Measure Position), 0 ≤ g x - ℓ := by
    apply ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
    · intro s hs hv
      exact (integrableOn_of_integrable_tfIndicator_pair g s hs hv.ne (hpair _)).sub
        (integrableOn_const hv.ne)
    · intro s hs hv
      by_cases hz : volume s = 0
      · simp [Measure.restrict_eq_zero.mpr hz]
      have hvr : 0 < volume.real s := ENNReal.toReal_pos hz hv.ne
      let b : ℝ≥0 := ⟨(ν : ℝ) / volume.real s, div_nonneg ν.property hvr.le⟩
      have hb : 0 < (b : ℝ) := div_pos hνr hvr
      have hbm : volume.real s * (b : ℝ) = (ν : ℝ) := by
        exact mul_div_cancel₀ _ hvr.ne'
      have hm : tfMass (tfIndicatorDensity s hs hv.ne b) = (ν : ℝ) := by
        rw [tfMass_tfIndicatorDensity]
        exact hbm
      have hi := hlinear (tfIndicatorDensity s hs hv.ne b) hm.le
      rw [integral_pair_tfIndicatorDensity] at hi
      have he : (b : ℝ) * (volume.real s * ℓ) = I := by
        rw [mul_comm (volume.real s) ℓ, ← mul_assoc, mul_comm (b : ℝ) ℓ,
          mul_assoc, mul_comm (b : ℝ) (volume.real s), hbm, hℓν]
      have hlo : volume.real s * ℓ ≤ ∫ x in s, g x := by
        apply (mul_le_mul_iff_of_pos_left hb).mp
        rw [he]
        exact hi
      rw [integral_sub
        (integrableOn_of_integrable_tfIndicator_pair g s hs hv.ne (hpair _))
        (integrableOn_const hv.ne), setIntegral_const, smul_eq_mul]
      exact sub_nonneg.mpr hlo
  have hgapint : Integrable (fun x : Position => (g x - ℓ) * ρ.val x) volume := by
    have h := (hpair ρ).sub ((integrable_tfDensity ρ).const_mul ℓ)
    apply h.congr
    filter_upwards [] with x
    dsimp
    ring
  have hgap : ∀ᵐ x ∂(volume : Measure Position), 0 ≤ (g x - ℓ) * ρ.val x := by
    filter_upwards [hge, tfDensity_ae_nonneg ρ] with x hx hy
    exact mul_nonneg hx hy
  have hgapval : (∫ x : Position, (g x - ℓ) * ρ.val x) = I - ℓ * tfMass ρ := by
    simp_rw [sub_mul]
    rw [integral_sub (hpair ρ) ((integrable_tfDensity ρ).const_mul ℓ), integral_const_mul]
    rfl
  have hslack : ℓ * ((ν : ℝ) - tfMass ρ) = 0 := by
    have hn : 0 ≤ ℓ * ((ν : ℝ) - tfMass ρ) := by
      have h := integral_nonneg_of_ae hgap
      rw [hgapval, ← hℓν] at h
      nlinarith only [h]
    exact le_antisymm (mul_nonpos_of_nonpos_of_nonneg hℓ (sub_nonneg.mpr hmass)) hn
  have hzero : ∀ᵐ x ∂(volume : Measure Position), (g x - ℓ) * ρ.val x = 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae hgap hgapint).mp
    rw [hgapval, ← hℓν]
    nlinarith only [hslack]
  refine ⟨⟨-ℓ, neg_nonneg.mpr hℓ⟩, ?_, ?_⟩
  · filter_upwards [hge, hzero] with x hx hz
    change -(-ℓ) ≤ g x ∧ (g x + -ℓ) * ρ.val x = 0
    constructor
    · simpa only [neg_neg] using sub_nonneg.mp hx
    · simpa only [sub_eq_add_neg] using hz
  · change -ℓ * ((ν : ℝ) - tfMass ρ) = 0
    rw [neg_mul, hslack, neg_zero]

end LiebThirring.TFMinimizer

end
