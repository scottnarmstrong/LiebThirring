/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.Mass
public import LiebThirring.Packing.BallShells
import all Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Explicit Thomas–Fermi trial densities

Constant densities on finite-volume balls supply every nonnegative mass.
the indicator construction is an elementary
implementation of the compact trial required there.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LiebThirring.TFFunctional

/-- Package a literal nonnegative integrable L^{5/3} function as a TF density. -/
@[expose] noncomputable def tfDensityOfFunction (f : Position → ℝ)
    (hp : MemLp f ((5 : ℝ≥0∞) / 3) volume)
    (hn : ∀ᵐ x ∂volume, 0 ≤ f x) (h1 : Integrable f volume) : TFDensity :=
  ⟨hp.toLp f, by
    filter_upwards [hp.coeFn_toLp, hn] with x hx hn'
    rw [hx]
    exact hn', h1.congr hp.coeFn_toLp.symm⟩

theorem tfDensityOfFunction_coeFn (f : Position → ℝ)
    (hp : MemLp f ((5 : ℝ≥0∞) / 3) volume)
    (hn : ∀ᵐ x ∂volume, 0 ≤ f x) (h1 : Integrable f volume) :
    (tfDensityOfFunction f hp hn h1).val =ᵐ[volume] f := hp.coeFn_toLp

/-- A uniform density on a measurable finite-volume set. -/
@[expose] noncomputable def tfIndicatorDensity (s : Set Position)
    (hs : MeasurableSet s) (hv : volume s ≠ ⊤) (b : ℝ≥0) : TFDensity :=
  tfDensityOfFunction (s.indicator fun _ => (b : ℝ))
    (memLp_indicator_const _ hs _ (Or.inr hv))
    (Filter.Eventually.of_forall fun _ => indicator_nonneg (fun _ _ => b.property) _)
    ((integrableOn_const hv).integrable_indicator hs)

theorem tfIndicatorDensity_coeFn (s : Set Position)
    (hs : MeasurableSet s) (hv : volume s ≠ ⊤) (b : ℝ≥0) :
    (tfIndicatorDensity s hs hv b).val =ᵐ[volume] s.indicator fun _ => (b : ℝ) :=
  tfDensityOfFunction_coeFn _ _ _ _

theorem tfMass_tfIndicatorDensity (s : Set Position)
    (hs : MeasurableSet s) (hv : volume s ≠ ⊤) (b : ℝ≥0) :
    tfMass (tfIndicatorDensity s hs hv b) = volume.real s * b := by
  unfold tfMass
  rw [integral_congr_ae (tfIndicatorDensity_coeFn s hs hv b), integral_indicator_const _ hs]
  rfl

theorem norm_tfIndicatorDensity (s : Set Position)
    (hs : MeasurableSet s) (hv : volume s ≠ ⊤) (b : ℝ≥0) :
    ‖(tfIndicatorDensity s hs hv b).val‖ =
      (b : ℝ) * volume.real s ^ ((3 : ℝ) / 5) := by
  change ‖indicatorConstLp ((5 : ℝ≥0∞) / 3) hs hv (b : ℝ)‖ = _
  rw [norm_indicatorConstLp (by norm_num : (5 : ℝ≥0∞) / 3 ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))]
  simp only [Real.norm_eq_abs]
  norm_num [ENNReal.toReal_div]

/-- The constant height of a ball density with the prescribed mass. -/
@[expose] noncomputable def tfBallDensityHeight (ν : ℝ≥0)
    (r : {r : ℝ // 0 < r}) : ℝ≥0 :=
  ⟨(ν : ℝ) / (ballVolumeConstant * r.val ^ 3),
    div_nonneg ν.property (mul_nonneg ballVolumeConstant_pos.le (pow_nonneg r.property.le 3))⟩

/-- A uniform ball trial, normalized to the prescribed mass. -/
@[expose] noncomputable def tfBallDensity (ν : ℝ≥0) (c : Position)
    (r : {r : ℝ // 0 < r}) : TFDensity :=
  tfIndicatorDensity (ball c r.val) measurableSet_ball
    (by rw [volume_ball_position]; finiteness)
    (tfBallDensityHeight ν r)

theorem tfMass_tfBallDensity (ν : ℝ≥0) (c : Position)
    (r : {r : ℝ // 0 < r}) : tfMass (tfBallDensity ν c r) = ν := by
  rw [tfBallDensity, tfMass_tfIndicatorDensity, volume_real_ball_position c r.property.le]
  exact mul_div_cancel₀ _ (mul_ne_zero ballVolumeConstant_pos.ne' (pow_ne_zero 3 r.property.ne'))

theorem norm_tfBallDensity (ν : ℝ≥0) (c : Position)
    (r : {r : ℝ // 0 < r}) :
    ‖(tfBallDensity ν c r).val‖ =
      (ν : ℝ) / (ballVolumeConstant * r.val ^ 3) *
        (ballVolumeConstant * r.val ^ 3) ^ ((3 : ℝ) / 5) := by
  rw [tfBallDensity, norm_tfIndicatorDensity, volume_real_ball_position c r.property.le]
  rfl

/-- Every nonnegative finite mass has an actual TF trial density. -/
theorem exists_tfDensity_mass (ν : ℝ≥0) : ∃ ρ : TFDensity, tfMass ρ = (ν : ℝ) := by
  let s : Set Position := ball 0 1
  have hs : MeasurableSet s := measurableSet_ball
  have hv : volume s ≠ ⊤ := by
    rw [show s = ball (0 : Position) 1 from rfl, volume_ball_position]
    finiteness
  let b : ℝ≥0 := ⟨(ν : ℝ) / ballVolumeConstant,
    div_nonneg ν.property ballVolumeConstant_pos.le⟩
  refine ⟨tfIndicatorDensity s hs hv b, ?_⟩
  rw [tfMass_tfIndicatorDensity]
  change volume.real (ball (0 : Position) 1) * ((ν : ℝ) / ballVolumeConstant) = _
  rw [volume_real_ball_position _ zero_le_one, one_pow, mul_one]
  exact mul_div_cancel₀ _ ballVolumeConstant_pos.ne'

end LiebThirring.TFFunctional

end
