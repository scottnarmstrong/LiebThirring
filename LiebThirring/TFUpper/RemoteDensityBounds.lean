/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.RemoteDensity
public import LiebThirring.TFFunctional.DensityBasic

/-! # Uniform Coulomb bounds for remote-orbital densities

The scaling argument for the particle-number correction is `direct proof`;
the complete proof is given by the explicit dilation and change-of-variables
lemmas below.
-/

public section

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace LiebThirring.TFUpper

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by simp) (by norm_num))).mp
  rw [ENNReal.toReal_div]
  norm_num⟩

theorem remoteOrbitalDensityFn_eq_dilation {q r : ℕ}
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (t : Fin q) (a : Position) (L : ℝ) (hL : 0 < L) (x : Position) :
    remoteOrbitalDensityFn h hh t a L hL (r := r) x =
      L⁻¹ ^ 3 * remoteOrbitalDensityFn h hh t 0 1 zero_lt_one (r := r)
        (L⁻¹ • (x - a)) := by
  unfold remoteOrbitalDensityFn remoteSpinOrbital
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [norm_escapeSpinOrbital]
  change ‖(L * Real.sqrt L)⁻¹ • h (L⁻¹ • (x - remoteOrbitalCenter a L i))‖ ^ 2 =
    L⁻¹ ^ 3 * ‖(1 * Real.sqrt 1)⁻¹ •
      h (1⁻¹ • (L⁻¹ • (x - a) - remoteOrbitalCenter 0 1 i))‖ ^ 2
  simp only [norm_smul, Real.norm_eq_abs]
  rw [show L⁻¹ • (x - remoteOrbitalCenter a L i) =
      L⁻¹ • (x - a) - remoteOrbitalCenter 0 1 i by
    simp only [remoteOrbitalCenter, zero_add]
    simp only [smul_sub, smul_add, smul_smul]
    rw [show L⁻¹ * (4 * L * (i : ℝ)) = 4 * (i : ℝ) by field_simp]
    module]
  rw [abs_of_pos (inv_pos.mpr (mul_pos hL (Real.sqrt_pos.mpr hL)))]
  simp only [Real.sqrt_one, mul_one, inv_one, abs_one, one_smul]
  have hs : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
  field_simp
  nlinarith only [hs]

theorem integral_rpow_remoteOrbitalDensityFn {q r : ℕ}
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (t : Fin q) (a : Position) (L : ℝ) (hL : 0 < L) :
    (∫ x, (remoteOrbitalDensityFn h hh t a L hL (r := r) x) ^ ((5 : ℝ) / 3)) =
      L⁻¹ ^ 2 * ∫ x,
        (remoteOrbitalDensityFn h hh t 0 1 zero_lt_one (r := r) x) ^ ((5 : ℝ) / 3) := by
  simp_rw [remoteOrbitalDensityFn_eq_dilation h hh t a L hL]
  have hb (x : Position) :
      0 ≤ remoteOrbitalDensityFn h hh t 0 1 zero_lt_one (r := r) x := by
    unfold remoteOrbitalDensityFn
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp_rw [Real.mul_rpow (by positivity : 0 ≤ L⁻¹ ^ 3) (hb _)]
  rw [integral_const_mul]
  let f : Position → ℝ := fun y =>
    (remoteOrbitalDensityFn h hh t 0 1 zero_lt_one (r := r) (L⁻¹ • y)) ^
      ((5 : ℝ) / 3)
  have htrans := MeasureTheory.integral_sub_right_eq_self
    (μ := (volume : Measure Position)) f a
  change (∫ x : Position, (remoteOrbitalDensityFn h hh t 0 1 zero_lt_one (r := r)
    (L⁻¹ • (x - a))) ^ ((5 : ℝ) / 3)) = _ at htrans
  rw [htrans]
  let g : Position → ℝ := fun y =>
    (remoteOrbitalDensityFn h hh t 0 1 zero_lt_one (r := r) y) ^ ((5 : ℝ) / 3)
  have hscale := Measure.integral_comp_inv_smul_of_nonneg
    (volume : Measure Position) g hL.le
  change (∫ x : Position, (remoteOrbitalDensityFn h hh t 0 1 zero_lt_one (r := r)
    (L⁻¹ • x)) ^ ((5 : ℝ) / 3)) = _ at hscale
  rw [hscale]
  simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul]
  have hp : (L⁻¹ ^ 3) ^ ((5 : ℝ) / 3) = L⁻¹ ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ L⁻¹)]
    norm_num
  rw [hp]
  field_simp
  simp only [g]

theorem norm_remoteOrbitalDensity {q r : ℕ}
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (t : Fin q) (a : Position) (L : ℝ) (hL : 0 < L) :
    ‖(remoteOrbitalDensity h hh t a L hL (r := r)).val‖ =
      L ^ (-(6 : ℝ) / 5) *
        ‖(remoteOrbitalDensity h hh t 0 1 zero_lt_one (r := r)).val‖ := by
  have hnonneg := norm_nonneg
    (remoteOrbitalDensity h hh t a L hL (r := r)).val
  have hnonneg₀ := mul_nonneg (Real.rpow_nonneg hL.le (-(6 : ℝ) / 5))
    (norm_nonneg (remoteOrbitalDensity h hh t 0 1 zero_lt_one (r := r)).val)
  rw [← Real.rpow_left_inj hnonneg hnonneg₀
    (by norm_num : (5 : ℝ) / 3 ≠ 0)]
  rw [← TFFunctional.integral_tfDensity_rpow_eq_norm]
  rw [integral_congr_ae]
  · rw [integral_rpow_remoteOrbitalDensityFn h hh t a L hL]
    have hbase : (∫ x,
        (remoteOrbitalDensityFn h hh t 0 1 zero_lt_one (r := r) x) ^
          ((5 : ℝ) / 3)) = ∫ x : Position,
            ((remoteOrbitalDensity h hh t 0 1 zero_lt_one (r := r)).val x) ^
              ((5 : ℝ) / 3) := by
      apply integral_congr_ae
      filter_upwards [remoteOrbitalDensity_coe_ae h hh t 0 1 zero_lt_one] with x hx
      rw [hx]
    rw [hbase, TFFunctional.integral_tfDensity_rpow_eq_norm]
    rw [Real.mul_rpow (Real.rpow_nonneg hL.le _)
      (norm_nonneg (remoteOrbitalDensity h hh t 0 1 zero_lt_one (r := r)).val)]
    rw [← Real.rpow_mul hL.le]
    norm_num
  · filter_upwards [remoteOrbitalDensity_coe_ae h hh t a L hL] with x hx
    rw [hx]

end LiebThirring.TFUpper

end
