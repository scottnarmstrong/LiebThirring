/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.ScreenedPositivity
import all LiebThirring.Electrostatics.Basic
import all LiebThirring.Electrostatics.FaceMeasurePotential

/-! # The sharp upper mass bound for a TF minimizer

Lieb–Simon (1977) II.17, pp. 48--49. Newton averaging bounds the mass
inside every sufficiently large ball. Continuity from below gives the whole
mass, without a first moment assumption or an asymptotic interchange.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LiebThirring.TFMinimizer

open TFFunctional

theorem mass_ball_le_radius_mul_cappedPotential (η : Measure Position) [IsFiniteMeasure η]
    (r : ℝ) (hr : 0 < r) :
    η.real (ball (0 : Position) r) ≤ r * (cappedCoulombPotential η r 0).toReal := by
  have hin : (ENNReal.ofReal r)⁻¹ * η (ball (0 : Position) r) ≤
      cappedCoulombPotential η r 0 := by
    calc
      _ = ∫⁻ y in ball (0 : Position) r, cappedCoulombKernel r 0 y ∂η := by
        have hp : ∀ᵐ y ∂η.restrict (ball (0 : Position) r),
            cappedCoulombKernel r 0 y = (ENNReal.ofReal r)⁻¹ := by
          filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
          have hn : ‖y‖ < r := by simpa only [mem_ball, dist_zero_right] using hy
          simp only [cappedCoulombKernel, zero_sub, norm_neg, max_eq_left hn.le]
        rw [lintegral_congr_ae hp, lintegral_const, Measure.restrict_apply_univ]
      _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl
  have hreal := ENNReal.toReal_mono (cappedCoulombPotential_lt_top η r hr 0).ne hin
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hr.le] at hreal
  change r⁻¹ * η.real (ball (0 : Position) r) ≤ _ at hreal
  calc
    _ = r * (r⁻¹ * η.real (ball (0 : Position) r)) := by rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hreal hr.le

/-- Internal comparison lemma, whose potential comparison is supplied by the TF equation. -/
theorem tfMass_le_totalNuclearCharge_of_potential_le {M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ρ : TFDensity)
    (hpot : ∀ x : Position, (∀ k, x ≠ R k) →
      (coulombPotential (tfDensityMeasure ρ) x).toReal ≤ tfNuclearPotential z R x) :
    tfMass ρ ≤ totalNuclearCharge z := by
  have hball : ∀ r : ℝ, 0 < r → (∀ k, ‖R k‖ < r) →
      tfDensityMeasure ρ (ball (0 : Position) r) ≤ ENNReal.ofReal (totalNuclearCharge z) := by
    intro r hr hR
    have havg : (cappedCoulombPotential (tfDensityMeasure ρ) r 0).toReal ≤
        totalNuclearCharge z / r := by
      have hle : ∀ᵐ x ∂shell (0 : Position) r,
          (coulombPotential (tfDensityMeasure ρ) x).toReal ≤ tfNuclearPotential z R x := by
        filter_upwards [ae_shell_norm (0 : Position) hr.le] with x hx
        apply hpot
        intro k hxe
        rw [hxe, sub_zero] at hx
        linarith only [hx, hR k]
      have h := integral_mono_ae (integrable_tfDensity_potential_shell ρ 0 r)
        (integrable_tfNuclearPotential_shell z R 0 r hr) hle
      rw [integral_tfDensity_potential_shell ρ 0 r hr, integral_tfNuclearPotential_shell z R 0 r hr] at h
      have he : (∑ k, (z k : ℝ) / max ‖R k - 0‖ r) = totalNuclearCharge z / r := by
        simp_rw [sub_zero, max_eq_right (hR _).le]
        exact (Finset.sum_div ..).symm
      rwa [he] at h
    have hm := mass_ball_le_radius_mul_cappedPotential (tfDensityMeasure ρ) r hr
    have hb : (tfDensityMeasure ρ).real (ball (0 : Position) r) ≤ totalNuclearCharge z := by
      calc
        _ ≤ r * (cappedCoulombPotential (tfDensityMeasure ρ) r 0).toReal := hm
        _ ≤ r * (totalNuclearCharge z / r) := mul_le_mul_of_nonneg_left havg hr.le
        _ = _ := mul_div_cancel₀ _ hr.ne'
    have h := ENNReal.ofReal_le_ofReal hb
    change ENNReal.ofReal ((tfDensityMeasure ρ) (ball (0 : Position) r)).toReal ≤
      ENNReal.ofReal (totalNuclearCharge z) at h
    rwa [ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  have hnat : ∀ n : ℕ, tfDensityMeasure ρ (ball (0 : Position) n) ≤
      ENNReal.ofReal (totalNuclearCharge z) := by
    intro n
    let r : ℝ := (∑ k : Fin M, ‖R k‖) + (n : ℝ) + 1
    have hs : 0 ≤ ∑ k : Fin M, ‖R k‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hr : 0 < r := by dsimp [r]; positivity
    have hR : ∀ k, ‖R k‖ < r := by
      intro k
      have hk := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => norm_nonneg (R i))
        (Finset.mem_univ k)
      dsimp [r]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    apply (measure_mono (ball_subset_ball (show (n : ℝ) ≤ r by dsimp [r]; linarith))).trans
    exact hball r hr hR
  have hmono : Monotone (fun n : ℕ => ball (0 : Position) (n : ℝ)) :=
    fun _ _ h => ball_subset_ball (by exact_mod_cast h)
  have huniv : tfDensityMeasure ρ univ ≤ ENNReal.ofReal (totalNuclearCharge z) := by
    rw [← iUnion_ball_nat (0 : Position), hmono.measure_iUnion]
    exact iSup_le hnat
  rw [tfDensityMeasure_univ] at huniv
  exact (ENNReal.ofReal_le_ofReal_iff (totalNuclearCharge_nonneg z)).mp huniv

/-- A relaxed minimizer never has more electrons than the total nuclear charge. -/
theorem tfMass_le_totalNuclearCharge_of_relaxed_minimizer {M : ℕ}
    (a : {a : ℝ // 0 < a}) (ν : ℝ≥0) (z : Fin M → ℝ≥0) (hz : ∀ k, 0 < z k)
    (R : Fin M → Position) (hR : Function.Injective R)
    (ρ : TFDensity) (hmass : tfMass ρ ≤ (ν : ℝ))
    (hmin : (tfFunctional a z R ρ : EReal) = tfRelaxedEnergy a ν z R) :
    tfMass ρ ≤ totalNuclearCharge z := by
  by_cases hν : 0 < ν
  · obtain ⟨μ, heq, _⟩ := tfEquation_of_relaxed_minimizer a ν hν z hz R hR ρ hmass hmin
    exact tfMass_le_totalNuclearCharge_of_potential_le z R ρ
      (tfDensity_potential_le_nuclear_of_equation a z hz R ρ μ heq)
  · have hzero : ν = 0 := le_antisymm (le_of_not_gt hν) bot_le
    rw [hzero, NNReal.coe_zero] at hmass
    exact hmass.trans (totalNuclearCharge_nonneg z)

end LiebThirring.TFMinimizer

end
