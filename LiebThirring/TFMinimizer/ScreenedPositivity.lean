/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.CappedNuclearPotential
public import LiebThirring.TFMinimizer.MeanValueMaximum
public import LiebThirring.TFMinimizer.ShellAverages
public import LiebThirring.TFMinimizer.Equation

/-! # Nonnegative screened potential off the nuclei

Lieb–Simon (1977) II.17, pp. 48--49. A capped nuclear potential makes
the positive part of electronic minus nuclear potential globally continuous.
It is harmonic wherever positive, because the TF equation removes the density
there. The proved shell mean-value maximum principle forces it to vanish.
-/

public section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace LiebThirring.TFMinimizer

open TFFunctional

local instance : Fact (1 ≤ (5 : ℝ≥0∞) / 3) := ⟨by
  apply (ENNReal.toReal_le_toReal (by simp)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num [ENNReal.toReal_div]⟩

/-- An internal consequence of the proved TF equation; no potential value at a pole is claimed. -/
theorem tfDensity_potential_le_nuclear_of_equation {M : ℕ}
    (a : {a : ℝ // 0 < a}) (z : Fin M → ℝ≥0) (hz : ∀ k, 0 < z k)
    (R : Fin M → Position) (ρ : TFDensity) (μ : ℝ≥0)
    (heq : ∀ᵐ x ∂(volume : Measure Position),
      (5 / 3 : ℝ) * a.val * (ρ.val x) ^ ((2 : ℝ) / 3) =
        max (tfNuclearPotential z R x -
          (coulombPotential (tfDensityMeasure ρ) x).toReal - (μ : ℝ)) 0)
    (x : Position) (hx : ∀ k, x ≠ R k) :
    (coulombPotential (tfDensityMeasure ρ) x).toReal ≤ tfNuclearPotential z R x := by
  let P : Position → ℝ := fun y => (coulombPotential (tfDensityMeasure ρ) y).toReal
  let B : ℝ := (8 * Real.pi * Real.sqrt 1) ^ ((2 : ℝ) / 5) * ‖ρ.val‖ + tfMass ρ / 1
  have hB : 0 ≤ B := add_nonneg
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _))
    (div_nonneg (tfMass_nonneg ρ) zero_lt_one.le)
  have hPB : ∀ y : Position, P y ≤ B := by
    intro y
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (coulombPotential_tfDensityMeasure_le_norm ρ y 1 zero_lt_one)
    change P y ≤ (ENNReal.ofReal B).toReal at h
    rwa [ENNReal.toReal_ofReal hB] at h
  obtain ⟨δ, hδ, hcap⟩ := exists_positive_nuclear_cap z hz B hB
  let V : Position → ℝ := tfCappedNuclearPotential z R δ
  let u : Position → ℝ := fun y => max (P y - V y) 0
  have hc : Continuous u := ((continuous_tfDensity_potential ρ).sub
    (continuous_tfCappedNuclearPotential z R δ hδ)).max continuous_const
  have ht : Tendsto u (Bornology.cobounded Position) (𝓝 0) := by
    have h0 : Tendsto (fun _ : Position => (0 : ℝ)) (Bornology.cobounded Position) (𝓝 0) :=
      tendsto_const_nhds
    change Tendsto (fun y : Position => max
      ((coulombPotential (tfDensityMeasure ρ) y).toReal - tfCappedNuclearPotential z R δ y) 0)
      (Bornology.cobounded Position) (𝓝 0)
    simpa only [sub_self, max_self] using
      ((tendsto_tfDensity_potential_zero ρ).sub
        (tendsto_tfCappedNuclearPotential_zero z R δ)).max h0
  have hdist : ∀ y : Position, 0 < u y → ∀ k, δ < ‖y - R k‖ := by
    intro y hy k
    have hw : 0 < P y - V y := (lt_max_iff.mp hy).resolve_right (lt_irrefl 0)
    by_contra hn
    have hnorm : ‖y - R k‖ ≤ δ := le_of_not_gt hn
    have hs : (z k : ℝ) / δ ≤ V y := by
      have h := Finset.single_le_sum
        (fun i (_ : i ∈ Finset.univ) => div_nonneg (z i).property
          (hδ.le.trans (le_max_left δ ‖y - R i‖))) (Finset.mem_univ k)
      rw [max_eq_left hnorm] at h
      exact h
    linarith only [hw, hPB y, hs, hcap k]
  have htrue : ∀ y : Position, 0 < u y →
      u y = P y - tfNuclearPotential z R y := by
    intro y hy
    have hw : 0 < P y - V y := (lt_max_iff.mp hy).resolve_right (lt_irrefl 0)
    change max (P y - V y) 0 = _
    rw [max_eq_left hw.le]
    dsimp only [V]
    rw [tfCappedNuclearPotential_eq_of_le z R δ y (fun k => (hdist y hy k).le)]
  have hmean : ∀ y : Position, 0 < u y → ∃ ε : ℝ, 0 < ε ∧
      ∀ r : ℝ, 0 < r → r < ε → u y ≤ ∫ w : Position, u w ∂shell y r := by
    intro y hy
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const hc) y hy
    refine ⟨ε, hε, ?_⟩
    intro r hr hrε
    have hR : ∀ k, r ≤ ‖R k - y‖ := by
      intro k
      have hn : R k ∉ ball y ε := by
        intro hk
        have h := hdist (R k) (hb hk) k
        rw [sub_self, norm_zero] at h
        linarith only [h, hδ]
      have hd : ε ≤ ‖R k - y‖ := by
        simpa only [mem_ball, dist_eq_norm, not_lt] using hn
      exact hrε.le.trans hd
    have hzero : tfDensityMeasure ρ (ball y r) = 0 := by
      change (volume.withDensity (fun w : Position => ENNReal.ofReal (ρ.val w))) (ball y r) = 0
      rw [withDensity_apply _ measurableSet_ball]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [ae_restrict_mem measurableSet_ball,
        ae_restrict_of_ae heq, ae_restrict_of_ae (tfDensity_ae_nonneg ρ)] with w hw he hρ
      have hwu : 0 < u w := hb (ball_subset_ball hrε.le hw)
      have hp : tfNuclearPotential z R w - P w < 0 := by
        have h := htrue w hwu
        linarith only [h, hwu]
      have hμnonneg : 0 ≤ (μ : ℝ) := μ.property
      have hm : tfNuclearPotential z R w - P w - (μ : ℝ) ≤ 0 := by
        linarith only [hp, hμnonneg]
      rw [max_eq_right hm] at he
      have hρzero : ρ.val w = 0 := by
        by_contra hn
        have hρpos : 0 < ρ.val w := lt_of_le_of_ne hρ (Ne.symm hn)
        have hk : 0 < (5 / 3 : ℝ) * a.val * (ρ.val w) ^ ((2 : ℝ) / 3) :=
          mul_pos (mul_pos (by norm_num) a.property) (Real.rpow_pos_of_pos hρpos _)
        linarith only [he, hk]
      rw [hρzero, ENNReal.ofReal_zero]
      rfl
    have havg := integral_screenedPotential_shell_eq z R ρ y r hr hR hzero
    have he : (∫ w : Position, u w ∂shell y r) =
        -(∫ w : Position, (tfNuclearPotential z R w - P w) ∂shell y r) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [ae_shell_norm y hr.le] with w hw
      have hwu : 0 < u w := hb (by
        rw [mem_ball, dist_eq_norm, hw]
        exact hrε)
      rw [htrue w hwu]
      ring
    rw [he, havg, htrue y hy]
    linarith
  have hu := nonpos_of_local_shell_submean hc ht hmean x
  have hPV : P x ≤ V x := by
    have h := (le_max_left (P x - V x) 0).trans hu
    linarith only [h]
  exact hPV.trans (tfCappedNuclearPotential_le_of_ne z R δ x hx)

end LiebThirring.TFMinimizer

end
