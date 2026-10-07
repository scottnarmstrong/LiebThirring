/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFMinimizer.SphereMoments

/-! # A local spherical mean-value maximum principle

A continuous function decaying to zero cannot have a positive
value if it satisfies the local submean inequality at every positive point.
The proof perturbs a compact maximum by a positive quadratic; no differentiability
or strong maximum principle is assumed.
-/

public section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace LiebThirring.TFMinimizer

theorem integrable_shell_of_continuous {f : Position → ℝ} (hf : Continuous f)
    (a : Position) (r : ℝ) : Integrable f (shell a r) := by
  rw [shell]
  apply (integrable_map_measure hf.aestronglyMeasurable
    (measurable_shellMap a r).aemeasurable).mpr
  have hc : Continuous (fun ω : sphere (0 : Position) 1 => f (a + r • (ω : Position))) :=
    hf.comp (continuous_const.add (continuous_subtype_val.const_smul r))
  exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

/-- Only a local submean inequality on the positive region is needed. -/
theorem nonpos_of_local_shell_submean {u : Position → ℝ} (hu : Continuous u)
    (hdecay : Tendsto u (Bornology.cobounded Position) (𝓝 0))
    (hmean : ∀ x : Position, 0 < u x → ∃ ε : ℝ, 0 < ε ∧
      ∀ r : ℝ, 0 < r → r < ε → u x ≤ ∫ y : Position, u y ∂shell x r) :
    ∀ x : Position, u x ≤ 0 := by
  intro x₀
  by_contra hbad
  have hpos : 0 < u x₀ := lt_of_not_ge hbad
  have he := hdecay.eventually_lt_const (by linarith : (0 : ℝ) < u x₀ / 4)
  obtain ⟨R₀, _, houter⟩ := (hasBasis_cobounded_compl_closedBall (0 : Position)).eventually_iff.mp he
  let R : ℝ := max (max R₀ ‖x₀‖) 1 + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right (max R₀ ‖x₀‖) (1 : ℝ)]
  have hR₀ : R₀ < R := by
    dsimp [R]
    linarith [le_max_left R₀ ‖x₀‖, le_max_left (max R₀ ‖x₀‖) (1 : ℝ)]
  have hx₀ : ‖x₀‖ < R := by
    dsimp [R]
    linarith [le_max_right R₀ ‖x₀‖, le_max_left (max R₀ ‖x₀‖) (1 : ℝ)]
  let τ : ℝ := u x₀ / (4 * R ^ 2)
  have hτ : 0 < τ := div_pos hpos (mul_pos (by norm_num) (sq_pos_of_pos hR))
  have hτR : τ * R ^ 2 = u x₀ / 4 := by
    dsimp [τ]
    field_simp
  let f : Position → ℝ := fun y => u y + τ * ‖y‖ ^ 2
  have hf : Continuous f := hu.add (continuous_const.mul (continuous_norm.pow 2))
  obtain ⟨a, ha, hmax⟩ := (isCompact_closedBall (0 : Position) R).exists_isMaxOn
    ⟨x₀, by simpa only [mem_closedBall, dist_zero_right] using hx₀.le⟩ hf.continuousOn
  have han : ‖a‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using ha
  have hτa : τ * ‖a‖ ^ 2 ≤ u x₀ / 4 := by
    rw [← hτR]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) han 2) hτ.le
  have hfa : u x₀ ≤ f a := by
    have h := hmax (by simpa only [mem_closedBall, dist_zero_right] using hx₀.le)
    have hn : 0 ≤ τ * ‖x₀‖ ^ 2 := mul_nonneg hτ.le (sq_nonneg _)
    dsimp [f] at h ⊢
    linarith only [h, hn]
  have hua : 0 < u a := by dsimp [f] at hfa; linarith only [hfa, hτa, hpos]
  have hai : ‖a‖ < R := by
    by_contra hnot
    have heq : ‖a‖ = R := le_antisymm han (le_of_not_gt hnot)
    have ho : u a < u x₀ / 4 := houter (by
      simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le, heq] using hR₀)
    dsimp [f] at hfa
    rw [heq, hτR] at hfa
    linarith only [ho, hfa, hpos]
  obtain ⟨ε, hε, havg⟩ := hmean a hua
  let r : ℝ := min ε (R - ‖a‖) / 2
  have hr : 0 < r := half_pos (lt_min hε (sub_pos.mpr hai))
  have hrε : r < ε := by
    have h := min_le_left ε (R - ‖a‖)
    dsimp [r]
    linarith
  have hrR : ‖a‖ + r ≤ R := by
    have h := min_le_right ε (R - ‖a‖)
    dsimp [r]
    linarith
  have hle : (∫ y : Position, f y ∂shell a r) ≤ f a := by
    have hm : ∀ᵐ y ∂shell a r, f y ≤ f a := by
      filter_upwards [ae_shell_norm a hr.le] with y hy
      apply hmax
      rw [mem_closedBall, dist_zero_right]
      have ht : ‖y‖ ≤ ‖y - a‖ + ‖a‖ := by
        simpa only [sub_add_cancel] using norm_add_le (y - a) a
      linarith only [ht, hy, hrR]
    simpa only [integral_const, probReal_univ, one_smul] using
      integral_mono_ae (integrable_shell_of_continuous hf a r) (integrable_const (f a)) hm
  have hint : (∫ y : Position, f y ∂shell a r) =
      (∫ y : Position, u y ∂shell a r) + τ * (‖a‖ ^ 2 + r ^ 2) := by
    have hq : Integrable (fun y : Position => τ * ‖y‖ ^ 2) (shell a r) :=
      (integrable_shell_of_continuous (show Continuous (fun y : Position => ‖y‖ ^ 2) from
        continuous_norm.pow 2) a r).const_mul τ
    dsimp only [f]
    rw [integral_add (integrable_shell_of_continuous hu a r) hq,
      integral_const_mul, integral_norm_sq_shell a r hr.le]
  rw [hint] at hle
  have haavg := havg r hr hrε
  have hgain : 0 < τ * r ^ 2 := mul_pos hτ (sq_pos_of_pos hr)
  dsimp [f] at hle
  nlinarith only [hle, haavg, hgain]

end LiebThirring.TFMinimizer

end
