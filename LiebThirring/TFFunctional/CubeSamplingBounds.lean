/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.CubeSampling

/-! # Joint L1 and Lp bounds for finite cube sampling

Uniform continuity gives a mesh error on one fixed finite-volume ball. The
explicit factor is its volume to the reciprocal exponent.
-/

public section

open MeasureTheory Set Metric Filter Topology
open scoped NNReal ENNReal

namespace LiebThirring.TFFunctional

theorem sampledCubeMesh_eLpNorm_sub_le (f : Position → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hcont : Continuous f) (A : ℝ) (hsupport : Function.support f ⊆ ball 0 A)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (hsmall : Real.sqrt 3 * ℓ.val ≤ 2)
    (ε δ : ℝ) (hε : 0 ≤ ε) (hdiam : Real.sqrt 3 * ℓ.val < δ)
    (hmod : ∀ x y : Position, dist x y < δ → dist (f x) (f y) < ε)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    eLpNorm ((sampledCubeMesh f hf ℓ
      (eligibleLatticeCubes ℓ.val (ball 0 (A + 3)) ℓ.property isBounded_ball)).stepFunction - f)
      p volume ≤ ENNReal.ofReal ε * volume (ball (0 : Position) (A + 3)) ^ (1 / p.toReal) := by
  let g := sampledCubeMesh f hf ℓ
    (eligibleLatticeCubes ℓ.val (ball 0 (A + 3)) ℓ.property isBounded_ball)
  apply eLpNorm_sub_le_of_dist_bdd volume hp measurableSet_ball.nullMeasurableSet hε
    (g.integrable_stepFunction.aestronglyMeasurable.sub hcont.aestronglyMeasurable)
    (sampledCubeMesh_error_le f hf A hsupport ℓ hsmall ε δ hε hdiam hmod)
    (sampledCubeMesh_support_subset f hf A ℓ)
  exact hsupport.trans (ball_subset_ball (by linarith : A ≤ A + 3))

private theorem exists_sampling_side (δ : ℝ) (hδ : 0 < δ) :
    ∃ ℓ : {ℓ : ℝ // 0 < ℓ}, Real.sqrt 3 * ℓ.val ≤ 2 ∧ Real.sqrt 3 * ℓ.val < δ := by
  let ℓ : ℝ := min 1 δ / (2 * (Real.sqrt 3 + 1))
  have hden : 0 < 2 * (Real.sqrt 3 + 1) := by positivity
  have hℓ : 0 < ℓ := div_pos (lt_min zero_lt_one hδ) hden
  have hcancel : 2 * (Real.sqrt 3 + 1) * ℓ = min 1 δ := by
    dsimp [ℓ]
    field_simp
  refine ⟨⟨ℓ, hℓ⟩, ?_, ?_⟩
  · have hmin := min_le_left (1 : ℝ) δ
    nlinarith only [hcancel, hmin, hℓ]
  · have hmin := min_le_right (1 : ℝ) δ
    nlinarith only [hcancel, hmin, hℓ, hδ]

/-- Compact continuous nonnegative functions admit finite regular mesh approximants
in both exponents, with the same mesh and explicit finite-volume error factor. -/
theorem exists_cubeMesh_eLpNorm_approximation (f : Position → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hcont : Continuous f) (hcompact : HasCompactSupport f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (B : ℕ) (g : TFUpper.CubeMesh B),
      eLpNorm (g.stepFunction - f) ((5 : ℝ≥0∞) / 3) volume ≤ ENNReal.ofReal ε ∧
      eLpNorm (g.stepFunction - f) 1 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨A, hsupport⟩ := hcompact.isCompact.isBounded.subset_ball (0 : Position)
  have hs : Function.support f ⊆ ball 0 A := (subset_tsupport f).trans hsupport
  let V : ℝ := volume.real (ball (0 : Position) (A + 3))
  have hV : 0 ≤ V := measureReal_nonneg
  let C : ℝ := V ^ ((3 : ℝ) / 5) + V + 1
  have hC : 0 < C := by
    have hp := Real.rpow_nonneg hV ((3 : ℝ) / 5)
    dsimp [C]
    linarith only [hp, hV]
  let η : ℝ := ε / C
  have hη : 0 < η := div_pos hε hC
  have huc := hcont.uniformContinuous_of_tendsto_cocompact hcompact.is_zero_at_infty
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp huc η hη
  obtain ⟨ℓ, hsmall, hdiam⟩ := exists_sampling_side δ hδ
  let s := eligibleLatticeCubes ℓ.val (ball 0 (A + 3)) ℓ.property isBounded_ball
  let g := sampledCubeMesh f hf ℓ s
  have hv : volume (ball (0 : Position) (A + 3)) = ENNReal.ofReal V := by
    dsimp [V, measureReal_def]
    exact (ENNReal.ofReal_toReal (by rw [volume_ball_position]; finiteness)).symm
  have hbudget : η * C = ε := div_mul_cancel₀ ε hC.ne'
  refine ⟨s.card, g, ?_, ?_⟩
  · have h := sampledCubeMesh_eLpNorm_sub_le f hf hcont A hs ℓ hsmall η δ hη.le
      hdiam hmod ((5 : ℝ≥0∞) / 3) (ENNReal.div_ne_top (by norm_num) (by norm_num))
    have hp : ((5 : ℝ≥0∞) / 3).toReal = (5 : ℝ) / 3 := by
      norm_num [ENNReal.toReal_div]
    rw [hv, hp, show (1 : ℝ) / (5 / 3) = 3 / 5 by norm_num] at h
    rw [ENNReal.ofReal_rpow_of_nonneg hV (by norm_num), ← ENNReal.ofReal_mul hη.le] at h
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hp := Real.rpow_nonneg hV ((3 : ℝ) / 5)
    dsimp [C] at hbudget
    nlinarith only [hbudget, hV, hη, hp]
  · have h := sampledCubeMesh_eLpNorm_sub_le f hf hcont A hs ℓ hsmall η δ hη.le
      hdiam hmod 1 ENNReal.one_ne_top
    rw [hv, ENNReal.toReal_one, div_one, ENNReal.rpow_one,
      ← ENNReal.ofReal_mul hη.le] at h
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hp := Real.rpow_nonneg hV ((3 : ℝ) / 5)
    dsimp [C] at hbudget
    nlinarith only [hbudget, hV, hη, hp]

end LiebThirring.TFFunctional

end
