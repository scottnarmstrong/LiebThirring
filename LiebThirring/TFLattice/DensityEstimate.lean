/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.DensityVariance
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# The filled-cube density error

For arbitrary partial last-shell fillings, the squared centered density
integral is at most `1944 q ℓ⁻³ n^(5/3)`. Its square root has the filled-density convergence
`n^(5/6)` scale. Source: Lieb–Simon (1977) III.14, pp. 69–71.
-/

@[expose] public section

open MeasureTheory

namespace LiebThirring.TFLattice

theorem integrable_filledDensity_sub_sq {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (s : Finset (ModeIndex q)) :
    Integrable (fun x => (filledDensity ℓ s x - s.card / ℓ.val ^ 3) ^ 2)
      (cubeCoordinateMeasure ℓ) := by
  have heq (x : Fin 3 → ℝ) : (filledDensity ℓ s x - s.card / ℓ.val ^ 3) ^ 2 =
      filledDensity ℓ s x ^ 2 - (2 * (s.card / ℓ.val ^ 3)) * filledDensity ℓ s x +
        (s.card / ℓ.val ^ 3) ^ 2 := by ring
  simp_rw [heq]
  exact ((integrable_filledDensity_sq ℓ s).sub
    ((integrable_filledDensity ℓ s).const_mul _)).add (integrable_const _)

theorem memLp_filledDensity_sub_two {q : ℕ} (ℓ : {ℓ : ℝ // 0 < ℓ})
    (s : Finset (ModeIndex q)) :
    MemLp (fun x => filledDensity ℓ s x - s.card / ℓ.val ^ 3) 2 (cubeCoordinateMeasure ℓ) := by
  have hc : Continuous (fun x => filledDensity ℓ s x - s.card / ℓ.val ^ 3) := by
    unfold filledDensity spatialModeDensity dirichletFactorDensity
    fun_prop
  exact (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
    (integrable_filledDensity_sub_sq ℓ s)

/-- The variance estimate uses only the explicit Dirichlet formulas and
lowest-mode occupation; no spectral-completeness assumption is needed. -/
theorem integral_filledDensity_sub_sq_le {q : ℕ} (hq : 0 < q)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) {s : Finset (ModeIndex q)}
    (hs : IsFilled IsDirichletIndex s) :
    (∫ x, (filledDensity ℓ s x - s.card / ℓ.val ^ 3) ^ 2 ∂cubeCoordinateMeasure ℓ) ≤
      1944 * q * (s.card : ℝ) ^ (5 / 3 : ℝ) / ℓ.val ^ 3 := by
  have hℓ : 0 < ℓ.val := ℓ.property
  by_cases hn : s.card = 0
  · have he : s = ∅ := Finset.card_eq_zero.mp hn
    simp [he, filledDensity]
  have hn' : 1 ≤ s.card := Nat.one_le_iff_ne_zero.mpr hn
  have hbox := dirichlet_occupation_subset_comparison_box hq hs
  have hv := integral_filledDensity_sub_sq_le_box ℓ hs.1 hbox
  have hside := comparison_box_side_le hn'
  have hroot : 0 ≤ (s.card : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hside2 :
      ((2 * (1 + (⌈(s.card : ℝ) ^ (1 / 3 : ℝ)⌉₊ + 1)) + 1 : ℕ) : ℝ) ^ 2 ≤
        (9 * (s.card : ℝ) ^ (1 / 3 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hside 2
  have hroot2 : ((s.card : ℝ) ^ (1 / 3 : ℝ)) ^ 2 = (s.card : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg s.card)]
    norm_num
  have hprod : (s.card : ℝ) * (s.card : ℝ) ^ (2 / 3 : ℝ) =
      (s.card : ℝ) ^ (5 / 3 : ℝ) := by
    calc
      _ = (s.card : ℝ) ^ (1 : ℝ) * (s.card : ℝ) ^ (2 / 3 : ℝ) := by rw [Real.rpow_one]
      _ = (s.card : ℝ) ^ ((1 : ℝ) + 2 / 3) :=
        (Real.rpow_add (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) _ _).symm
      _ = _ := by congr 1; norm_num
  calc
    _ ≤ 24 * q * s.card *
        (2 * (1 + (⌈(s.card : ℝ) ^ (1 / 3 : ℝ)⌉₊ + 1)) + 1 : ℕ) ^ 2 / ℓ.val ^ 3 := hv
    _ ≤ 24 * q * s.card * (9 * (s.card : ℝ) ^ (1 / 3 : ℝ)) ^ 2 / ℓ.val ^ 3 := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hℓ.le _)
      exact mul_le_mul_of_nonneg_left hside2 (by positivity)
    _ = 1944 * q * ((s.card : ℝ) * ((s.card : ℝ) ^ (1 / 3 : ℝ)) ^ 2) / ℓ.val ^ 3 := by ring
    _ = _ := by rw [hroot2, hprod]

/-- The square-root version of the quantitative L² error. -/
theorem sqrt_integral_filledDensity_sub_sq_le {q : ℕ} (hq : 0 < q)
    (ℓ : {ℓ : ℝ // 0 < ℓ}) {s : Finset (ModeIndex q)}
    (hs : IsFilled IsDirichletIndex s) :
    Real.sqrt (∫ x, (filledDensity ℓ s x - s.card / ℓ.val ^ 3) ^ 2 ∂cubeCoordinateMeasure ℓ) ≤
      Real.sqrt (1944 * q / ℓ.val ^ 3) * (s.card : ℝ) ^ (5 / 6 : ℝ) := by
  have hℓ : 0 < ℓ.val := ℓ.property
  calc
    _ ≤ Real.sqrt (1944 * q * (s.card : ℝ) ^ (5 / 3 : ℝ) / ℓ.val ^ 3) :=
      Real.sqrt_le_sqrt (integral_filledDensity_sub_sq_le hq ℓ hs)
    _ = Real.sqrt ((1944 * q / ℓ.val ^ 3) * (s.card : ℝ) ^ (5 / 3 : ℝ)) := by congr 1; ring
    _ = Real.sqrt (1944 * q / ℓ.val ^ 3) * Real.sqrt ((s.card : ℝ) ^ (5 / 3 : ℝ)) :=
      Real.sqrt_mul (by positivity) _
    _ = _ := by
      simp_rw [Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul (Nat.cast_nonneg s.card)]
      norm_num

end LiebThirring.TFLattice

end
