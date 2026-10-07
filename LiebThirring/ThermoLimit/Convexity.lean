/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic

/-!
# Midpoint convexity on nonnegative densities

Abstract analytic consequences of the midpoint packing estimate in limit convexity of the
thermodynamic-limit argument.
-/

public section

namespace LiebThirring.ThermoLimit

theorem midpoint_convex_dyadic_right
    {f : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ x → ∀ y, 0 ≤ y → f ((x + y) / 2) ≤ (f x + f y) / 2)
    {x h : ℝ}
    (hx : 0 ≤ x) (n : ℕ) (hend : 0 ≤ x + (2 : ℝ) ^ n * h) :
    f (x + h) ≤ (1 - ((2 : ℝ) ^ n)⁻¹) * f x + ((2 : ℝ) ^ n)⁻¹ *
      f (x + (2 : ℝ) ^ n * h) := by
  induction n generalizing h with
  | zero => simp
  | succ n ihn =>
      have hmid : x + h = ((x : ℝ) + (x + 2 * h)) / 2 := by ring
      have htwo : x + (2 : ℝ) ^ n * (2 * h) = x + (2 : ℝ) ^ (n + 1) * h := by
        rw [pow_succ]
        ring
      have hnear : 0 ≤ x + 2 * h := by
        rw [← htwo] at hend
        by_contra hneg
        have hn : x + (2 : ℝ) ^ n * (2 * h) < 0 := by
          have hp : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
          nlinarith [hx]
        linarith
      calc
        f (x + h) = f ((x + (x + 2 * h)) / 2) := by rw [hmid]
        _ ≤ (f x + f (x + 2 * h)) / 2 := hf x hx (x + 2 * h) hnear
        _ ≤ (f x + ((1 - ((2 : ℝ) ^ n)⁻¹) * f x + ((2 : ℝ) ^ n)⁻¹ *
              f (x + (2 : ℝ) ^ n * (2 * h)))) / 2 := by
          gcongr
          exact ihn (h := 2 * h) (by simpa [htwo] using hend)
        _ = (1 - ((2 : ℝ) ^ (n + 1))⁻¹) * f x + ((2 : ℝ) ^ (n + 1))⁻¹ *
              f (x + (2 : ℝ) ^ (n + 1) * h) := by
          rw [htwo, pow_succ]
          field_simp
          ring

/-- A midpoint-convex function which is locally bounded above is continuous at every
positive density. This is the Bernstein--Doetsch step used in limit convexity. -/
theorem continuousAt_of_midpointConvexOnNonneg_of_locally_boundedAbove
    {f : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ x → ∀ y, 0 ≤ y → f ((x + y) / 2) ≤ (f x + f y) / 2)
    (hub : ∀ x, 0 < x → ∃ r > 0, r ≤ x ∧ ∃ U,
      ∀ y ∈ Set.Icc (x - r) (x + r), f y ≤ U)
    {x : ℝ} (hx : 0 < x) : ContinuousAt f x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨r, hr, hrx, U, hU⟩ := hub x hx
  let C := max (U - f x) 0
  obtain ⟨n : ℕ, hn : C / (2 : ℝ) ^ n < ε / 2⟩ :=
    (tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℝ)))).eventually
      (gt_mem_nhds (half_pos hε)) |>.exists
  refine ⟨min (r / (2 : ℝ) ^ n) (x / 2), lt_min (div_pos hr (pow_pos (by norm_num) n))
      (half_pos hx), ?_⟩
  intro y hy
  have hxy : |y - x| < min (r / (2 : ℝ) ^ n) (x / 2) := by simpa [Real.dist_eq] using hy
  have hy0 : 0 ≤ y := by
    have : |y - x| < x / 2 := lt_of_lt_of_le hxy (min_le_right _ _)
    rw [abs_lt] at this
    linarith
  have hp : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hend (z : ℝ) (hz : |z - x| < r / (2 : ℝ) ^ n) :
      x + (2 : ℝ) ^ n * (z - x) ∈ Set.Icc (x - r) (x + r) := by
    rw [abs_lt] at hz
    have hzhi := hz.2
    have hlo : -r < (2 : ℝ)^n * (z-x) := by
      have hq : -r / (2 : ℝ)^n < z-x := by simpa [neg_div] using hz.1
      simpa [mul_comm] using (div_lt_iff₀ hp).mp hq
    have hhi : (2 : ℝ)^n * (z-x) < r := by
      simpa [mul_comm] using (lt_div_iff₀ hp).mp hzhi
    constructor <;> linarith
  have hupp : f y - f x < ε / 2 := by
    have hd := midpoint_convex_dyadic_right hf (x := x) (h := y - x) (le_of_lt hx) n
      (show 0 ≤ x + (2 : ℝ) ^ n * (y - x) by
        exact (hend y (lt_of_lt_of_le hxy (min_le_left _ _))).1.trans' (by linarith))
    have hb := hU _ (hend y (lt_of_lt_of_le hxy (min_le_left _ _)))
    have hC : U - f x ≤ C := le_max_left _ _
    rw [show x + (y - x) = y by ring] at hd
    calc
      f y - f x ≤ (U - f x) / (2 : ℝ) ^ n := by
        apply (sub_le_iff_le_add).2
        calc
          f y ≤ (1 - ((2 : ℝ) ^ n)⁻¹) * f x + ((2 : ℝ) ^ n)⁻¹ *
              f (x + (2 : ℝ) ^ n * (y - x)) := hd
          _ ≤ (1 - ((2 : ℝ) ^ n)⁻¹) * f x + ((2 : ℝ) ^ n)⁻¹ * U := by gcongr
          _ = (U - f x) / (2 : ℝ) ^ n + f x := by field_simp; ring
      _ ≤ C / (2 : ℝ) ^ n := div_le_div_of_nonneg_right hC (le_of_lt hp)
      _ < ε / 2 := hn
  have hupp' : f (2 * x - y) - f x < ε / 2 := by
    have hdxy : |(2 * x - y) - x| = |y - x| := by rw [show (2*x-y)-x = -(y-x) by ring, abs_neg]
    have hzdist : |(2 * x - y) - x| < min (r / (2 : ℝ) ^ n) (x / 2) := hdxy.trans_lt hxy
    -- Repeat the preceding upper estimate at the reflected point.
    have hz0 : 0 ≤ 2 * x - y := by
      have := lt_of_lt_of_le hzdist (min_le_right _ _)
      rw [abs_lt] at this
      linarith
    have hd := midpoint_convex_dyadic_right hf (x := x) (h := (2*x-y)-x) (le_of_lt hx) n
      (show 0 ≤ x + (2 : ℝ) ^ n * ((2*x-y)-x) by
        exact (hend (2*x-y) (by simpa [hdxy] using lt_of_lt_of_le hxy (min_le_left _ _))).1.trans'
          (by linarith))
    have hb := hU _ (hend (2*x-y) (by simpa [hdxy] using lt_of_lt_of_le hxy (min_le_left _ _)))
    have hC : U - f x ≤ C := le_max_left _ _
    rw [show x + ((2*x-y)-x) = 2*x-y by ring] at hd
    calc
      f (2*x-y) - f x ≤ (U-f x)/(2:ℝ)^n := by
        apply (sub_le_iff_le_add).2
        calc
          f (2*x-y) ≤ (1 - ((2:ℝ)^n)⁻¹)*f x + ((2:ℝ)^n)⁻¹ *
              f (x+(2:ℝ)^n*((2*x-y)-x)) := hd
          _ ≤ (1 - ((2:ℝ)^n)⁻¹)*f x + ((2:ℝ)^n)⁻¹*U := by gcongr
          _ = (U-f x)/(2:ℝ)^n + f x := by field_simp; ring
      _ ≤ C/(2:ℝ)^n := div_le_div_of_nonneg_right hC (le_of_lt hp)
      _ < ε/2 := hn
  have hlower : f x - f y < ε / 2 := by
    have hm : f x ≤ (f y + f (2*x-y))/2 := by
      have hz0 : 0 ≤ 2*x-y := by
        have hh := lt_of_lt_of_le hxy (min_le_right _ _)
        rw [abs_lt] at hh
        linarith
      have harg : (y + (2*x-y))/2 = x := by ring
      simpa only [harg] using hf y hy0 (2*x-y) hz0
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- An explicit linear squeeze gives right continuity at vacuum density. -/
theorem continuousWithinAt_zero_of_linear_squeeze
    {f : ℝ → ℝ} (hf0 : f 0 = 0) {A B : ℝ}
    (hlo : ∀ x, 0 ≤ x → -A * x ≤ f x)
    {δ : ℝ} (hδ : 0 < δ)
    (hhi : ∀ x ∈ Set.Icc (0 : ℝ) δ, f x ≤ B * x) :
    ContinuousWithinAt f (Set.Ici 0) 0 := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  let C := max (|A| + |B|) 1
  refine ⟨min (ε / C) δ, lt_min (div_pos hε
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _))) hδ, ?_⟩
  intro y hy hyε
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hy0 : 0 ≤ y := hy
  have hay : |A| * y ≤ C * y := mul_le_mul_of_nonneg_right
    (le_trans (le_add_of_nonneg_right (abs_nonneg B)) (le_max_left _ _)) hy0
  have hby : |B| * y ≤ C * y := mul_le_mul_of_nonneg_right
    (le_trans (le_add_of_nonneg_left (abs_nonneg A)) (le_max_left _ _)) hy0
  have hySmall : y < ε / C := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hy0] at hyε
    exact lt_of_lt_of_le hyε (min_le_left _ _)
  have hyδ : y ≤ δ := le_of_lt <| by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hy0] at hyε
    exact lt_of_lt_of_le hyε (min_le_right _ _)
  have hyC : C * y < ε := by simpa [mul_comm] using (lt_div_iff₀ hC).mp hySmall
  rw [Real.dist_eq, hf0, sub_zero, abs_lt]
  constructor
  · calc
      -ε < -(|A| * y) := by linarith
      _ ≤ -A * y := by
        have := neg_le_neg (le_abs_self A)
        simpa only [neg_mul] using mul_le_mul_of_nonneg_right this hy0
      _ ≤ f y := hlo y hy0
  · calc
      f y ≤ B * y := hhi y ⟨hy0, hyδ⟩
      _ ≤ |B| * y := mul_le_mul_of_nonneg_right (le_abs_self B) hy0
      _ < ε := lt_of_le_of_lt hby hyC

/-- Continuity on nonnegative densities from the interior midpoint argument and the vacuum
linear squeeze. -/
theorem continuousOn_nonneg_of_midpointConvex_of_bounds
    {f : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ x → ∀ y, 0 ≤ y → f ((x + y) / 2) ≤ (f x + f y) / 2)
    (hub : ∀ x, 0 < x → ∃ r > 0, r ≤ x ∧ ∃ U,
      ∀ y ∈ Set.Icc (x-r) (x+r), f y ≤ U)
    (hf0 : f 0 = 0) {A B δ : ℝ}
    (hlo : ∀ x, 0 ≤ x → -A*x ≤ f x) (hδ : 0 < δ)
    (hhi : ∀ x ∈ Set.Icc (0 : ℝ) δ, f x ≤ B*x) :
    ContinuousOn f (Set.Ici 0) := by
  intro x hx
  rcases hx.eq_or_lt with rfl | hx
  · exact continuousWithinAt_zero_of_linear_squeeze hf0 hlo hδ hhi
  · exact (continuousAt_of_midpointConvexOnNonneg_of_locally_boundedAbove hf hub hx).continuousWithinAt

end LiebThirring.ThermoLimit

end
