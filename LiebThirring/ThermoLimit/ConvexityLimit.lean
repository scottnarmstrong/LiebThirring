/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.ConvexityDyadic
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Convexity from continuous midpoint convexity

Limit convexity passes the dyadic inequalities to every real coefficient, including
zero-density endpoints. No convexity or continuity of the limit is assumed
in the canonical assembly: those are supplied by the preceding analytic steps.
-/

public section

open Filter Topology Set

namespace LiebThirring.ThermoLimit

theorem convexOn_nonneg_of_midpoint_and_continuous
    {f : ℝ → ℝ}
    (hmid : ∀ x, 0 ≤ x → ∀ y, 0 ≤ y → f ((x + y) / 2) ≤ (f x + f y) / 2)
    (hc : ContinuousOn f (Ici 0)) : ConvexOn ℝ (Ici 0) f := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  change f (a * x + b * y) ≤ a * f x + b * f y
  have ha1 : a ≤ 1 := by linarith only [hb, hab]
  have hb' : b = 1 - a := by linarith only [hab]
  let m := fun n : ℕ => ⌊a * (2 : ℝ) ^ n⌋₊
  let t := fun n : ℕ => (m n : ℝ) / (2 : ℝ) ^ n
  have hp (n : ℕ) : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hm (n : ℕ) : m n ≤ 2 ^ n := by
    have hfloor := Nat.floor_le (mul_nonneg ha (hp n).le)
    have hbound : (m n : ℝ) ≤ (2 : ℝ) ^ n := by
      exact hfloor.trans (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right ha1 (hp n).le)
    exact_mod_cast hbound
  have ht0 (n : ℕ) : 0 ≤ t n := div_nonneg (Nat.cast_nonneg _) (hp n).le
  have ht1 (n : ℕ) : t n ≤ 1 := by
    apply (div_le_one (hp n)).mpr
    exact_mod_cast hm n
  have ht : Tendsto t atTop (𝓝 a) :=
    (tendsto_nat_floor_mul_div_atTop ha).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have harg : Tendsto (fun n => t n * x + (1 - t n) * y) atTop
      (𝓝 (a * x + (1 - a) * y)) :=
    (ht.mul_const x).add ((tendsto_const_nhds.sub ht).mul_const y)
  have harg0 (n : ℕ) : 0 ≤ t n * x + (1 - t n) * y :=
    add_nonneg (mul_nonneg (ht0 n) hx) (mul_nonneg (sub_nonneg.mpr (ht1 n)) hy)
  have htarget0 : 0 ≤ a * x + (1 - a) * y :=
    add_nonneg (mul_nonneg ha hx) (mul_nonneg (sub_nonneg.mpr ha1) hy)
  have hleft : Tendsto (fun n => f (t n * x + (1 - t n) * y)) atTop
      (𝓝 (f (a * x + (1 - a) * y))) :=
    Filter.Tendsto.comp (hc _ htarget0) (tendsto_nhdsWithin_iff.mpr
      ⟨harg, Eventually.of_forall harg0⟩)
  have hright : Tendsto (fun n => t n * f x + (1 - t n) * f y) atTop
      (𝓝 (a * f x + (1 - a) * f y)) :=
    (ht.mul_const _).add ((tendsto_const_nhds.sub ht).mul_const _)
  have hle := le_of_tendsto_of_tendsto hleft hright
    (Eventually.of_forall (fun n => midpoint_convex_dyadic hmid hx hy n (m n) (hm n)))
  simpa only [hb'] using hle

end LiebThirring.ThermoLimit

end
