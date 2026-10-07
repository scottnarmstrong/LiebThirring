/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoBounds.ComplementaryGeometry
import Mathlib.Tactic

/-!
# Passing the complementary comparison to the lower limit

Internal analytic lower-limit comparison transfer. The finite comparison is an input to
this helper only; the arbitrary-radius energy theorem proves it from
integer physics. Continuity is used near the fixed positive density.
No sign of the energy is assumed, and the lattice defect tends to zero
only after the filler scale has been fixed.
-/

public section

open Filter Topology Finset Set

namespace LiebThirring.ThermoBounds

theorem eventually_limit_sub_le_of_lower_comparison
    {a s : ℕ → ℝ} {f : ℕ → ℝ → ℝ} {e : ℝ → ℝ}
    {W : ℕ → ℝ} {U η : ℕ → ℕ → ℝ} {K : ℕ → ℕ} {ρ : ℝ}
    (hρ : 0 < ρ) (hs : Tendsto s atTop (𝓝 ρ))
    (he : ContinuousOn e (Ici 0))
    (huniform : ∀ (l u : ℝ), 0 ≤ l → l ≤ u → ∀ δ > 0, ∃ n₀,
      ∀ n ≥ n₀, ∀ x ∈ Set.Icc l u, |f n x - e x| ≤ δ)
    (hK : Tendsto K atTop atTop)
    (hη : ∀ k, Tendsto (η k) atTop (𝓝 0))
    (hgeometry : ∀ k, ∀ᶠ j in atTop,
      (28 : ℝ) ^ (-3 : ℤ) ≤ W j ∧ W j ≤ 1 ∧
      0 ≤ U k j ∧ 0 ≤ η k j ∧ W j + U k j + η k j = 1)
    (hcomparison : ∀ t, 1 ≤ t → ∀ k, t < k → ∀ᶠ j in atTop,
      f (K j) (s j * (W j + retainedFraction t * U k j)) ≤
        W j * a j + U k j * ∑ h ∈ range t,
          ((1 / 28 : ℝ) * swissCheeseGamma ^ h) * f (k - h - 1) (s j)) :
    ∀ ε > 0, ∀ᶠ j in atTop, e ρ - ε ≤ a j := by
  intro ε hε
  let C : ℝ := (28 : ℝ) ^ 3
  let τ : ℝ := ε / (16 * C)
  have hC : 0 < C := by dsimp [C]; positivity
  have hτ : 0 < τ := div_pos hε (mul_pos (by norm_num) hC)
  have heAt : ContinuousAt e ρ := he.continuousAt (Ici_mem_nhds hρ)
  obtain ⟨d, hd, hcont⟩ := Metric.continuousAt_iff.mp heAt τ hτ
  have hdistTail : Tendsto (fun t : ℕ => (4 * ρ) * swissCheeseGamma ^ t)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_swissCheese_residual
  have henergyTail : Tendsto (fun t : ℕ => (2 * |e ρ|) * swissCheeseGamma ^ t)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_swissCheese_residual
  obtain ⟨t, htdist, htenergy, ht⟩ :=
    (((tendsto_order.1 hdistTail).2 (d / 2) (half_pos hd)).and
      (((tendsto_order.1 henergyTail).2 τ hτ).and (eventually_ge_atTop 1))).exists
  let g : ℝ := swissCheeseGamma ^ t
  let c : ℝ := retainedFraction t
  have hg : g ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [g]; exact pow_nonneg (by norm_num [swissCheeseGamma]) _
    · dsimp [g]; exact pow_le_one₀ (by norm_num [swissCheeseGamma])
        (by norm_num [swissCheeseGamma])
  have hgpos : 0 < g := pow_pos (by norm_num [swissCheeseGamma]) _
  have hc0 : 0 ≤ c := retainedFraction_nonneg t
  have hc1 : c ≤ 1 := retainedFraction_le_one t
  let l : ℝ := (ρ / 2) * (28 : ℝ) ^ (-3 : ℤ)
  let u : ℝ := 2 * ρ
  have hl0 : 0 ≤ l := by dsimp [l]; positivity
  have hlu : l ≤ u := by dsimp [l, u]; norm_num; linarith only [hρ]
  obtain ⟨n₀, hn₀⟩ := huniform l u hl0 hlu τ hτ
  let k := n₀ + t + 1
  have htk : t < k := by omega
  have hsrange : ∀ᶠ j in atTop, s j ∈ Set.Icc (ρ / 2) (2 * ρ) :=
    (hs.eventually (Ioo_mem_nhds (by linarith only [hρ])
      (by linarith only [hρ]))).mono fun _ hj => ⟨hj.1.le, hj.2.le⟩
  have hsclose : ∀ᶠ j in atTop, dist (s j) ρ < d / 2 :=
    hs.eventually (Metric.ball_mem_nhds ρ (half_pos hd))
  have hηsmall : ∀ᶠ j in atTop, η k j ≤ g :=
    ((tendsto_order.1 (hη k)).2 g hgpos).mono fun _ hj => hj.le
  filter_upwards [hsrange, hsclose, hηsmall, hK.eventually (eventually_ge_atTop n₀),
    hgeometry k, hcomparison t ht k htk] with j hsj hclose hηj hKj hgeom hcomp
  obtain ⟨hW, hW1, hU0, hη0, hsum⟩ := hgeom
  have hpoint := complementary_geometry hρ hsj hW hW1 hU0 hη0 hsum hg hηj
  change 0 ≤ 1 - W j - c * U k j ∧ 1 - W j - c * U k j ≤ 2 * g ∧
    0 ≤ U k j ∧ U k j ≤ 1 ∧
    s j * (W j + c * U k j) ∈ Set.Icc l u ∧
    |s j * (W j + c * U k j) - s j| ≤ 4 * ρ * g ∧
    1 - W j - c * U k j = (1 - c) * (1 - W j) + c * η k j at hpoint
  obtain ⟨hΔ0, hΔ2, _, hU1, hspmem, hdiff, hΔid⟩ := hpoint
  let sp := s j * (W j + c * U k j)
  have hspclose : dist sp ρ < d := by
    calc
      dist sp ρ ≤ dist sp (s j) + dist (s j) ρ := dist_triangle _ _ _
      _ ≤ 4 * ρ * g + dist (s j) ρ := by
        exact add_le_add (by simpa only [sp, Real.dist_eq] using hdiff) le_rfl
      _ < d := by change (4 * ρ) * g < d / 2 at htdist; linarith only [htdist, hclose]
  have heSp : |e sp - e ρ| < τ := by
    simpa only [Real.dist_eq] using hcont hspclose
  have heS : |e (s j) - e ρ| < τ := by
    simpa only [Real.dist_eq] using hcont (hclose.trans (by linarith only [hd]))
  have hsI : s j ∈ Set.Icc l u := by
    refine ⟨?_, hsj.2⟩
    have hsmall : l ≤ ρ / 2 := by dsimp [l]; norm_num; linarith only [hρ]
    exact hsmall.trans hsj.1
  have hKapprox : e sp - τ ≤ f (K j) sp := by
    have hh := hn₀ (K j) hKj sp hspmem
    exact (sub_le_iff_le_add).2 (by linarith only [abs_le.mp hh |>.1])
  have hfill : ∀ h < t, f (k - h - 1) (s j) ≤ e ρ + 2 * τ := by
    intro h hht
    have hh := hn₀ (k - h - 1) (by dsimp [k]; omega) (s j) hsI
    linarith only [abs_le.mp hh |>.2, abs_lt.mp heS |>.2]
  have hmod : e ρ - τ ≤ e sp := by linarith only [abs_lt.mp heSp |>.1]
  have herr0 : 0 ≤ τ + |e ρ| * (1 - W j - c * U k j) + τ + U k j * c * (2 * τ) := by
    positivity
  have hlo := lower_bound_of_complementary_comparison
    (c := c) (eS := e ρ) (eS' := e sp) (δK := τ) (δ := 2 * τ) (ω := τ)
    (B := |e ρ|) hW hU0 hΔid hΔ0 hcomp rfl hKapprox hfill hmod le_rfl herr0
  have hBΔ : |e ρ| * (1 - W j - c * U k j) ≤ 2 * |e ρ| * g := by
    calc
      _ ≤ |e ρ| * (2 * g) := mul_le_mul_of_nonneg_left hΔ2 (abs_nonneg _)
      _ = _ := by ring
  have hUc : U k j * c ≤ 1 :=
    (mul_le_mul_of_nonneg_right hU1 hc0).trans (by simpa only [one_mul] using hc1)
  have hterm : U k j * c * (2 * τ) ≤ 2 * τ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hUc (by positivity : 0 ≤ 2 * τ)
  have herr : τ + |e ρ| * (1 - W j - c * U k j) + τ + U k j * c * (2 * τ) ≤ 5 * τ := by
    change (2 * |e ρ|) * g < τ at htenergy
    linarith only [hBΔ, htenergy, hterm]
  have htol : C * (5 * τ) ≤ ε := by
    dsimp [C, τ]
    norm_num
    linarith only [hε]
  rw [← hΔid] at hlo
  have hscaled := (mul_le_mul_of_nonneg_left herr hC.le).trans htol
  change C * _ ≤ ε at hscaled
  linarith only [hlo, hscaled]

end LiebThirring.ThermoBounds

end
