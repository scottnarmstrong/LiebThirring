/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.SwissCheeseAlgebra
import Mathlib.Tactic

/-!
# Analytic estimates for the arbitrary-ball comparisons

Internal estimates used to pass from the finite upper and complementary packing
comparisons to the thermodynamic limit.  The comparison inequalities themselves
remain explicit hypotheses: this module contains no packing or physics assertion.
-/

public section

open Filter Finset Set Topology

namespace LiebThirring.ThermoBounds

/-- The retained fraction after the first `t` zero-based Swiss-cheese levels. -/
@[expose] noncomputable def retainedFraction (t : ℕ) : ℝ := 1 - swissCheeseGamma ^ t

theorem retainedFraction_eq_sum (t : ℕ) :
    retainedFraction t =
      ∑ h ∈ range t, (1 / 28 : ℝ) * swissCheeseGamma ^ h := by
  rw [sum_swissCheese_weight]
  rfl

theorem retainedFraction_pos {t : ℕ} (ht : 1 ≤ t) : 0 < retainedFraction t := by
  change 0 < 1 - (27 / 28 : ℝ) ^ t
  have hpow : (27 / 28 : ℝ) ^ t < 1 ^ t :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  simpa only [one_pow, sub_pos] using hpow

theorem swissCheese_weight_nonneg (h : ℕ) :
    0 ≤ (1 / 28 : ℝ) * swissCheeseGamma ^ h := by
  norm_num [swissCheeseGamma]

theorem retainedFraction_nonneg (t : ℕ) : 0 ≤ retainedFraction t := by
  change 0 ≤ 1 - (27 / 28 : ℝ) ^ t
  exact sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))

theorem retainedFraction_le_one (t : ℕ) : retainedFraction t ≤ 1 := by
  change 1 - (27 / 28 : ℝ) ^ t ≤ 1
  exact sub_le_self _ (by positivity)

/-- Algebraic deficit estimate used after fixing the truncation depth. -/
theorem complementary_deficit_bounds
    {W U η g : ℝ} (hW : 0 ≤ W) (hU : 0 ≤ U) (hη : 0 ≤ η)
    (hsum : W + U + η = 1) (hηg : η ≤ g) :
    0 ≤ 1 - W - (1 - g) * U ∧ 1 - W - (1 - g) * U ≤ 2 * g := by
  have hUle : U ≤ 1 := by linarith
  have hg : 0 ≤ g := hη.trans hηg
  constructor
  · nlinarith
  · nlinarith

theorem tendsto_retainedFraction :
    Tendsto retainedFraction atTop (𝓝 1) := by
  change Tendsto (fun t => 1 - swissCheeseGamma ^ t) atTop (𝓝 1)
  simpa only [sub_zero] using tendsto_const_nhds.sub tendsto_swissCheese_residual

/-- Signed arithmetic behind the upper comparison.  This is deliberately
separate from the geometric comparison which supplies `hcomparison`. -/
theorem upper_bound_of_comparison
    {a μ x y δ : ℝ} {t k : ℕ} {f : ℕ → ℝ → ℝ}
    (hμ : 0 ≤ μ)
    (hcomparison :
      a ≤ μ * ∑ h ∈ range t,
        (1 / 28 : ℝ) * swissCheeseGamma ^ h * f (k - h - 1) x)
    (happrox : ∀ h < t, f (k - h - 1) x ≤ y + δ) :
    a ≤ μ * retainedFraction t * (y + δ) := by
  calc
    a ≤ μ * ∑ h ∈ range t,
        (1 / 28 : ℝ) * swissCheeseGamma ^ h * f (k - h - 1) x := hcomparison
    _ ≤ μ * ∑ h ∈ range t,
        (1 / 28 : ℝ) * swissCheeseGamma ^ h * (y + δ) := by
      apply mul_le_mul_of_nonneg_left _ hμ
      apply sum_le_sum
      intro h hh
      exact mul_le_mul_of_nonneg_left (happrox h (mem_range.mp hh))
        (swissCheese_weight_nonneg h)
    _ = μ * retainedFraction t * (y + δ) := by
      rw [← sum_mul, ← retainedFraction_eq_sum]
      ring

/-- Internal interior packing comparison transfer. The only geometric/physical input is the
displayed eventual comparison at each fixed pair `t,k`. -/
theorem eventually_le_limit_add_of_upper_comparison
    {a s : ℕ → ℝ} {f : ℕ → ℝ → ℝ} {e : ℝ → ℝ}
    {μ : ℕ → ℕ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (hs : Tendsto s atTop (𝓝 ρ))
    (he : ContinuousOn e (Ici 0))
    (huniform : ∀ l u, 0 ≤ l → l ≤ u → ∀ δ > 0, ∃ n₀,
      ∀ n ≥ n₀, ∀ x ∈ Set.Icc l u, |f n x - e x| ≤ δ)
    (hμ : ∀ k, Tendsto (μ k) atTop (𝓝 1))
    (hcomparison : ∀ t, 1 ≤ t → ∀ k, t < k → ∀ᶠ j in atTop,
      0 ≤ μ k j ∧
      a j ≤ μ k j * ∑ h ∈ range t,
        (1 / 28 : ℝ) * swissCheeseGamma ^ h *
          f (k - h - 1) (s j / (retainedFraction t * μ k j))) :
    ∀ ε > 0, ∀ᶠ j in atTop, a j ≤ e ρ + ε := by
  intro ε hε
  have hscaleArg : Tendsto (fun t => ρ / retainedFraction t) atTop (𝓝 ρ) := by
    convert tendsto_const_nhds.div tendsto_retainedFraction (by norm_num : (1 : ℝ) ≠ 0) using 1
    simp
  have hscaleArgNonneg : ∀ᶠ t in atTop, ρ / retainedFraction t ∈ Ici (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    exact div_nonneg hρ.le (retainedFraction_pos ht).le
  have heScale : Tendsto (fun t => e (ρ / retainedFraction t)) atTop (𝓝 (e ρ)) :=
    Filter.Tendsto.comp (he ρ hρ.le)
      (tendsto_nhdsWithin_iff.mpr ⟨hscaleArg, hscaleArgNonneg⟩)
  have hscale : Tendsto
      (fun t => retainedFraction t * e (ρ / retainedFraction t)) atTop (𝓝 (e ρ)) := by
    simpa only [one_mul] using tendsto_retainedFraction.mul heScale
  have hscaleEv : ∀ᶠ t in atTop,
      retainedFraction t * e (ρ / retainedFraction t) < e ρ + ε / 4 :=
    (tendsto_order.1 hscale).2 _ (by linarith)
  rcases (hscaleEv.and (eventually_ge_atTop 1)).exists with ⟨t, hscaleLt, ht⟩
  let c := retainedFraction t
  have hcpos : 0 < c := retainedFraction_pos ht
  let l := (ρ / c) / 2
  let u := 2 * (ρ / c)
  have hlu : l ≤ u := by
    dsimp [l, u]
    have : 0 < ρ / c := div_pos hρ hcpos
    linarith
  have hl0 : 0 ≤ l := by positivity
  rcases huniform l u hl0 hlu (ε / 4) (by linarith) with ⟨n₀, hn₀⟩
  let k := n₀ + t + 1
  have htk : t < k := by omega
  have hx : Tendsto (fun j => s j / (c * μ k j)) atTop (𝓝 (ρ / c)) := by
    have hden : Tendsto (fun j => c * μ k j) atTop (𝓝 c) := by
      simpa only [mul_one] using tendsto_const_nhds.mul (hμ k)
    exact hs.div hden hcpos.ne'
  have hxmem : ∀ᶠ j in atTop, s j / (c * μ k j) ∈ Icc l u := by
    have hinside : ρ / c ∈ Ioo l u := by
      have : 0 < ρ / c := div_pos hρ hcpos
      constructor <;> dsimp [l, u] <;> linarith
    exact (hx.eventually (Ioo_mem_nhds hinside.1 hinside.2)).mono
      fun _ hj => ⟨hj.1.le, hj.2.le⟩
  have hxnonneg : ∀ᶠ j in atTop, s j / (c * μ k j) ∈ Ici (0 : ℝ) :=
    hxmem.mono fun _ hj => hl0.trans hj.1
  have heX : Tendsto (fun j => e (s j / (c * μ k j))) atTop (𝓝 (e (ρ / c))) :=
    Filter.Tendsto.comp (he (ρ / c) (div_nonneg hρ.le hcpos.le))
      (tendsto_nhdsWithin_iff.mpr ⟨hx, hxnonneg⟩)
  have hboundLim : Tendsto
      (fun j => μ k j * c * (e (s j / (c * μ k j)) + ε / 4)) atTop
      (𝓝 (c * (e (ρ / c) + ε / 4))) := by
    simpa only [one_mul] using
      ((hμ k).mul tendsto_const_nhds).mul (heX.add tendsto_const_nhds)
  have hboundEv : ∀ᶠ j in atTop,
      μ k j * c * (e (s j / (c * μ k j)) + ε / 4) <
        c * (e (ρ / c) + ε / 4) + ε / 4 :=
    (tendsto_order.1 hboundLim).2 _ (by linarith)
  filter_upwards [hcomparison t ht k htk, hxmem, hboundEv] with j hj hxm hlim
  have happ : ∀ h < t,
      f (k - h - 1) (s j / (c * μ k j)) ≤
        e (s j / (c * μ k j)) + ε / 4 := by
    intro h hht
    have habs := hn₀ (k - h - 1) (by dsimp [k]; omega) _ hxm
    rw [abs_le] at habs
    linarith
  have ha := upper_bound_of_comparison hj.1 hj.2 happ
  change a j ≤ μ k j * c * (e (s j / (c * μ k j)) + ε / 4) at ha
  exact le_of_lt <| calc
    a j ≤ μ k j * c * (e (s j / (c * μ k j)) + ε / 4) := ha
    _ < c * (e (ρ / c) + ε / 4) + ε / 4 := hlim
    _ ≤ e ρ + ε := by
      have hc : c ≤ 1 := retainedFraction_le_one t
      dsimp [c] at hscaleLt ⊢
      nlinarith

/-- Fully signed rearrangement of the complementary comparison.  In particular,
the term involving `e` is controlled by `|e|`; no sign of the limiting energy is
assumed. -/
theorem lower_bound_of_complementary_comparison
    {a W U η c s s' eS eS' δK δ ω B : ℝ} {t K k : ℕ}
    {f : ℕ → ℝ → ℝ}
    (hW : (28 : ℝ) ^ (-3 : ℤ) ≤ W) (hU : 0 ≤ U)
    (hΔ : 1 - W - c * U = (1 - c) * (1 - W) + c * η)
    (hΔnonneg : 0 ≤ 1 - W - c * U)
    (hcomparison :
      f K s' ≤ W * a + U * ∑ h ∈ range t,
        (1 / 28 : ℝ) * swissCheeseGamma ^ h * f (k - h - 1) s)
    (hc : c = retainedFraction t)
    (hK : eS' - δK ≤ f K s')
    (hfill : ∀ h < t, f (k - h - 1) s ≤ eS + δ)
    (hmod : eS - ω ≤ eS') (heabs : |eS| ≤ B)
    (herrors : 0 ≤ ω + B * (1 - W - c * U) + δK + U * c * δ) :
    eS - (28 : ℝ) ^ 3 *
      (ω + B * ((1 - c) * (1 - W) + c * η) + δK + U * c * δ) ≤ a := by
  have hWpos : 0 < W := lt_of_lt_of_le (by norm_num) hW
  have hsum :
      ∑ h ∈ range t, (1 / 28 : ℝ) * swissCheeseGamma ^ h * f (k - h - 1) s ≤
        c * (eS + δ) := by
    calc
      _ ≤ ∑ h ∈ range t,
          (1 / 28 : ℝ) * swissCheeseGamma ^ h * (eS + δ) := by
        apply sum_le_sum
        intro h hh
        exact mul_le_mul_of_nonneg_left (hfill h (mem_range.mp hh))
          (swissCheese_weight_nonneg h)
      _ = c * (eS + δ) := by rw [← sum_mul, ← retainedFraction_eq_sum, ← hc]
  have hbase : eS' - δK - U * c * (eS + δ) ≤ W * a := by
    calc
      eS' - δK - U * c * (eS + δ) ≤ f K s' - U * c * (eS + δ) := by linarith
      _ ≤ W * a := by
        have := hcomparison
        have hmul := mul_le_mul_of_nonneg_left hsum hU
        linarith
  have heLower : -B ≤ eS := (neg_le_of_abs_le heabs)
  have hprod : -B * (1 - W - c * U) ≤ eS * (1 - W - c * U) :=
    mul_le_mul_of_nonneg_right heLower hΔnonneg
  have hnum :
      W * eS - (ω + B * (1 - W - c * U) + δK + U * c * δ) ≤ W * a := by
    linarith only [hbase, hmod, hprod]
  have hinv : W⁻¹ ≤ (28 : ℝ) ^ 3 := by
    rw [inv_le_comm₀ hWpos (by positivity)]
    norm_num at hW ⊢
    exact hW
  have hscaled :
      eS - W⁻¹ * (ω + B * (1 - W - c * U) + δK + U * c * δ) ≤ a := by
    apply le_of_mul_le_mul_left _ hWpos
    simpa only [mul_sub, ← mul_assoc, mul_inv_cancel₀ hWpos.ne', one_mul] using hnum
  rw [← hΔ]
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_right hinv herrors) eS).trans hscaled


end LiebThirring.ThermoBounds

end
