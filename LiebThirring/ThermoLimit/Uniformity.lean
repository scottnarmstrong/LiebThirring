/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.Convexity
public import LiebThirring.ThermoLimit.Renewal
public import Mathlib.Topology.UniformSpace.Dini

/-!
# Uniform convergence in the density

Dini convergence and a quantitative defect estimate, separated from the thermodynamic construction.
-/

public section

open Filter Topology

namespace LiebThirring.ThermoLimit

/-- Dini's theorem in the exact decreasing-majorant form used by the renewal argument. -/
theorem antitone_majorant_tendstoUniformlyOn
    {H : ℕ → ℝ → ℝ} {e : ℝ → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hHc : ∀ n, ContinuousOn (H n) K)
    (hanti : ∀ x ∈ K, Antitone fun n ↦ H n x)
    (hec : ContinuousOn e K)
    (hlim : ∀ x ∈ K, Tendsto (fun n ↦ H n x) atTop (𝓝 (e x))) :
    TendstoUniformlyOn H e atTop K :=
  Antitone.tendstoUniformlyOn_of_forall_tendsto hK hHc hanti hec hlim

/-- If `α dₙ = Hₙ - Hₙ₊₁`, uniform convergence of `H` forces the defects to vanish
uniformly. -/
theorem defect_tendstoUniformlyOn_zero
    {H d : ℕ → ℝ → ℝ} {e : ℝ → ℝ} {K : Set ℝ} {α : ℝ}
    (hα : 0 < α) (hH : TendstoUniformlyOn H e atTop K)
    (hrel : ∀ n x, α * d n x = H n x - H (n + 1) x) :
    TendstoUniformlyOn d (fun _ ↦ 0) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rw [Metric.tendstoUniformlyOn_iff] at hH
  rcases eventually_atTop.1 (hH (α * ε / 2)
    (div_pos (mul_pos hα hε) (by norm_num))) with ⟨N, hN⟩
  refine eventually_atTop.2 ⟨N, fun n hn x hx ↦ ?_⟩
  have hn0 := hN n hn x hx
  have hn1 := hN (n + 1) (hn.trans (Nat.le_add_right n 1)) x hx
  rw [Real.dist_eq]
  simp only [zero_sub, abs_neg]
  rw [abs_lt]
  rw [Real.dist_eq, abs_sub_comm] at hn0 hn1
  have hrelation := hrel n x
  constructor
  · have : -(α * ε) < α * d n x := by linarith [abs_lt.mp hn0, abs_lt.mp hn1]
    nlinarith
  · have : α * d n x < α * ε := by linarith [abs_lt.mp hn0, abs_lt.mp hn1]
    nlinarith

/-- Subtracting uniformly vanishing renewal defects preserves the uniform limit of the
majorants. -/
theorem sub_defect_tendstoUniformlyOn
    {H d f : ℕ → ℝ → ℝ} {e : ℝ → ℝ} {K : Set ℝ}
    (hH : TendstoUniformlyOn H e atTop K)
    (hd : TendstoUniformlyOn d (fun _ ↦ 0) atTop K)
    (hf : ∀ n x, f n x = H n x - d n x) :
    TendstoUniformlyOn f e atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rw [Metric.tendstoUniformlyOn_iff] at hH hd
  filter_upwards [hH (ε / 2) (half_pos hε), hd (ε / 2) (half_pos hε)] with n hHn hdn
  intro x hx
  have h1 := hHn x hx
  have h2 := hdn x hx
  rw [Real.dist_eq] at h1
  rw [Real.dist_eq] at h2
  have h2' : |d n x| < ε / 2 := by simpa only [zero_sub, abs_neg] using h2
  rw [Real.dist_eq, hf]
  have hrewrite : e x - (H n x - d n x) = (e x - H n x) + d n x := by ring
  rw [hrewrite]
  exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)

/-- The complete uniform convergence Dini-defect mechanism. -/
theorem renewal_tendstoUniformlyOn
    {H d f : ℕ → ℝ → ℝ} {e : ℝ → ℝ} {K : Set ℝ} {α : ℝ}
    (hK : IsCompact K) (hHc : ∀ n, ContinuousOn (H n) K)
    (hanti : ∀ x ∈ K, Antitone fun n ↦ H n x)
    (hec : ContinuousOn e K)
    (hlim : ∀ x ∈ K, Tendsto (fun n ↦ H n x) atTop (𝓝 (e x)))
    (hα : 0 < α) (hrel : ∀ n x, α * d n x = H n x - H (n + 1) x)
    (hf : ∀ n x, f n x = H n x - d n x) :
    TendstoUniformlyOn f e atTop K := by
  have hH := antitone_majorant_tendstoUniformlyOn hK hHc hanti hec hlim
  exact sub_defect_tendstoUniformlyOn hH (defect_tendstoUniformlyOn_zero hα hH hrel) hf

end LiebThirring.ThermoLimit

end
