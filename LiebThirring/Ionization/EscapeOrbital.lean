/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.Variational.TrialOrbitals
public import LiebThirring.Fourier.Schwartz
/-! # Compact remote orbitals for escape trials

The orbital has amplitude `(L * sqrt L)⁻¹ = L⁻³ᐟ²` and argument
`L⁻¹ • (x-a)`. The dimension-three change of variables preserves its L² mass,
while every directional derivative-square integral scales by `L⁻²`.
-/

public section
open MeasureTheory Set Function
open scoped ENNReal NNReal ContDiff SchwartzMap
namespace LiebThirring
/-- Translate and dilate a scalar orbital with the dimension-three L² normalization. -/
@[expose] noncomputable def escapeOrbital (h : Position → ℂ) (L : ℝ) (a : Position) : Position → ℂ :=
  fun x => (L * Real.sqrt L)⁻¹ • h (L⁻¹ • (x - a))

/-- The translated dilated orbital has the same L² mass as its base orbital. -/
theorem integral_norm_sq_escapeOrbital (h : Position → ℂ) (L : ℝ) (hL : 0 < L)
    (a : Position) :
    (∫ x, ‖escapeOrbital h L a x‖ ^ 2) = ∫ x, ‖h x‖ ^ 2 := by
  simp only [escapeOrbital, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul]
  rw [integral_sub_right_eq_self (fun x : Position => ‖h (L⁻¹ • x)‖ ^ 2) a]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun x : Position => ‖h x‖ ^ 2) hL.le]
  have hd : Module.finrank ℝ Position = 3 := by simp [Position]
  rw [hd, smul_eq_mul]
  have hs : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
  have hsn : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  have he : ((L * Real.sqrt L)⁻¹) ^ 2 * L ^ 3 = 1 := by
    field_simp
    nlinarith only [hs]
  rw [← mul_assoc, he, one_mul]

/-- A base orbital vanishing outside the unit ball dilates to radius `L` about `a`. -/
theorem escapeOrbital_eq_zero_of_dist_gt (h : Position → ℂ)
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (L : ℝ) (hL : 0 < L) (a x : Position)
    (hx : L < dist x a) : escapeOrbital h L a x = 0 := by
  unfold escapeOrbital
  have hn : 1 < ‖L⁻¹ • (x - a)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    rw [← div_eq_inv_mul, lt_div_iff₀ hL]
    simpa only [one_mul, dist_eq_norm] using hx
  rw [hh _ hn, smul_zero]

/-- The dilated orbital is compactly supported. -/
theorem hasCompactSupport_escapeOrbital (h : Position → ℂ)
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (L : ℝ) (hL : 0 < L) (a : Position) :
    HasCompactSupport (escapeOrbital h L a) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall a L)
  intro x hx
  rw [Metric.mem_closedBall]
  by_contra hnot
  exact hx (escapeOrbital_eq_zero_of_dist_gt h hh L hL a x (lt_of_not_ge hnot))

/-- Translation, dilation and scalar normalization preserve smoothness. -/
theorem contDiff_escapeOrbital (h : Position → ℂ) (hh : ContDiff ℝ ∞ h)
    (L : ℝ) (a : Position) : ContDiff ℝ ∞ (escapeOrbital h L a) := by
  unfold escapeOrbital
  have ht : ContDiff ℝ ∞ (fun x : Position => L⁻¹ • (x - a)) := by fun_prop
  exact (hh.comp ht).const_smul ((L * Real.sqrt L)⁻¹ : ℝ)

/-- A directional derivative picks up one additional factor of `L⁻¹`. -/
theorem fderiv_escapeOrbital (h : Position → ℂ) (hh : ContDiff ℝ ∞ h)
    (L : ℝ) (a x v : Position) :
    fderiv ℝ (escapeOrbital h L a) x v =
      ((L * Real.sqrt L)⁻¹ * L⁻¹) • fderiv ℝ h (L⁻¹ • (x - a)) v := by
  have ht := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const a).const_smul L⁻¹
  have hf : HasFDerivAt h (fderiv ℝ h (L⁻¹ • (x - a))) (L⁻¹ • (x - a)) :=
    (hh.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp := (hf.comp x ht).const_smul (L * Real.sqrt L)⁻¹
  rw [show fderiv ℝ (escapeOrbital h L a) x =
    (L * Real.sqrt L)⁻¹ • ((fderiv ℝ h (L⁻¹ • (x - a))).comp
      (L⁻¹ • ContinuousLinearMap.id ℝ Position)) from hcomp.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_smul]

/-- The directional derivative quadratic energy scales exactly by `L⁻²`. -/
theorem integral_norm_sq_fderiv_escapeOrbital (h : Position → ℂ)
    (hh : ContDiff ℝ ∞ h) (L : ℝ) (hL : 0 < L) (a v : Position) :
    (∫ x, ‖fderiv ℝ (escapeOrbital h L a) x v‖ ^ 2) =
      L⁻¹ ^ 2 * ∫ x, ‖fderiv ℝ h x v‖ ^ 2 := by
  simp only [fderiv_escapeOrbital h hh, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul]
  rw [integral_sub_right_eq_self
    (fun x : Position => ‖fderiv ℝ h (L⁻¹ • x) v‖ ^ 2) a]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume
    (fun x : Position => ‖fderiv ℝ h x v‖ ^ 2) hL.le]
  have hd : Module.finrank ℝ Position = 3 := by simp [Position]
  rw [hd, smul_eq_mul]
  have hs : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
  have hsn : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  have he : ((L * Real.sqrt L)⁻¹) ^ 2 * L⁻¹ ^ 2 * L ^ 3 = L⁻¹ ^ 2 := by
    field_simp
    nlinarith only [hs]
  rw [← mul_assoc, he]

/-- A normalized compact smooth scalar orbital supported in the closed unit ball exists. -/
theorem exists_normalized_compact_orbital :
    ∃ h : Position → ℂ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
      (∀ x, 1 < ‖x‖ → h x = 0) ∧ (∫ x, ‖h x‖ ^ 2) = 1 := by
  obtain ⟨b, hb, hc, hs, _, hv⟩ := exists_contDiff_tsupport_subset
    (n := (⊤ : ℕ∞)) (Metric.ball_mem_nhds (0 : Position) (by norm_num : (0 : ℝ) < 1))
  have hbc : HasCompactSupport (fun x => b x ^ 2) := hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hI : 0 < ∫ x, b x ^ 2 :=
    (hs.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (0 : Position)) hbc
      (fun x => sq_nonneg _) (by simp [hv])
  let I : ℝ := ∫ x, b x ^ 2
  let c : ℝ := (Real.sqrt I)⁻¹
  let h : Position → ℂ := fun x => c • (b x : ℂ)
  have hcont : ContDiff ℝ ∞ h :=
    (Complex.ofRealCLM.contDiff.comp hs).const_smul c
  have hz (x : Position) (hx : 1 < ‖x‖) : h x = 0 := by
    have hbx : b x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have hball := hb hm
      rw [Metric.mem_ball, dist_zero_right] at hball
      exact (not_lt.mpr hx.le) hball
    change c • (b x : ℂ) = 0
    rw [hbx, Complex.ofReal_zero, smul_zero]
  refine ⟨h, hcont, ?_, hz, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Position) 1)
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hn
    exact hx (hz x (lt_of_not_ge hn))
  · change (∫ x, ‖c • (b x : ℂ)‖ ^ 2) = 1
    simp only [norm_smul, Real.norm_eq_abs, Complex.norm_real, mul_pow, sq_abs]
    rw [integral_const_mul]
    change c ^ 2 * I = 1
    have hn : Real.sqrt I ≠ 0 := (Real.sqrt_pos.mpr hI).ne'
    dsimp only [c]
    rw [inv_pow, Real.sq_sqrt hI.le, inv_mul_cancel₀ hI.ne']

/-- The closed support is contained in the closed ball of radius `L` about `a`. -/
theorem tsupport_escapeOrbital_subset (h : Position → ℂ)
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (L : ℝ) (hL : 0 < L) (a : Position) :
    tsupport (escapeOrbital h L a) ⊆ Metric.closedBall a L := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall]
  by_contra hnot
  exact hx (escapeOrbital_eq_zero_of_dist_gt h hh L hL a x (lt_of_not_ge hnot))

/-- The full three-dimensional gradient quadratic energy scales exactly by `L⁻²`. -/
theorem sum_integral_norm_sq_fderiv_escapeOrbital (h : Position → ℂ)
    (hh : ContDiff ℝ ∞ h) (L : ℝ) (hL : 0 < L) (a : Position) :
    (∑ j : Fin 3, ∫ x, ‖fderiv ℝ (escapeOrbital h L a) x
      (PiLp.single 2 j (1 : ℝ))‖ ^ 2) =
      L⁻¹ ^ 2 * ∑ j : Fin 3, ∫ x, ‖fderiv ℝ h x (PiLp.single 2 j (1 : ℝ))‖ ^ 2 := by
  simp only [integral_norm_sq_fderiv_escapeOrbital h hh L hL]
  exact (Finset.mul_sum _ _ _).symm

/-- The compact dilated orbital bundled as a Schwartz function. -/
@[expose] noncomputable def escapeOrbitalSchwartz (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (L : ℝ) (hL : 0 < L) (a : Position) :
    𝓢(Position, ℂ) :=
  (hasCompactSupport_escapeOrbital (fun x => h x) hh L hL a).toSchwartzMap
    (contDiff_escapeOrbital (fun x => h x) (h.smooth ⊤) L a)

/-- A compact normalized scalar Schwartz orbital exists in the closed unit ball. -/
theorem exists_normalized_compact_schwartz_orbital :
    ∃ h : 𝓢(Position, ℂ), HasCompactSupport (fun x => h x) ∧
      (∀ x, 1 < ‖x‖ → h x = 0) ∧ (∫ x, ‖h x‖ ^ 2) = 1 := by
  obtain ⟨h, hd, hc, hz, hn⟩ := exists_normalized_compact_orbital
  exact ⟨hc.toSchwartzMap hd, hc, hz, hn⟩

/-- The dilated Schwartz orbital represents a normalized L² state. -/
theorem norm_toLp_escapeOrbitalSchwartz (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (hn : (∫ x, ‖h x‖ ^ 2) = 1)
    (L : ℝ) (hL : 0 < L) (a : Position) :
    ‖(escapeOrbitalSchwartz h hh L hL a).toLp 2
      (volume : Measure Position)‖ = 1 := by
  rw [SchwartzMap.norm_toLp' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  change (∫ x, ‖escapeOrbital (fun y => h y) L a x‖ ^ 2) ^ (2 : ℝ)⁻¹ = 1
  rw [integral_norm_sq_escapeOrbital (fun y => h y) L hL a, hn, Real.one_rpow]

end LiebThirring
end
