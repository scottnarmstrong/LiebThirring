/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Compact smooth cutoff approximation for Schwartz tests

Spatial dilation of a fixed bump approximates a Schwartz function together with
its first derivatives in L². This supplies the compact test core for weak coordinate derivatives.
-/

public section

open MeasureTheory Filter
open scoped SchwartzMap ENNReal Topology ContDiff

namespace LiebThirring.Sobolev

variable {E F G : Type*} [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedAddCommGroup G]

/-- Dominated pointwise convergence to zero implies convergence of the L² seminorm. -/
theorem tendsto_eLpNorm_two_zero_of_dominated {μ : Measure E} {f : ℕ → E → F}
    {b : E → G} (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hb : MemLp b 2 μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ ‖b x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0) := by
  have hint : Tendsto (fun n => ∫⁻ x, ‖f n x‖ₑ ^ (2 : ℝ) ∂μ) atTop (𝓝 0) := by
    have hz : (0 : ℝ≥0∞) = ∫⁻ x : E, (0 : ℝ≥0∞) ∂μ := by simp only [lintegral_zero]
    rw [hz]
    apply tendsto_lintegral_of_dominated_convergence' (fun x => ‖b x‖ₑ ^ (2 : ℝ))
    · exact fun n => (hf n).enorm.pow_const _
    · intro n
      filter_upwards [hbound n] with x hx
      exact ENNReal.rpow_le_rpow (by
        change (‖f n x‖₊ : ℝ≥0∞) ≤ (‖b x‖₊ : ℝ≥0∞)
        exact_mod_cast hx) (by norm_num)
    · simpa only [Function.comp_def, ENNReal.toReal_ofNat] using
        (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          ENNReal.ofNat_ne_top hb.eLpNorm_lt_top).ne
    · filter_upwards [hlim] with x hx
      simpa only [Function.comp_def, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using
        (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp hx.enorm
  have h := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hint
  simp only [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
  convert h using 1
  ext n
  simpa only [Function.comp_def, ENNReal.toReal_ofNat] using
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      ENNReal.ofNat_ne_top (hf n)

section Cutoff

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [NormedSpace ℝ F]

/-- Compact smooth spatial cutoffs approximate a Schwartz function and its full
Fréchet derivative in L². -/
theorem exists_compact_smooth_schwartz_cutoff_sequence (η : 𝓢(E, F)) :
    ∃ f : ℕ → E → F, (∀ n, HasCompactSupport (f n) ∧ ContDiff ℝ ∞ (f n)) ∧
      Tendsto (fun n => eLpNorm (fun x => f n x - η x) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm
        (fun x => fderiv ℝ (f n) x - fderiv ℝ η x) 2 volume) atTop (𝓝 0) := by
  let χ : ContDiffBump (0 : E) := default
  let s : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hspos (n : ℕ) : 0 < s n := inv_pos.mpr (by positivity)
  have hsle (n : ℕ) : s n ≤ 1 := by
    dsimp only [s]
    exact inv_le_one_of_one_le₀ (by linarith only [Nat.cast_nonneg (α := ℝ) n])
  have hs : Tendsto s atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  let c : ℕ → E → ℝ := fun n x => χ (s n • x)
  have hc (n : ℕ) : ContDiff ℝ ∞ (c n) :=
    χ.contDiff.comp (contDiff_id.const_smul (s n))
  have hcK (n : ℕ) : HasCompactSupport (c n) :=
    χ.hasCompactSupport.comp_smul (hspos n).ne'
  have hdc (n : ℕ) (x : E) :
      fderiv ℝ (c n) x = s n • fderiv ℝ χ (s n • x) := by
    have hh : HasFDerivAt (c n)
        ((fderiv ℝ χ (s n • x)).comp (s n • ContinuousLinearMap.id ℝ E)) x :=
      (((χ.contDiff : ContDiff ℝ ∞ (χ : E → ℝ)).differentiable (by simp)
        (s n • x)).hasFDerivAt).comp x
        ((hasFDerivAt_id x).const_smul (s n))
    rw [hh.fderiv]
    ext v
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul]
  obtain ⟨C, hC⟩ := ((χ.contDiff : ContDiff ℝ ∞ (χ : E → ℝ)).continuous_fderiv (by simp)).bounded_above_of_compact_support
    (χ.hasCompactSupport.fderiv ℝ)
  have hCpos : 0 ≤ C := (norm_nonneg (fderiv ℝ χ 0)).trans (hC 0)
  have hdc_bound (n : ℕ) (x : E) : ‖fderiv ℝ (c n) x‖ ≤ C := by
    rw [hdc, norm_smul, Real.norm_eq_abs, abs_of_pos (hspos n)]
    exact (mul_le_mul_of_nonneg_left (hC _) (hspos n).le).trans
      (mul_le_of_le_one_left hCpos (hsle n))
  have hc_bound (n : ℕ) (x : E) : ‖c n x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
    exact χ.le_one
  have hlocal (x : E) : ∀ᶠ n in atTop, c n =ᶠ[𝓝 x] (fun _ => 1) := by
    have hxs : Tendsto (fun n => s n • x) atTop (𝓝 (0 : E)) := by
      simpa only [zero_smul] using hs.smul_const x
    have hsmall : ∀ᶠ n in atTop, s n • x ∈ Metric.ball (0 : E) χ.rIn :=
      hxs.eventually (Metric.ball_mem_nhds _ χ.rIn_pos)
    filter_upwards [hsmall] with n hn
    exact (χ.eventuallyEq_one_of_mem_ball hn).comp_tendsto
      ((continuous_id.const_smul (s n)).tendsto x)
  let f : ℕ → E → F := fun n x => c n x • η x
  have hf (n : ℕ) : ContDiff ℝ ∞ (f n) := (hc n).smul (η.smooth ⊤)
  have hfK (n : ℕ) : HasCompactSupport (f n) := (hcK n).smul_right
  have hdf (n : ℕ) (x : E) : fderiv ℝ (f n) x =
      c n x • fderiv ℝ η x + (fderiv ℝ (c n) x).smulRight (η x) :=
    fderiv_smul ((hc n).differentiable (by simp) x) η.differentiableAt
  have hf_local (x : E) : ∀ᶠ n in atTop, f n =ᶠ[𝓝 x] (η : E → F) := by
    filter_upwards [hlocal x] with n hn
    filter_upwards [hn] with y hy
    simp only [f, hy, one_smul]
  refine ⟨f, fun n => ⟨hfK n, hf n⟩, ?_, ?_⟩
  · apply tendsto_eLpNorm_two_zero_of_dominated
      (fun n => ((hf n).continuous.sub η.continuous).aestronglyMeasurable)
      ((η.memLp 2 volume).norm.const_smul (2 : ℝ))
    · intro n
      apply ae_of_all
      intro x
      change ‖f n x - η x‖ ≤ ‖2 * ‖η x‖‖
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply (norm_sub_le _ _).trans
      have hfn : ‖f n x‖ ≤ ‖η x‖ := by
        rw [show f n x = c n x • η x from rfl, norm_smul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hc_bound n x)
      linarith only [hfn]
    · apply ae_of_all
      intro x
      apply Tendsto.congr' (f₁ := fun _ : ℕ => (0 : F)) ?_ tendsto_const_nhds
      filter_upwards [hf_local x] with n hn
      simp only [Pi.sub_apply, hn.eq_of_nhds, sub_self]
  · let b : E → ℝ := fun x => 2 * ‖fderiv ℝ η x‖ + C * ‖η x‖
    have hb : MemLp b 2 volume :=
      (((SchwartzMap.fderivCLM ℝ E F η).memLp 2 volume).norm.const_smul (2 : ℝ)).add
        ((η.memLp 2 volume).norm.const_smul C)
    apply tendsto_eLpNorm_two_zero_of_dominated
      (fun n => (((hf n).continuous_fderiv (by simp)).sub
        ((η.smooth ⊤).continuous_fderiv (by simp))).aestronglyMeasurable) hb
    · intro n
      apply ae_of_all
      intro x
      change ‖fderiv ℝ (f n) x - fderiv ℝ η x‖ ≤ ‖b x‖
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ b x from by dsimp only [b]; positivity)]
      apply (norm_sub_le _ _).trans
      rw [hdf]
      have hfn : ‖c n x • fderiv ℝ η x + (fderiv ℝ (c n) x).smulRight (η x)‖ ≤
          ‖fderiv ℝ η x‖ + C * ‖η x‖ := by
        apply (norm_add_le _ _).trans
        rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
        exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) (hc_bound n x))
          (mul_le_mul_of_nonneg_right (hdc_bound n x) (norm_nonneg _))
      dsimp only [b]
      linarith only [hfn]
    · apply ae_of_all
      intro x
      apply Tendsto.congr' (f₁ := fun _ : ℕ => (0 : E →L[ℝ] F)) ?_ tendsto_const_nhds
      filter_upwards [hf_local x] with n hn
      simp only [Pi.sub_apply, hn.fderiv_eq, sub_self]

/-- L² convergence of first derivatives implies convergence in every fixed direction. -/
theorem tendsto_eLpNorm_directional_of_fderiv {f : ℕ → E → F} {η : E → F}
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hη : ContDiff ℝ ∞ η)
    (ht : Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (f n) x - fderiv ℝ η x) 2 volume) atTop (𝓝 0)) (v : E) :
    Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (f n) x v - fderiv ℝ η x v) 2 volume) atTop (𝓝 0) := by
  have hm : Tendsto (fun n => ENNReal.ofReal ‖v‖ *
      eLpNorm (fun x => fderiv ℝ (f n) x - fderiv ℝ η x) 2 volume) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hm
      (fun _ => bot_le)
  intro n
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    ((((hf n).continuous_fderiv (by simp)).clm_apply continuous_const).sub
      ((hη.continuous_fderiv (by simp)).clm_apply continuous_const)).aestronglyMeasurable
  apply ae_of_all
  intro x
  simpa only [Pi.sub_apply, sub_apply, mul_comm] using
    (fderiv ℝ (f n) x - fderiv ℝ η x).le_opNorm v

/-- Compact smooth approximation of a Schwartz test together with each directional derivative. -/
theorem exists_compact_smooth_schwartz_test_approximation (η : 𝓢(E, F)) :
    ∃ f : ℕ → E → F, (∀ n, HasCompactSupport (f n) ∧ ContDiff ℝ ∞ (f n)) ∧
      Tendsto (fun n => eLpNorm (fun x => f n x - η x) 2 volume) atTop (𝓝 0) ∧
      ∀ v : E, Tendsto (fun n => eLpNorm
        (fun x => fderiv ℝ (f n) x v - fderiv ℝ η x v) 2 volume) atTop (𝓝 0) := by
  obtain ⟨f, hf, h₀, h₁⟩ := exists_compact_smooth_schwartz_cutoff_sequence η
  exact ⟨f, hf, h₀, fun v => tendsto_eLpNorm_directional_of_fderiv
    (fun n => (hf n).2) (η.smooth ⊤) h₁ v⟩

end Cutoff

end LiebThirring.Sobolev

end
