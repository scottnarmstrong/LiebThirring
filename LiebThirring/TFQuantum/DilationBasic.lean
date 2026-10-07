/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.Kinetic.CurryingProductBasic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
/-! # Normalized dilation of finite-dimensional L² states

The spatial pullback is compensated by the square root of its inverse
Jacobian. The construction is a genuine complex linear isometry equivalence
and gives weighted change of variables on every L² state, including zero
spatial dimension. Proof: large-charge dilation, direct proof calculation.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.Dilation
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

@[expose] noncomputable def amplitude (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (r : ℝ) : ℝ :=
  Real.sqrt (r ^ Module.finrank ℝ V)

omit [MeasurableSpace V] [BorelSpace V] in
theorem amplitude_nonneg (r : ℝ) : 0 ≤ amplitude V r := Real.sqrt_nonneg _

omit [MeasurableSpace V] [BorelSpace V] in
theorem amplitude_sq (r : ℝ) (hr : 0 < r) : (amplitude V r)^2 = r^Module.finrank ℝ V :=
  Real.sq_sqrt (pow_nonneg hr.le _)

theorem lintegral_comp_smul (r : ℝ) (hr : 0 < r) (g : V → ℝ≥0∞) :
    (∫⁻ x, g (r • x)) = (ENNReal.ofReal (r^Module.finrank ℝ V))⁻¹ * ∫⁻ x, g x := by
  have h := (Homeomorph.smulOfNeZero r hr.ne' : V ≃ₜ V).measurableEmbedding.lintegral_map
    (μ := (volume : Measure V)) g
  change (∫⁻ x, g x ∂Measure.map (fun x : V => r • x) volume) = (∫⁻ x, g (r • x)) at h
  rw [← h]
  rw [Measure.map_addHaar_smul volume hr.ne', lintegral_smul_measure]
  rw [abs_of_pos (inv_pos.mpr (pow_pos hr _)), ENNReal.ofReal_inv_of_pos (pow_pos hr _)]
  rfl

omit [NormedSpace ℂ H] in
theorem memLp_comp_smul (r : ℝ) (hr : 0 < r) (ψ : Lp H 2 (volume : Measure V)) :
    MemLp (fun x => ψ (r • x)) 2 volume := by
  apply MemLp.comp_of_map ?_ (measurable_const_smul r).aemeasurable
  rw [Measure.map_addHaar_smul volume hr.ne']
  exact (Lp.memLp ψ).smul_measure ENNReal.ofReal_ne_top

@[expose] noncomputable def applyL2 (r : ℝ) (hr : 0 < r)
    (ψ : Lp H 2 (volume : Measure V)) : Lp H 2 (volume : Measure V) :=
  (((memLp_comp_smul r hr ψ).const_smul ((amplitude V r : ℝ) : ℂ))).toLp
    (fun x => ((amplitude V r : ℝ) : ℂ) • ψ (r • x))

theorem coeFn_applyL2 (r : ℝ) (hr : 0 < r) (ψ : Lp H 2 (volume : Measure V)) :
    applyL2 r hr ψ =ᵐ[volume] fun x => (amplitude V r : ℂ) • ψ (r • x) :=
  MemLp.coeFn_toLp _

theorem lintegral_applyL2_enorm_sq (r : ℝ) (hr : 0 < r)
    (ψ : Lp H 2 (volume : Measure V)) :
    (∫⁻ x, ‖applyL2 r hr ψ x‖ₑ^2) = ∫⁻ x, ‖ψ x‖ₑ^2 := by
  calc
    _ = ∫⁻ x, ENNReal.ofReal (r^Module.finrank ℝ V) * ‖ψ (r • x)‖ₑ^2 := by
      apply lintegral_congr_ae
      filter_upwards [coeFn_applyL2 r hr ψ] with x hx
      rw [hx, enorm_smul, mul_pow]
      congr 1
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (amplitude_nonneg (V := V) r),
        ← ENNReal.ofReal_pow (amplitude_nonneg (V := V) r), amplitude_sq r hr]
    _ = ENNReal.ofReal (r^Module.finrank ℝ V) *
        ((ENNReal.ofReal (r^Module.finrank ℝ V))⁻¹ * ∫⁻ x, ‖ψ x‖ₑ^2) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_comp_smul r hr (fun x : V => ‖ψ x‖ₑ^2)]
    _ = _ := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel
        (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne' ENNReal.ofReal_ne_top, one_mul]

theorem norm_applyL2 (r : ℝ) (hr : 0 < r) (ψ : Lp H 2 (volume : Measure V)) :
    ‖applyL2 r hr ψ‖ = ‖ψ‖ := by
  have he := lintegral_applyL2_enorm_sq r hr ψ
  rw [lintegral_l2_enorm_sq, lintegral_l2_enorm_sq] at he
  have h := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_pow, enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

@[expose] noncomputable def linearIsometry (r : ℝ) (hr : 0 < r) :
    Lp H 2 (volume : Measure V) →ₗᵢ[ℂ] Lp H 2 (volume : Measure V) where
  toFun := applyL2 r hr
  map_add' ψ φ := by
    apply Lp.ext
    filter_upwards [coeFn_applyL2 r hr (ψ+φ), coeFn_applyL2 r hr ψ,
      coeFn_applyL2 r hr φ, Lp.coeFn_add (applyL2 r hr ψ) (applyL2 r hr φ),
      (Measure.quasiMeasurePreserving_smul volume hr.ne').ae (Lp.coeFn_add ψ φ)]
      with x hx hψ hφ ha hsum
    simp only [hx, ha, Pi.add_apply, hψ, hφ, hsum, smul_add]
  map_smul' c ψ := by
    change applyL2 r hr (c • ψ) = c • applyL2 r hr ψ
    apply Lp.ext
    filter_upwards [coeFn_applyL2 r hr (c • ψ), coeFn_applyL2 r hr ψ,
      Lp.coeFn_smul c (applyL2 r hr ψ),
      (Measure.quasiMeasurePreserving_smul volume hr.ne').ae (Lp.coeFn_smul c ψ)]
      with x hx hψ hc hs
    simp only [hx, hc, Pi.smul_apply, hψ, hs]
    exact smul_comm _ _ _
  norm_map' := norm_applyL2 r hr

omit [MeasurableSpace V] [BorelSpace V] in
theorem amplitude_pos (r : ℝ) (hr : 0 < r) : 0 < amplitude V r :=
  Real.sqrt_pos.mpr (pow_pos hr _)

omit [MeasurableSpace V] [BorelSpace V] in
theorem amplitude_inv (r : ℝ) : amplitude V r⁻¹ = (amplitude V r)⁻¹ := by
  simp only [amplitude, inv_pow, Real.sqrt_inv]

theorem applyL2_inv_applyL2 (r : ℝ) (hr : 0 < r)
    (ψ : Lp H 2 (volume : Measure V)) :
    applyL2 r⁻¹ (inv_pos.mpr hr) (applyL2 r hr ψ) = ψ := by
  apply Lp.ext
  filter_upwards [coeFn_applyL2 r⁻¹ (inv_pos.mpr hr) (applyL2 r hr ψ),
    (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hr.ne')).ae
      (coeFn_applyL2 r hr ψ)] with x hx hy
  rw [hx, hy]
  simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, amplitude_inv,
    Complex.ofReal_inv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
      (amplitude_pos (V := V) r hr).ne')]

@[expose] noncomputable def linearIsometryEquiv (r : ℝ) (hr : 0 < r) :
    Lp H 2 (volume : Measure V) ≃ₗᵢ[ℂ] Lp H 2 (volume : Measure V) :=
  LinearIsometryEquiv.ofSurjective (linearIsometry r hr) (fun ψ =>
    ⟨applyL2 r⁻¹ (inv_pos.mpr hr) ψ, by
      change applyL2 r hr (applyL2 r⁻¹ (inv_pos.mpr hr) ψ) = ψ
      simpa only [inv_inv] using applyL2_inv_applyL2 r⁻¹ (inv_pos.mpr hr) ψ⟩)

theorem lintegral_weight_applyL2 (r : ℝ) (hr : 0 < r)
    (ψ : Lp H 2 (volume : Measure V)) (w : V → ℝ≥0∞) :
    (∫⁻ x, w x * ‖applyL2 r hr ψ x‖ₑ^2) =
      ∫⁻ x, w (r⁻¹ • x) * ‖ψ x‖ₑ^2 := by
  let g : V → ℝ≥0∞ := fun x => w (r⁻¹ • x) * ‖ψ x‖ₑ^2
  calc
    _ = ∫⁻ x, ENNReal.ofReal (r^Module.finrank ℝ V) * g (r • x) := by
      apply lintegral_congr_ae
      filter_upwards [coeFn_applyL2 r hr ψ] with x hx
      simp only [hx, g, smul_smul, inv_mul_cancel₀ hr.ne', one_smul,
        enorm_smul, mul_pow]
      have ha : ‖(amplitude V r : ℂ)‖ₑ^2 =
          ENNReal.ofReal (r^Module.finrank ℝ V) := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (amplitude_nonneg (V := V) r),
          ← ENNReal.ofReal_pow (amplitude_nonneg (V := V) r), amplitude_sq r hr]
      rw [ha]
      ring
    _ = ENNReal.ofReal (r^Module.finrank ℝ V) *
        ((ENNReal.ofReal (r^Module.finrank ℝ V))⁻¹ * ∫⁻ x, g x) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_comp_smul r hr g]
    _ = _ := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel
        (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne' ENNReal.ofReal_ne_top, one_mul]

end LiebThirring.Dilation
end
