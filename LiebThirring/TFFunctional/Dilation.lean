/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThomasFermi.Mass
public import LiebThirring.ThomasFermi.DensityMeasure

/-! # Dilations of Thomas--Fermi densities -/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- The raw dilation `A ρ(βx)`. -/
@[expose] noncomputable def tfDensityDilationFn (β A : ℝ) (ρ : TFDensity) (x : Position) : ℝ :=
  A * ρ.val (β • x)

private theorem memLp_comp_pos_smul {p : ℝ≥0∞} (f : Position → ℝ)
    (hf : MemLp f p volume) {β : ℝ} (hβ : 0 < β) :
    MemLp (fun x : Position => f (β • x)) p volume := by
  have hm := Measure.map_addHaar_smul (volume : Measure Position) hβ.ne'
  have hc : ENNReal.ofReal |(β ^ Module.finrank ℝ Position)⁻¹| ≠ ∞ := ENNReal.ofReal_ne_top
  apply MemLp.comp_of_map
  · rw [hm]
    exact hf.smul_measure hc
  · exact measurable_const_smul β |>.aemeasurable

/-- Positive coordinate dilation and nonnegative amplitude preserve the TF carrier. -/
noncomputable def tfDensityDilation (β A : ℝ) (hβ : 0 < β) (hA : 0 ≤ A)
    (ρ : TFDensity) : TFDensity := by
  let f : Position → ℝ := tfDensityDilationFn β A ρ
  have hp : MemLp f ((5 : ℝ≥0∞) / 3) volume := by
    exact (memLp_comp_pos_smul (fun x => ρ.val x) (Lp.memLp ρ.val) hβ).const_mul A
  refine ⟨hp.toLp f, ?_, ?_⟩
  · filter_upwards [hp.coeFn_toLp,
      (Measure.quasiMeasurePreserving_smul (volume : Measure Position) hβ.ne').ae
        ρ.property.1] with x hx hρ
    rw [hx]
    exact mul_nonneg hA hρ
  · have h1 : MemLp f 1 volume :=
      (memLp_comp_pos_smul (fun x => ρ.val x)
        (memLp_one_iff_integrable.mpr ρ.property.2) hβ).const_mul A
    exact (memLp_one_iff_integrable.mp h1).congr hp.coeFn_toLp.symm

theorem tfDensityDilation_coe_ae (β A : ℝ) (hβ : 0 < β) (hA : 0 ≤ A)
    (ρ : TFDensity) :
    (tfDensityDilation β A hβ hA ρ).val =ᵐ[volume]
      tfDensityDilationFn β A ρ := by
  let f : Position → ℝ := tfDensityDilationFn β A ρ
  have hp : MemLp f ((5 : ℝ≥0∞) / 3) volume :=
    (memLp_comp_pos_smul (fun x => ρ.val x) (Lp.memLp ρ.val) hβ).const_mul A
  change hp.toLp f =ᵐ[volume] f
  exact hp.coeFn_toLp

theorem tfMass_tfDensityDilation (β A : ℝ) (hβ : 0 < β) (hA : 0 ≤ A)
    (ρ : TFDensity) :
    tfMass (tfDensityDilation β A hβ hA ρ) = A * (β ^ 3)⁻¹ * tfMass ρ := by
  unfold tfMass
  rw [integral_congr_ae (tfDensityDilation_coe_ae β A hβ hA ρ)]
  unfold tfDensityDilationFn
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg (volume : Measure Position)
      (fun x : Position => ρ.val x) β (hR := hβ.le)]
  simp only [Position, finrank_euclideanSpace_fin]
  ring

theorem tfDensityDilation_inv (β : ℝ) (hβ : 0 < β) (ρ : TFDensity) :
    tfDensityDilation β⁻¹ (β⁻¹ ^ 6) (inv_pos.mpr hβ)
        (pow_nonneg (inv_nonneg.mpr hβ.le) 6)
        (tfDensityDilation β (β ^ 6) hβ (pow_nonneg hβ.le 6) ρ) = ρ := by
  apply Subtype.ext
  apply MeasureTheory.Lp.ext
  have hi := tfDensityDilation_coe_ae β (β ^ 6) hβ (pow_nonneg hβ.le 6) ρ
  have hit := (Measure.quasiMeasurePreserving_smul (volume : Measure Position)
    (inv_ne_zero hβ.ne')).ae hi
  filter_upwards [tfDensityDilation_coe_ae β⁻¹ (β⁻¹ ^ 6) (inv_pos.mpr hβ)
    (pow_nonneg (inv_nonneg.mpr hβ.le) 6)
    (tfDensityDilation β (β ^ 6) hβ (pow_nonneg hβ.le 6) ρ), hit] with x hx hix
  rw [hx]
  simp only [tfDensityDilationFn, hix, smul_smul]
  field_simp [hβ.ne']
  simp

@[expose] noncomputable def tfDensityDilationEquiv (β : ℝ) (hβ : 0 < β) :
    TFDensity ≃ TFDensity where
  toFun := tfDensityDilation β (β ^ 6) hβ (pow_nonneg hβ.le 6)
  invFun := tfDensityDilation β⁻¹ (β⁻¹ ^ 6) (inv_pos.mpr hβ)
    (pow_nonneg (inv_nonneg.mpr hβ.le) 6)
  left_inv := tfDensityDilation_inv β hβ
  right_inv ρ := by
    simpa only [inv_inv] using tfDensityDilation_inv β⁻¹ (inv_pos.mpr hβ) ρ

theorem tfMass_tfDensityDilationEquiv (β : ℝ) (hβ : 0 < β) (ρ : TFDensity) :
    tfMass (tfDensityDilationEquiv β hβ ρ) = β ^ 3 * tfMass ρ := by
  change tfMass (tfDensityDilation β (β ^ 6) hβ (pow_nonneg hβ.le 6) ρ) = _
  rw [tfMass_tfDensityDilation]
  field_simp [hβ.ne']

@[expose] noncomputable def tfDensityDilationMassEquiv (β : ℝ) (hβ : 0 < β) (m : ℝ) :
    {ρ : TFDensity // tfMass ρ = m} ≃
      {ρ : TFDensity // tfMass ρ = β ^ 3 * m} :=
  Equiv.subtypeEquiv (tfDensityDilationEquiv β hβ) fun ρ => by
    rw [tfMass_tfDensityDilationEquiv]
    constructor
    · exact fun h => congrArg (β ^ 3 * ·) h
    · intro h
      exact (mul_left_cancel₀ (pow_ne_zero 3 hβ.ne') h)

end LiebThirring

end
