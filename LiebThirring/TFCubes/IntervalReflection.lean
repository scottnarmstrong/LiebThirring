/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CircleParity
public import LiebThirring.TFCubes.RegionL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic

/-!
# Literal reflection of interval L² functions

Extend by zero from `(0, ℓ)`, reflect across zero, and lift
from `(-ℓ, ℓ]` to the circle of period `2ℓ`. Multiplication by `√ℓ` converts
physical Lebesgue L² normalization into the circle's probability Haar
normalization. The Boolean parameter selects odd (`true`) or even (`false`)
reflection. No Sobolev assertion is made in this module.
-/

@[expose] public section

open MeasureTheory Set AddCircle
open scoped ENNReal

namespace LiebThirring.TFCubes

instance intervalDoublePeriod_pos (ℓ : {ℓ : ℝ // 0 < ℓ}) : Fact (0 < 2 * ℓ.val) :=
  ⟨mul_pos zero_lt_two ℓ.property⟩

/-- The sign on the reflected half of the interval. -/
def intervalReflectionSign (odd : Bool) : ℂ := if odd then -1 else 1

theorem norm_intervalReflectionSign (odd : Bool) : ‖intervalReflectionSign odd‖ = 1 := by
  cases odd <;> simp [intervalReflectionSign]

/-- Unscaled odd/even reflection, with zero endpoint values. -/
noncomputable def intervalReflectionReal (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Ioo 0 ℓ.val).indicator u x +
    intervalReflectionSign odd * (Ioo 0 ℓ.val).indicator u (-x)

/-- Literal `√ℓ`-scaled reflection on the doubled circle. -/
noncomputable def intervalReflectionCircle (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) (u : ℝ → ℂ) : AddCircle (2 * ℓ.val) → ℂ :=
  AddCircle.liftIoc (2 * ℓ.val) (-ℓ.val)
    (fun x ↦ (Real.sqrt ℓ.val : ℂ) * intervalReflectionReal ℓ odd u x)

theorem intervalReflectionReal_pos (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) (u : ℝ → ℂ) {x : ℝ} (hx : x ∈ Ioo 0 ℓ.val) :
    intervalReflectionReal ℓ odd u x = u x := by
  rw [intervalReflectionReal, indicator_of_mem hx,
    indicator_of_notMem (by intro hn; linarith only [hx.1, hn.1])]
  simp only [mul_zero, add_zero]

theorem intervalReflectionReal_neg (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) (u : ℝ → ℂ) (x : ℝ) :
    intervalReflectionReal ℓ odd u (-x) =
      intervalReflectionSign odd * intervalReflectionReal ℓ odd u x := by
  cases odd <;> simp [intervalReflectionReal, intervalReflectionSign, add_comm]

theorem intervalReflectionReal_eq_zero_off (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) (u : ℝ → ℂ) {x : ℝ} (hx : x ∉ Ioo (-ℓ.val) ℓ.val) :
    intervalReflectionReal ℓ odd u x = 0 := by
  have hp : x ∉ Ioo 0 ℓ.val := by
    intro hp
    exact hx ⟨lt_trans (neg_neg_of_pos ℓ.property) hp.1, hp.2⟩
  have hn : -x ∉ Ioo 0 ℓ.val := by
    intro hn
    apply hx
    constructor <;> linarith only [hn.1, hn.2, ℓ.property]
  simp only [intervalReflectionReal, indicator_of_notMem hp, indicator_of_notMem hn,
    mul_zero, add_zero]

theorem norm_intervalReflectionReal_sq (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) (u : ℝ → ℂ) (x : ℝ) :
    ‖intervalReflectionReal ℓ odd u x‖ ^ 2 =
      (Ioo 0 ℓ.val).indicator (fun y ↦ ‖u y‖ ^ 2) x +
      (Ioo 0 ℓ.val).indicator (fun y ↦ ‖u y‖ ^ 2) (-x) := by
  by_cases hp : x ∈ Ioo 0 ℓ.val
  · have hn : -x ∉ Ioo 0 ℓ.val := by
      intro hn; linarith only [hp.1, hn.1]
    rw [intervalReflectionReal_pos ℓ odd u hp, indicator_of_mem hp,
      indicator_of_notMem hn, add_zero]
  · rw [intervalReflectionReal, indicator_of_notMem hp, zero_add,
      norm_mul, norm_intervalReflectionSign, one_mul]
    by_cases hn : -x ∈ Ioo 0 ℓ.val
    · rw [indicator_of_mem hn, indicator_of_notMem hp, indicator_of_mem hn, zero_add]
    · simp only [indicator_of_notMem hn, indicator_of_notMem hp, norm_zero,
        zero_pow (by decide : 2 ≠ 0), add_zero]

theorem memLp_intervalReflectionReal (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) {u : ℝ → ℂ} (hu : MemLp u 2 (volume.restrict (Ioo 0 ℓ.val))) :
    MemLp (intervalReflectionReal ℓ odd u) 2 volume := by
  have hz := (memLp_indicator_iff_restrict measurableSet_Ioo).mpr hu
  exact hz.add ((hz.comp_measurePreserving (Measure.measurePreserving_neg volume)).const_mul _)

theorem integral_norm_intervalReflectionReal_sq (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) {u : ℝ → ℂ} (hu : MemLp u 2 (volume.restrict (Ioo 0 ℓ.val))) :
    (∫ x, ‖intervalReflectionReal ℓ odd u x‖ ^ 2) =
      2 * ∫ x in Ioo 0 ℓ.val, ‖u x‖ ^ 2 := by
  have hi : Integrable ((Ioo 0 ℓ.val).indicator (fun x ↦ ‖u x‖ ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr
      ((memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu)
  simp_rw [norm_intervalReflectionReal_sq]
  have hn : Integrable (fun x ↦ (Ioo 0 ℓ.val).indicator (fun y ↦ ‖u y‖ ^ 2) (-x)) :=
    (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hi
  rw [integral_add hi hn,
    integral_neg_eq_self, integral_indicator measurableSet_Ioo, two_mul]

theorem memLp_intervalReflectionCircle (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) {u : ℝ → ℂ} (hu : MemLp u 2 (volume.restrict (Ioo 0 ℓ.val))) :
    MemLp (intervalReflectionCircle ℓ odd u) 2 haarAddCircle :=
  (((memLp_intervalReflectionReal ℓ odd hu).const_mul (Real.sqrt ℓ.val : ℂ)).restrict
    (Ioc (-ℓ.val) (-ℓ.val + 2 * ℓ.val))).memLp_liftIoc.haarAddCircle

/-- Exact transport of physical squared norm to probability Haar measure. -/
theorem integral_norm_intervalReflectionCircle_sq (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) {u : ℝ → ℂ} (hu : MemLp u 2 (volume.restrict (Ioo 0 ℓ.val))) :
    (∫ x : AddCircle (2 * ℓ.val), ‖intervalReflectionCircle ℓ odd u x‖ ^ 2
      ∂haarAddCircle) = ∫ x in Ioo 0 ℓ.val, ‖u x‖ ^ 2 := by
  change (∫ x : AddCircle (2 * ℓ.val),
    liftIoc (2 * ℓ.val) (-ℓ.val)
      (fun y ↦ ‖(Real.sqrt ℓ.val : ℂ) * intervalReflectionReal ℓ odd u y‖ ^ 2) x
      ∂haarAddCircle) = _
  rw [integral_haarAddCircle, integral_liftIoc_eq_intervalIntegral]
  have hend : -ℓ.val + 2 * ℓ.val = ℓ.val := by ring
  rw [hend]
  simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt ℓ.property.le]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le (by linarith only [ℓ.property])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
    rw [intervalReflectionReal_eq_zero_off ℓ odd u (fun hi ↦ hx ⟨hi.1, hi.2.le⟩),
      norm_zero, zero_pow (by decide : 2 ≠ 0)]),
    integral_norm_intervalReflectionReal_sq ℓ odd hu]
  simp only [smul_eq_mul]
  field_simp [ℓ.property.ne']

/-- The literal reflected circle L² function. -/
noncomputable def intervalReflectionL2 (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) (u : Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))) :
    Lp ℂ 2 (haarAddCircle (T := 2 * ℓ.val)) :=
  (memLp_intervalReflectionCircle ℓ odd (Lp.memLp u)).toLp
    (intervalReflectionCircle ℓ odd u)

theorem intervalReflectionL2_ae (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) (u : Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))) :
    intervalReflectionL2 ℓ odd u =ᵐ[haarAddCircle] intervalReflectionCircle ℓ odd u :=
  (memLp_intervalReflectionCircle ℓ odd (Lp.memLp u)).coeFn_toLp

theorem norm_complexL2_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : Lp ℂ 2 μ) : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re (L2.integrable_inner u u)]
  simp only [← norm_sq_eq_re_inner]

theorem norm_intervalReflectionL2 (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) (u : Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))) :
    ‖intervalReflectionL2 ℓ odd u‖ = ‖u‖ := by
  have hi : ‖intervalReflectionL2 ℓ odd u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [norm_complexL2_sq, norm_complexL2_sq]
    calc
      _ = ∫ x : AddCircle (2 * ℓ.val), ‖intervalReflectionCircle ℓ odd u x‖ ^ 2
          ∂haarAddCircle := integral_congr_ae
            ((intervalReflectionL2_ae ℓ odd u).mono (fun x hx ↦ by rw [hx]))
      _ = _ := integral_norm_intervalReflectionCircle_sq ℓ odd (Lp.memLp u)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hi

theorem intervalReflectionCircle_coe (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) (u : ℝ → ℂ) {x : ℝ} (hx : x ∈ Ioc (-ℓ.val) ℓ.val) :
    intervalReflectionCircle ℓ odd u x =
      (Real.sqrt ℓ.val : ℂ) * intervalReflectionReal ℓ odd u x := by
  apply liftIoc_coe_apply
  exact ⟨hx.1, by linarith only [hx.2]⟩

/-- The endpoint convention is compatible with both circle parities. -/
theorem intervalReflectionCircle_neg (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) (u : ℝ → ℂ) (x : AddCircle (2 * ℓ.val)) :
    intervalReflectionCircle ℓ odd u (-x) =
      intervalReflectionSign odd * intervalReflectionCircle ℓ odd u x := by
  let y : ℝ := (equivIoc (2 * ℓ.val) (-ℓ.val) x).val
  have hy : y ∈ Ioc (-ℓ.val) ℓ.val := by
    have h := (equivIoc (2 * ℓ.val) (-ℓ.val) x).property
    change -ℓ.val < y ∧ y ≤ -ℓ.val + 2 * ℓ.val at h
    constructor
    · exact h.1
    · linarith only [h.2]
  have hxy : (y : AddCircle (2 * ℓ.val)) = x := coe_equivIoc
  rw [← hxy, ← coe_neg]
  change intervalReflectionCircle ℓ odd u ((-y : ℝ) : AddCircle (2 * ℓ.val)) =
    intervalReflectionSign odd * intervalReflectionCircle ℓ odd u (y : AddCircle (2 * ℓ.val))
  by_cases he : y = ℓ.val
  · rw [he] at hy ⊢
    have hends : ((-ℓ.val : ℝ) : AddCircle (2 * ℓ.val)) =
        ((ℓ.val : ℝ) : AddCircle (2 * ℓ.val)) := by
      have h := coe_add_period (2 * ℓ.val) (-ℓ.val)
      have heq : -ℓ.val + 2 * ℓ.val = ℓ.val := by ring
      rw [heq] at h
      exact h.symm
    rw [hends, intervalReflectionCircle_coe ℓ odd u hy,
      intervalReflectionReal_eq_zero_off ℓ odd u (by simp only [mem_Ioo]; exact fun h ↦ h.2.false)]
    simp only [mul_zero]
  · have hlt : y < ℓ.val := lt_of_le_of_ne hy.2 he
    have hny : -y ∈ Ioc (-ℓ.val) ℓ.val := by
      constructor <;> linarith only [hy.1, hlt]
    rw [intervalReflectionCircle_coe ℓ odd u hy,
      intervalReflectionCircle_coe ℓ odd u hny, intervalReflectionReal_neg]
    ring

/-- Reflection respects local almost-everywhere equality. -/
theorem intervalReflectionCircle_congr_ae (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) {u v : ℝ → ℂ} (huv : u =ᵐ[volume.restrict (Ioo 0 ℓ.val)] v) :
    intervalReflectionCircle ℓ odd u =ᵐ[haarAddCircle] intervalReflectionCircle ℓ odd v := by
  have hz := (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Ioo).mp huv
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp hz
  have hr : intervalReflectionReal ℓ odd u =ᵐ[volume] intervalReflectionReal ℓ odd v := by
    filter_upwards [hz, hn] with x hp hm
    dsimp only [Function.comp_def] at hm
    change (Ioo 0 ℓ.val).indicator u x +
      intervalReflectionSign odd * (Ioo 0 ℓ.val).indicator u (-x) =
      (Ioo 0 ℓ.val).indicator v x + intervalReflectionSign odd * (Ioo 0 ℓ.val).indicator v (-x)
    rw [hp, hm]
  have hs : (fun x ↦ (Real.sqrt ℓ.val : ℂ) * intervalReflectionReal ℓ odd u x)
      =ᵐ[volume.restrict (Ioc (-ℓ.val) (-ℓ.val + 2 * ℓ.val))]
      (fun x ↦ (Real.sqrt ℓ.val : ℂ) * intervalReflectionReal ℓ odd v x) :=
    (hr.mono (fun _ hx ↦ congrArg (fun z : ℂ ↦ (Real.sqrt ℓ.val : ℂ) * z) hx)).filter_mono
      (ae_mono Measure.restrict_le_self)
  have hmp := (measurePreserving_subtype_coe
    (measurableSet_Ioc (a := -ℓ.val) (b := -ℓ.val + 2 * ℓ.val))).comp
      (measurePreserving_equivIoc (2 * ℓ.val) (a := -ℓ.val))
  have hc := hmp.quasiMeasurePreserving.ae_eq_comp hs
  change intervalReflectionCircle ℓ odd u =ᵐ[volume] intervalReflectionCircle ℓ odd v at hc
  rw [volume_eq_smul_haarAddCircle] at hc
  exact (Measure.ae_ennreal_smul_measure_iff
    (ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos zero_lt_two ℓ.property)))).mp hc

theorem intervalReflectionCircle_add (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) (u v : ℝ → ℂ) (x : AddCircle (2 * ℓ.val)) :
    intervalReflectionCircle ℓ odd (u + v) x =
      intervalReflectionCircle ℓ odd u x + intervalReflectionCircle ℓ odd v x := by
  have hi : (Ioo 0 ℓ.val).indicator (u + v) =
      (Ioo 0 ℓ.val).indicator u + (Ioo 0 ℓ.val).indicator v :=
    indicator_add (Ioo 0 ℓ.val) u v
  simp only [intervalReflectionCircle, liftIoc, domRestrict_def, Function.comp_def,
    intervalReflectionReal, hi, Pi.add_apply]
  ring

theorem intervalReflectionCircle_smul (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) (c : ℂ) (u : ℝ → ℂ) (x : AddCircle (2 * ℓ.val)) :
    intervalReflectionCircle ℓ odd (c • u) x = c * intervalReflectionCircle ℓ odd u x := by
  have hi : (Ioo 0 ℓ.val).indicator (c • u) = c • (Ioo 0 ℓ.val).indicator u :=
    indicator_smul (Ioo 0 ℓ.val) (fun _ ↦ c) u
  simp only [intervalReflectionCircle, liftIoc, domRestrict_def, Function.comp_def,
    intervalReflectionReal, hi, Pi.smul_apply, smul_eq_mul]
  ring

/-- The literal reflection is a complex linear isometry. -/
noncomputable def intervalReflectionLI (ℓ : {ℓ : ℝ // 0 < ℓ}) (odd : Bool) :
    Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val)) →ₗᵢ[ℂ]
      Lp ℂ 2 (haarAddCircle (T := 2 * ℓ.val)) where
  toFun := intervalReflectionL2 ℓ odd
  map_add' u v := by
    apply Lp.ext
    have hsum := intervalReflectionCircle_congr_ae ℓ odd (Lp.coeFn_add u v)
    filter_upwards [intervalReflectionL2_ae ℓ odd (u + v), hsum,
      intervalReflectionL2_ae ℓ odd u, intervalReflectionL2_ae ℓ odd v,
      Lp.coeFn_add (intervalReflectionL2 ℓ odd u) (intervalReflectionL2 ℓ odd v)]
      with x hl hs hu hv ha
    simp only [Pi.add_apply] at ha
    rw [hl, hs, intervalReflectionCircle_add, ha, hu, hv]
  map_smul' c u := by
    apply Lp.ext
    have hsmul := intervalReflectionCircle_congr_ae ℓ odd (Lp.coeFn_smul c u)
    filter_upwards [intervalReflectionL2_ae ℓ odd (c • u), hsmul,
      intervalReflectionL2_ae ℓ odd u, Lp.coeFn_smul c (intervalReflectionL2 ℓ odd u)]
      with x hl hs hu ha
    simp only [Pi.smul_apply, smul_eq_mul] at ha
    change intervalReflectionL2 ℓ odd (c • u) x = (c • intervalReflectionL2 ℓ odd u) x
    rw [hl, hs, intervalReflectionCircle_smul, ha, hu]
  norm_map' := norm_intervalReflectionL2 ℓ odd

@[simp] theorem intervalReflectionLI_apply (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) (u : Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))) :
    intervalReflectionLI ℓ odd u = intervalReflectionL2 ℓ odd u := rfl

theorem intervalReflectionL2_parity (ℓ : {ℓ : ℝ // 0 < ℓ})
    (odd : Bool) (u : Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))) :
    (fun x ↦ intervalReflectionL2 ℓ odd u (-x)) =ᵐ[haarAddCircle]
      (fun x ↦ intervalReflectionSign odd * intervalReflectionL2 ℓ odd u x) := by
  have hn := (Measure.measurePreserving_neg
    (haarAddCircle (T := 2 * ℓ.val))).quasiMeasurePreserving.ae_eq_comp
      (intervalReflectionL2_ae ℓ odd u)
  filter_upwards [hn, intervalReflectionL2_ae ℓ odd u] with x hm hp
  dsimp only [Function.comp_def] at hm
  rw [hm, hp, intervalReflectionCircle_neg]

theorem intervalReflectionL2_even (ℓ : {ℓ : ℝ // 0 < ℓ})
    (u : Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))) :
    (fun x ↦ intervalReflectionL2 ℓ false u (-x)) =ᵐ[haarAddCircle]
      intervalReflectionL2 ℓ false u := by
  simpa only [intervalReflectionSign, Bool.false_eq_true, ite_false, one_mul]
    using intervalReflectionL2_parity ℓ false u

theorem intervalReflectionL2_odd (ℓ : {ℓ : ℝ // 0 < ℓ})
    (u : Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))) :
    (fun x ↦ intervalReflectionL2 ℓ true u (-x)) =ᵐ[haarAddCircle]
      (fun x ↦ -intervalReflectionL2 ℓ true u x) := by
  simpa only [intervalReflectionSign, ite_true, neg_one_mul]
    using intervalReflectionL2_parity ℓ true u

end LiebThirring.TFCubes

end
