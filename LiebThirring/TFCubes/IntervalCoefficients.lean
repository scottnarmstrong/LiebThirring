/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.IntervalModesL2
public import LiebThirring.TFCubes.IntervalReflection
import Mathlib.Tactic

/-!
# Fourier coefficients of literal interval reflection

Interval L² group: the physical sine/cosine coefficients are
identified with the positive circle Fourier coefficients of the literal
`√ℓ`-scaled reflection. The proof reflects individual literal modes and
uses the already proved reflection isometry and circle parity. All mode
transport identities are almost-everywhere identities, including the cosine
endpoint convention. No completeness or quadratic-form hypothesis is assumed.
-/

@[expose] public section

open MeasureTheory Set AddCircle
open scoped ComplexConjugate InnerProductSpace

namespace LiebThirring.TFCubes

theorem circle_ae_of_interval_coe_ae (ℓ : {ℓ : ℝ // 0 < ℓ})
    {f g : AddCircle (2 * ℓ.val) → ℂ}
    (h : (fun x : ℝ => f x) =ᵐ[volume.restrict (Ioc (-ℓ.val) (-ℓ.val + 2 * ℓ.val))]
      (fun x : ℝ => g x)) : f =ᵐ[haarAddCircle] g := by
  have hmp := (measurePreserving_subtype_coe
    (measurableSet_Ioc (a := -ℓ.val) (b := -ℓ.val + 2 * ℓ.val))).comp
      (measurePreserving_equivIoc (2 * ℓ.val) (a := -ℓ.val))
  have hc := hmp.quasiMeasurePreserving.ae_eq_comp h
  have hcv : f =ᵐ[volume] g := by
    filter_upwards [hc] with x hx
    change f (((equivIoc (2 * ℓ.val) (-ℓ.val) x).val : ℝ) : AddCircle (2 * ℓ.val)) =
      g (((equivIoc (2 * ℓ.val) (-ℓ.val) x).val : ℝ) : AddCircle (2 * ℓ.val)) at hx
    simpa only [coe_equivIoc] using hx
  rw [volume_eq_smul_haarAddCircle] at hcv
  exact (Measure.ae_ennreal_smul_measure_iff
    (ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos zero_lt_two ℓ.property)))).mp hcv
theorem fourier_doublePeriod_coe_nat (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) (x : ℝ) :
    fourier (T := 2 * ℓ.val) (n : ℤ) (x : AddCircle (2 * ℓ.val)) =
      (Real.cos (intervalFrequency ℓ n * x) : ℂ) +
        (Real.sin (intervalFrequency ℓ n * x) : ℂ) * Complex.I := by
  rw [fourier_coe_apply]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  have harg : (2 * Real.pi * Complex.I * (n : ℤ) * x / (2 * ℓ.val) : ℂ) =
      ((intervalFrequency ℓ n * x : ℝ) : ℂ) * Complex.I := by
    simp only [intervalFrequency, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_natCast, Int.cast_natCast]
    ring
  simp only [Int.cast_natCast] at harg ⊢
  rw [harg, Complex.exp_ofReal_mul_I]
theorem sqrt_length_mul_intervalAmplitude (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    Real.sqrt ℓ.val * Real.sqrt (2 / ℓ.val) = Real.sqrt 2 := by
  rw [← Real.sqrt_mul ℓ.property.le]
  congr 1
  field_simp [ℓ.property.ne']
theorem fourier_sum_coe_nat (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) (x : ℝ) :
    (Real.sqrt 2 : ℂ) * (Real.cos (intervalFrequency ℓ n * x) : ℂ) =
      ((Real.sqrt 2 : ℂ) / 2) *
        (fourier (T := 2 * ℓ.val) (n : ℤ) (x : AddCircle (2 * ℓ.val)) +
          fourier (T := 2 * ℓ.val) (- (n : ℤ)) (x : AddCircle (2 * ℓ.val))) := by
  rw [fourier_neg, fourier_doublePeriod_coe_nat]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring
theorem fourier_sub_coe_nat (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ) (x : ℝ) :
    (Real.sqrt 2 : ℂ) * (Real.sin (intervalFrequency ℓ n * x) : ℂ) =
      (-Complex.I * ((Real.sqrt 2 : ℂ) / 2)) *
        (fourier (T := 2 * ℓ.val) (n : ℤ) (x : AddCircle (2 * ℓ.val)) -
          fourier (T := 2 * ℓ.val) (- (n : ℤ)) (x : AddCircle (2 * ℓ.val))) := by
  rw [fourier_neg, fourier_doublePeriod_coe_nat]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination ((Real.sqrt 2 : ℂ) * (Real.sin (intervalFrequency ℓ n * x) : ℂ)) * Complex.I_sq

/-- Away from the midpoint and endpoints, reflection agrees with a parity-compatible function. -/
theorem intervalReflectionReal_eq_of_parity (ℓ : {ℓ : ℝ // 0 < ℓ}) (odd : Bool)
    {f : ℝ → ℂ} (hpar : ∀ x, f (-x) = intervalReflectionSign odd * f x)
    {x : ℝ} (hx : x ∈ Ioo (-ℓ.val) ℓ.val) (hzero : x ≠ 0) :
    intervalReflectionReal ℓ odd f x = f x := by
  by_cases hp : 0 < x
  · exact intervalReflectionReal_pos ℓ odd f ⟨hp, hx.2⟩
  · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hzero
    have hn : -x ∈ Ioo 0 ℓ.val :=
      ⟨neg_pos.mpr hxneg, by linarith only [hx.1]⟩
    have hnot : x ∉ Ioo 0 ℓ.val := fun h => hp h.1
    rw [intervalReflectionReal, indicator_of_notMem hnot, indicator_of_mem hn,
      zero_add, hpar x]
    cases odd <;> simp [intervalReflectionSign]

theorem intervalReflectionCircle_dirichletIntervalMode (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) :
    intervalReflectionCircle ℓ true (fun x => (dirichletIntervalMode ℓ n x : ℂ))
      =ᵐ[haarAddCircle]
      (fun x => (-Complex.I * ((Real.sqrt 2 : ℂ) / 2)) *
        (fourier (n : ℤ) x - fourier (- (n : ℤ)) x)) := by
  apply circle_ae_of_interval_coe_ae ℓ
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    (volume.restrict (Ioc (-ℓ.val) (-ℓ.val + 2 * ℓ.val))).ae_ne 0,
    (volume.restrict (Ioc (-ℓ.val) (-ℓ.val + 2 * ℓ.val))).ae_ne ℓ.val]
    with x hx hzero hend
  have hxi : x ∈ Ioc (-ℓ.val) ℓ.val := ⟨hx.1, by linarith only [hx.2]⟩
  have hxo : x ∈ Ioo (-ℓ.val) ℓ.val := ⟨hx.1, lt_of_le_of_ne hxi.2 hend⟩
  have hpar (y : ℝ) : (dirichletIntervalMode ℓ n (-y) : ℂ) =
      intervalReflectionSign true * (dirichletIntervalMode ℓ n y : ℂ) := by
    simp only [dirichletIntervalMode, mul_neg, Real.sin_neg, Complex.ofReal_mul,
      Complex.ofReal_neg, intervalReflectionSign, ite_true, neg_one_mul]
  rw [intervalReflectionCircle_coe ℓ true _ hxi,
    intervalReflectionReal_eq_of_parity ℓ true hpar hxo hzero,
    dirichletIntervalMode, Complex.ofReal_mul, ← mul_assoc,
    ← Complex.ofReal_mul, sqrt_length_mul_intervalAmplitude]
  exact fourier_sub_coe_nat ℓ n x

theorem intervalReflectionCircle_neumannIntervalMode_pos
    (ℓ : {ℓ : ℝ // 0 < ℓ}) {n : ℕ} (hn : n ≠ 0) :
    intervalReflectionCircle ℓ false (fun x => (neumannIntervalMode ℓ n x : ℂ))
      =ᵐ[haarAddCircle]
      (fun x => ((Real.sqrt 2 : ℂ) / 2) *
        (fourier (n : ℤ) x + fourier (- (n : ℤ)) x)) := by
  apply circle_ae_of_interval_coe_ae ℓ
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    (volume.restrict (Ioc (-ℓ.val) (-ℓ.val + 2 * ℓ.val))).ae_ne 0,
    (volume.restrict (Ioc (-ℓ.val) (-ℓ.val + 2 * ℓ.val))).ae_ne ℓ.val]
    with x hx hzero hend
  have hxi : x ∈ Ioc (-ℓ.val) ℓ.val := ⟨hx.1, by linarith only [hx.2]⟩
  have hxo : x ∈ Ioo (-ℓ.val) ℓ.val := ⟨hx.1, lt_of_le_of_ne hxi.2 hend⟩
  have hpar (y : ℝ) : (neumannIntervalMode ℓ n (-y) : ℂ) =
      intervalReflectionSign false * (neumannIntervalMode ℓ n y : ℂ) := by
    simp only [neumannIntervalMode, mul_neg, Real.cos_neg, intervalReflectionSign,
      Bool.false_eq_true, ite_false, one_mul]
  rw [intervalReflectionCircle_coe ℓ false _ hxi,
    intervalReflectionReal_eq_of_parity ℓ false hpar hxo hzero]
  simp only [neumannIntervalMode, neumannIntervalCoefficient, ite_eq_right hn,
    Complex.ofReal_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, sqrt_length_mul_intervalAmplitude]
  exact fourier_sum_coe_nat ℓ n x

theorem intervalReflectionCircle_neumannIntervalMode_zero
    (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    intervalReflectionCircle ℓ false (fun x => (neumannIntervalMode ℓ 0 x : ℂ))
      =ᵐ[haarAddCircle] (fun x => fourier 0 x) := by
  apply circle_ae_of_interval_coe_ae ℓ
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    (volume.restrict (Ioc (-ℓ.val) (-ℓ.val + 2 * ℓ.val))).ae_ne 0,
    (volume.restrict (Ioc (-ℓ.val) (-ℓ.val + 2 * ℓ.val))).ae_ne ℓ.val]
    with x hx hzero hend
  have hxi : x ∈ Ioc (-ℓ.val) ℓ.val := ⟨hx.1, by linarith only [hx.2]⟩
  have hxo : x ∈ Ioo (-ℓ.val) ℓ.val := ⟨hx.1, lt_of_le_of_ne hxi.2 hend⟩
  have hpar (y : ℝ) : (neumannIntervalMode ℓ 0 (-y) : ℂ) =
      intervalReflectionSign false * (neumannIntervalMode ℓ 0 y : ℂ) := by
    simp only [neumannIntervalMode_zero, intervalReflectionSign, Bool.false_eq_true,
      ite_false, one_mul]
  rw [intervalReflectionCircle_coe ℓ false _ hxi,
    intervalReflectionReal_eq_of_parity ℓ false hpar hxo hzero,
    neumannIntervalMode_zero, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr ℓ.property).ne', Complex.ofReal_one, fourier_zero]

theorem intervalReflectionL2_dirichletIntervalModeL2
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (n : ℕ+) :
    intervalReflectionL2 ℓ true (dirichletIntervalModeL2 ℓ n) =
      (-Complex.I * ((Real.sqrt 2 : ℂ) / 2)) •
        (fourierLp (T := 2 * ℓ.val) 2 (n : ℤ) - fourierLp 2 (- (n : ℤ))) := by
  apply Lp.ext
  have hr := intervalReflectionCircle_congr_ae ℓ true (dirichletIntervalModeL2_ae ℓ n)
  have ht := intervalReflectionCircle_dirichletIntervalMode ℓ n
  filter_upwards [intervalReflectionL2_ae ℓ true (dirichletIntervalModeL2 ℓ n), hr, ht,
    Lp.coeFn_smul (-Complex.I * ((Real.sqrt 2 : ℂ) / 2))
      (fourierLp (T := 2 * ℓ.val) 2 (n : ℤ) - fourierLp 2 (- (n : ℤ))),
    Lp.coeFn_sub (fourierLp (T := 2 * ℓ.val) 2 (n : ℤ)) (fourierLp 2 (- (n : ℤ))),
    coeFn_fourierLp (T := 2 * ℓ.val) 2 (n : ℤ),
    coeFn_fourierLp (T := 2 * ℓ.val) 2 (- (n : ℤ))] with x hl hr ht hs hd hp hn
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  simp only [Pi.sub_apply] at hd
  rw [hl, hr, ht, hs, hd, hp, hn]

theorem intervalReflectionL2_neumannIntervalModeL2_pos
    (ℓ : {ℓ : ℝ // 0 < ℓ}) {n : ℕ} (hn : n ≠ 0) :
    intervalReflectionL2 ℓ false (neumannIntervalModeL2 ℓ n) =
      ((Real.sqrt 2 : ℂ) / 2) •
        (fourierLp (T := 2 * ℓ.val) 2 (n : ℤ) + fourierLp 2 (- (n : ℤ))) := by
  apply Lp.ext
  have hr := intervalReflectionCircle_congr_ae ℓ false (neumannIntervalModeL2_ae ℓ n)
  have ht := intervalReflectionCircle_neumannIntervalMode_pos ℓ hn
  filter_upwards [intervalReflectionL2_ae ℓ false (neumannIntervalModeL2 ℓ n), hr, ht,
    Lp.coeFn_smul ((Real.sqrt 2 : ℂ) / 2)
      (fourierLp (T := 2 * ℓ.val) 2 (n : ℤ) + fourierLp 2 (- (n : ℤ))),
    Lp.coeFn_add (fourierLp (T := 2 * ℓ.val) 2 (n : ℤ)) (fourierLp 2 (- (n : ℤ))),
    coeFn_fourierLp (T := 2 * ℓ.val) 2 (n : ℤ),
    coeFn_fourierLp (T := 2 * ℓ.val) 2 (- (n : ℤ))] with x hl hr ht hs ha hp hn
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  simp only [Pi.add_apply] at ha
  rw [hl, hr, ht, hs, ha, hp, hn]

theorem intervalReflectionL2_neumannIntervalModeL2_zero
    (ℓ : {ℓ : ℝ // 0 < ℓ}) :
    intervalReflectionL2 ℓ false (neumannIntervalModeL2 ℓ 0) =
      fourierLp (T := 2 * ℓ.val) 2 0 := by
  apply Lp.ext
  have hr := intervalReflectionCircle_congr_ae ℓ false (neumannIntervalModeL2_ae ℓ 0)
  filter_upwards [intervalReflectionL2_ae ℓ false (neumannIntervalModeL2 ℓ 0), hr,
    intervalReflectionCircle_neumannIntervalMode_zero ℓ,
    coeFn_fourierLp (T := 2 * ℓ.val) 2 0] with x hl hr ht hf
  rw [hl, hr, ht, hf]

theorem inner_fourierLp_eq_fourierCoeff {T : ℝ} [Fact (0 < T)]
    (u : Lp ℂ 2 (haarAddCircle (T := T))) (n : ℤ) :
    ⟪fourierLp (T := T) 2 n, u⟫_ℂ = fourierCoeff u n := by
  rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply, coe_fourierBasis]

/-- The constant even-reflection coefficient equals the physical constant-mode coefficient. -/
theorem fourierCoeff_intervalReflectionL2_even_zero (ℓ : {ℓ : ℝ // 0 < ℓ})
    (u : Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))) :
    fourierCoeff (intervalReflectionL2 ℓ false u) 0 =
      ⟪neumannIntervalModeL2 ℓ 0, u⟫_ℂ := by
  have hi := (intervalReflectionLI ℓ false).inner_map_map (neumannIntervalModeL2 ℓ 0) u
  change ⟪intervalReflectionL2 ℓ false (neumannIntervalModeL2 ℓ 0),
    intervalReflectionL2 ℓ false u⟫_ℂ = _ at hi
  rw [intervalReflectionL2_neumannIntervalModeL2_zero, inner_fourierLp_eq_fourierCoeff] at hi
  exact hi

/-- Positive even-reflection coefficients are the physical cosine coefficients divided by √2. -/
theorem fourierCoeff_intervalReflectionL2_even_pos (ℓ : {ℓ : ℝ // 0 < ℓ})
    (n : ℕ+) (u : Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))) :
    fourierCoeff (intervalReflectionL2 ℓ false u) (n : ℤ) =
      ⟪neumannIntervalModeL2 ℓ (n : ℕ), u⟫_ℂ / (Real.sqrt 2 : ℂ) := by
  have hi := (intervalReflectionLI ℓ false).inner_map_map
    (neumannIntervalModeL2 ℓ (n : ℕ)) u
  change ⟪intervalReflectionL2 ℓ false (neumannIntervalModeL2 ℓ (n : ℕ)),
    intervalReflectionL2 ℓ false u⟫_ℂ = _ at hi
  rw [intervalReflectionL2_neumannIntervalModeL2_pos ℓ (n := (n : ℕ)) n.property.ne',
    inner_smul_left, inner_add_left, inner_fourierLp_eq_fourierCoeff,
    inner_fourierLp_eq_fourierCoeff,
    fourierCoeff_neg_of_even (intervalReflectionL2_even ℓ u)] at hi
  simp only [map_div₀, Complex.conj_ofReal, map_ofNat] at hi
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  apply (eq_div_iff hs).mpr
  calc
    _ = ((Real.sqrt 2 : ℂ) / 2) *
        (fourierCoeff (intervalReflectionL2 ℓ false u) (n : ℤ) +
          fourierCoeff (intervalReflectionL2 ℓ false u) (n : ℤ)) := by ring
    _ = _ := hi

/-- Positive odd-reflection coefficients are −i times the physical sine coefficients divided by √2. -/
theorem fourierCoeff_intervalReflectionL2_odd_pos (ℓ : {ℓ : ℝ // 0 < ℓ})
    (n : ℕ+) (u : Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))) :
    fourierCoeff (intervalReflectionL2 ℓ true u) (n : ℤ) =
      (-Complex.I / (Real.sqrt 2 : ℂ)) * ⟪dirichletIntervalModeL2 ℓ n, u⟫_ℂ := by
  have hi := (intervalReflectionLI ℓ true).inner_map_map (dirichletIntervalModeL2 ℓ n) u
  change ⟪intervalReflectionL2 ℓ true (dirichletIntervalModeL2 ℓ n),
    intervalReflectionL2 ℓ true u⟫_ℂ = _ at hi
  rw [intervalReflectionL2_dirichletIntervalModeL2, inner_smul_left, inner_sub_left,
    inner_fourierLp_eq_fourierCoeff, inner_fourierLp_eq_fourierCoeff,
    fourierCoeff_neg_of_odd (intervalReflectionL2_odd ℓ u)] at hi
  simp only [map_mul, map_neg, Complex.conj_I, map_div₀, Complex.conj_ofReal,
    map_ofNat, neg_neg, sub_neg_eq_add] at hi
  have hi' : Complex.I * (Real.sqrt 2 : ℂ) *
      fourierCoeff (intervalReflectionL2 ℓ true u) (n : ℤ) =
      ⟪dirichletIntervalModeL2 ℓ n, u⟫_ℂ := by
    calc
      _ = (Complex.I * ((Real.sqrt 2 : ℂ) / 2)) *
          (fourierCoeff (intervalReflectionL2 ℓ true u) (n : ℤ) +
            fourierCoeff (intervalReflectionL2 ℓ true u) (n : ℤ)) := by ring
      _ = _ := hi
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  rw [← hi']
  field_simp [hs]
  linear_combination
    fourierCoeff (intervalReflectionL2 ℓ true u) (n : ℤ) * Complex.I_sq

end LiebThirring.TFCubes

end
