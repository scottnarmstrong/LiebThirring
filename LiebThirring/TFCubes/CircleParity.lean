/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Reflection and Fourier coefficients on the doubled circle

The interval reflection step in the cube spectral theory reduces interval sine/cosine completeness
and Parseval to odd/even circle functions. This module proves the circle part of that
reduction. The circle Haar measure has total mass one. These results do not construct
an interval reflection map, an interval mode basis, or a Sobolev form identity.
-/

public section

noncomputable section

open MeasureTheory AddCircle
open scoped ENNReal

namespace LiebThirring.TFCubes

variable {T : ℝ}

/-- Reflection of a circle character reverses its integer frequency. -/
theorem fourier_apply_neg (n : ℤ) (x : AddCircle T) :
    fourier n (-x) = fourier (-n) x := by
  simp only [fourier_apply, smul_neg, neg_smul]

variable [Fact (0 < T)]

/-- Reflection reverses Fourier coefficients, with no integrability prerequisite. -/
theorem fourierCoeff_comp_neg (f : AddCircle T → ℂ) (n : ℤ) :
    fourierCoeff (fun x => f (-x)) n = fourierCoeff f (-n) := by
  unfold fourierCoeff
  rw [← integral_neg_eq_self (fun x : AddCircle T => fourier (-n) x • f (-x))
    haarAddCircle]
  simp only [fourier_apply_neg, neg_neg]

/-- The Fourier coefficients of an even circle function are even. -/
theorem fourierCoeff_neg_of_even {f : AddCircle T → ℂ}
    (hf : (fun x => f (-x)) =ᵐ[haarAddCircle] f) (n : ℤ) :
    fourierCoeff f (-n) = fourierCoeff f n := by
  rw [← fourierCoeff_comp_neg]
  exact congrFun (fourierCoeff_congr_ae hf) n

/-- The Fourier coefficients of an odd circle function are odd. -/
theorem fourierCoeff_neg_of_odd {f : AddCircle T → ℂ}
    (hf : (fun x => f (-x)) =ᵐ[haarAddCircle] (fun x => -f x)) (n : ℤ) :
    fourierCoeff f (-n) = -fourierCoeff f n := by
  rw [← fourierCoeff_comp_neg, congrFun (fourierCoeff_congr_ae hf) n]
  simp only [fourierCoeff, smul_neg, integral_neg]

/-- An odd circle function has no constant coefficient. -/
theorem fourierCoeff_zero_of_odd {f : AddCircle T → ℂ}
    (hf : (fun x => f (-x)) =ᵐ[haarAddCircle] (fun x => -f x)) :
    fourierCoeff f 0 = 0 := by
  have h := fourierCoeff_neg_of_odd hf 0
  simp only [neg_zero] at h
  exact CharZero.eq_neg_self_iff.mp h

/-- Circle Fourier completeness expressed as coefficient uniqueness. -/
theorem eq_zero_of_fourierCoeff_eq_zero (f : Lp ℂ 2 (haarAddCircle (T := T)))
    (hf : ∀ n : ℤ, fourierCoeff f n = 0) : f = 0 := by
  apply fourierBasis.repr.injective
  ext n
  rw [fourierBasis_repr, hf n]
  simp only [map_zero, lp.coeFn_zero, Pi.zero_apply]

/-- Positive coefficients and the constant coefficient determine an even circle
function. This is the completeness input for interval cosine reflection. -/
theorem eq_zero_of_even_positive_fourierCoeff_eq_zero
    (f : Lp ℂ 2 (haarAddCircle (T := T)))
    (hfeven : (fun x => f (-x)) =ᵐ[haarAddCircle] f)
    (hzero : fourierCoeff f 0 = 0)
    (hf : ∀ n : ℕ+, fourierCoeff f (n : ℤ) = 0) : f = 0 := by
  apply eq_zero_of_fourierCoeff_eq_zero f
  intro n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have hnpos : 0 < -n := neg_pos.mpr hn
    have h := hf ⟨(-n).toNat, by omega⟩
    change fourierCoeff f ((-n).toNat : ℤ) = 0 at h
    rw [Int.toNat_of_nonneg hnpos.le, fourierCoeff_neg_of_even hfeven] at h
    exact h
  · exact hzero
  · have h := hf ⟨n.toNat, by omega⟩
    change fourierCoeff f (n.toNat : ℤ) = 0 at h
    rwa [Int.toNat_of_nonneg hn.le] at h

/-- Positive coefficients determine an odd circle function. This is the
completeness input for interval sine reflection. -/
theorem eq_zero_of_odd_positive_fourierCoeff_eq_zero
    (f : Lp ℂ 2 (haarAddCircle (T := T)))
    (hfodd : (fun x => f (-x)) =ᵐ[haarAddCircle] (fun x => -f x))
    (hf : ∀ n : ℕ+, fourierCoeff f (n : ℤ) = 0) : f = 0 := by
  apply eq_zero_of_fourierCoeff_eq_zero f
  intro n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have hnpos : 0 < -n := neg_pos.mpr hn
    have h := hf ⟨(-n).toNat, by omega⟩
    change fourierCoeff f ((-n).toNat : ℤ) = 0 at h
    rw [Int.toNat_of_nonneg hnpos.le, fourierCoeff_neg_of_odd hfodd] at h
    exact neg_eq_zero.mp h
  · exact fourierCoeff_zero_of_odd hfodd
  · have h := hf ⟨n.toNat, by omega⟩
    change fourierCoeff f (n.toNat : ℤ) = 0 at h
    rwa [Int.toNat_of_nonneg hn.le] at h

end LiebThirring.TFCubes
