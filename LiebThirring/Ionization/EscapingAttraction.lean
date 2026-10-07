/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapingSectorKernels
public import LiebThirring.Ionization.EscapingInside

/-! # The integrated attraction cost of an escaping sector -/

public section

open MeasureTheory
open scoped ENNReal NNReal Classical

namespace LiebThirring
open Variational

/-- Selected attraction is finite whenever the full state has finite kinetic energy. -/
theorem lintegral_selected_attraction_lt_top {N k q : ℕ} (Z : ℝ≥0)
    (S : Finset (Fin N)) (e : Fin k ≃ (S : Set (Fin N)))
    (v : State N q) (hv : kineticEnergy v < ⊤) :
    (∫⁻ X : Configuration N,
      attraction (fun _ : Fin 1 => Z) (fun _ => 0)
        (((subsetOrderedInsertion (S : Set (Fin N)) e).symm X).2) * ‖v X‖ₑ ^ 2) < ⊤ := by
  apply (lintegral_mono (fun X => ?_)).trans_lt
    (lintegral_attraction_lt_top (fun _ : Fin 1 => Z) (fun _ => 0) v hv)
  apply mul_le_mul' _ le_rfl
  have h := attraction_subsetOrderedInsertion_selected_le Z S e
    ((subsetOrderedInsertion (S : Set (Fin N)) e).symm X).1
    ((subsetOrderedInsertion (S : Set (Fin N)) e).symm X).2
  simpa only [Prod.mk.eta, MeasurableEquiv.apply_symm_apply] using h

/-- Complementary electrons cost at most `NZ/R` times the localized mass in attraction.
The selected attraction remains a literal pulled-back quadratic expectation. -/
theorem imsLocalizedState_attraction_le_selected_add_error {N k q : ℕ}
    {R : ℝ} (hR : 0 < R) (Z : ℝ≥0) (S : Finset (Fin N))
    (e : Fin k ≃ (S : Set (Fin N))) (u : State N q) (hu : kineticEnergy u < ⊤) :
    let v := imsLocalizedState hR S u
    (∫⁻ X : Configuration N,
      attraction (fun _ : Fin 1 => Z) (fun _ => 0) X * ‖v X‖ₑ ^ 2).toReal ≤
      (∫⁻ X : Configuration N,
        attraction (fun _ : Fin 1 => Z) (fun _ => 0)
          (((subsetOrderedInsertion (S : Set (Fin N)) e).symm X).2) * ‖v X‖ₑ ^ 2).toReal +
        ((N : ℝ) * (Z : ℝ) / R) * ‖v‖ ^ 2 := by
  let v := imsLocalizedState hR S u
  let p : Configuration N → ℝ≥0∞ := fun X =>
    attraction (fun _ : Fin 1 => Z) (fun _ => 0)
      (((subsetOrderedInsertion (S : Set (Fin N)) e).symm X).2)
  let c : ℝ≥0∞ := (N : ℝ≥0∞) * (Z : ℝ≥0∞) * (ENNReal.ofReal R)⁻¹
  have hv := imsLocalizedState_kineticEnergy_lt_top hR S u hu
  have hfin := lintegral_selected_attraction_lt_top Z S e v hv
  have hp : Measurable p := (measurable_attraction _ _).comp
    (measurable_snd.comp (subsetOrderedInsertion (S : Set (Fin N)) e).symm.measurable)
  have hcle : (N - k : ℝ≥0∞) * (Z : ℝ≥0∞) * (ENNReal.ofReal R)⁻¹ ≤ c := by
    exact mul_le_mul' (mul_le_mul' tsub_le_self le_rfl) le_rfl
  have hpoint : ∀ᵐ X : Configuration N,
      attraction (fun _ : Fin 1 => Z) (fun _ => 0) X * ‖v X‖ₑ ^ 2 ≤
        (p X + c) * ‖v X‖ₑ ^ 2 := by
    filter_upwards [imsLocalizedState_coeFn hR S u] with X hX
    by_cases hw : imsSectorWeight (imsChi R) (imsEta R) S X = 0
    · have hz : v X = 0 := by rw [hX, hw, Complex.ofReal_zero, zero_smul]
      rw [hz, enorm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, mul_zero]
    · have ha := attraction_subsetOrderedInsertion_le_of_sector_ne_zero hR Z S e
        ((subsetOrderedInsertion (S : Set (Fin N)) e).symm X).1
        ((subsetOrderedInsertion (S : Set (Fin N)) e).symm X).2
        (by simpa only [Prod.mk.eta, MeasurableEquiv.apply_symm_apply] using hw)
      simp only [Prod.mk.eta, MeasurableEquiv.apply_symm_apply] at ha
      exact mul_le_mul' (ha.trans (add_le_add le_rfl hcle)) le_rfl
  have hcfin : c ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) ENNReal.coe_ne_top
    · exact ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hR))
  have hmassfin : c * ‖v‖ₑ ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top hcfin (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hbound : (∫⁻ X : Configuration N,
      attraction (fun _ : Fin 1 => Z) (fun _ => 0) X * ‖v X‖ₑ ^ 2) ≤
      (∫⁻ X : Configuration N, p X * ‖v X‖ₑ ^ 2) + c * ‖v‖ₑ ^ 2 := by
    calc
      _ ≤ ∫⁻ X : Configuration N, (p X + c) * ‖v X‖ₑ ^ 2 := lintegral_mono_ae hpoint
      _ = _ := by
        simp_rw [add_mul]
        have hmeas : Measurable (fun X => p X * ‖v X‖ₑ ^ 2) :=
          hp.mul ((Lp.stronglyMeasurable v).enorm.pow_const 2)
        rw [lintegral_add_left hmeas,
          lintegral_const_mul _ ((Lp.stronglyMeasurable v).enorm.pow_const 2),
          lintegral_l2_enorm_sq]
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin.ne, hmassfin⟩) hbound
  rw [ENNReal.toReal_add hfin.ne hmassfin, ENNReal.toReal_mul, ENNReal.toReal_pow,
    enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm] at hreal
  have hcr : c.toReal = (N : ℝ) * (Z : ℝ) / R := by
    simp only [c, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.coe_toReal,
      ENNReal.toReal_inv, ENNReal.toReal_ofReal hR.le, div_eq_mul_inv]
  rw [hcr] at hreal
  exact hreal

end LiebThirring
end
