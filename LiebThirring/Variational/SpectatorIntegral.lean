/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Assembly.RealFormSlices
public import LiebThirring.Variational.FormIntegral

/-!
# Weighted spectator disintegration with all selected-spin sectors

The spectator disintegration Tonelli identity below keeps the finite sum over the selected spin.
It works for every measurable nonnegative kernel, including Coulomb kernels
depending only on the remaining positions and kernels involving the selected
position. No normalization or antisymmetry is used. Real-valued subtraction
is performed only after the nonnegative expectation is proved finite.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- Bounded real weights preserve every finite nonnegative quadratic expectation. -/
theorem lintegral_bounded_weight_lt_top {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} (w : α → ℝ) (B : ℝ)
    (hB : ∀ x, ‖w x‖ ≤ B) (p : α → ℝ≥0∞) (f : α → E)
    (hfin : (∫⁻ x, p x * ‖f x‖ₑ ^ 2 ∂μ) < ⊤) :
    (∫⁻ x, ENNReal.ofReal (w x) * p x * ‖f x‖ₑ ^ 2 ∂μ) < ⊤ := by
  have hbound (x : α) : ENNReal.ofReal (w x) ≤ ENNReal.ofReal B :=
    ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB x))
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal B * (p x * ‖f x‖ₑ ^ 2) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [mul_assoc]
      exact mul_le_mul' (hbound x) le_rfl
    _ = ENNReal.ofReal B * ∫⁻ x, p x * ‖f x‖ₑ ^ 2 ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- The spatial insertion and selected-spin regrouping preserve the pointwise
quadratic mass on one common full-measure set of slices. -/
theorem spectator_spin_mass_ae {N q : ℕ} (i : Fin N) (u : State N q) :
    ∀ᵐ x : Position, ∀ᵐ y : OtherConfiguration i,
      ‖u (insertParticle i x y)‖ₑ ^ 2 =
        ∑ s : Fin q, ‖oneParticleCurrying i u x s y‖ₑ ^ 2 := by
  filter_upwards [oneParticleCurrying_ae i u] with x hx
  have hxy := ae_all_iff.mpr hx
  filter_upwards [hxy] with y hy
  rw [← (spinCurryingLinearIsometryEquiv (q := q) i).enorm_map, piLp_enorm_sq]
  apply Finset.sum_congr rfl
  intro s _
  have heq : spinCurryingLinearIsometryEquiv i (u (insertParticle i x y)) s =
      oneParticleCurrying i u x s y := by
    ext t
    exact (hy s t).symm
  rw [heq]

/-- Tonelli disintegration of an arbitrary nonnegative quadratic expectation,
with the indispensable sum over all selected-spin values. -/
theorem lintegral_spectator_spin {N q : ℕ} (i : Fin N) (u : State N q)
    (p : Position × OtherConfiguration i → ℝ≥0∞) (hp : Measurable p) :
    (∫⁻ X : Configuration N,
      p ((insertionMeasurableEquiv i).symm X) * ‖u X‖ₑ ^ 2) =
      ∫⁻ x : Position, ∑ s : Fin q, ∫⁻ y : OtherConfiguration i,
        p (x, y) * ‖oneParticleCurrying i u x s y‖ₑ ^ 2 := by
  let F : Configuration N → ℝ≥0∞ := fun X =>
    p ((insertionMeasurableEquiv i).symm X) * ‖u X‖ₑ ^ 2
  have hF : Measurable F :=
    (hp.comp (insertionMeasurableEquiv i).symm.measurable).mul
      ((Lp.stronglyMeasurable u).enorm.pow_const 2)
  calc
    _ = ∫⁻ z : Position × OtherConfiguration i, F (insertionMeasurableEquiv i z) :=
      ((measurePreserving_insertion i).lintegral_comp hF).symm
    _ = ∫⁻ x : Position, ∫⁻ y : OtherConfiguration i,
        p (x, y) * ‖u (insertParticle i x y)‖ₑ ^ 2 := by
      have ht := lintegral_prod (μ := (volume : Measure Position))
        (ν := (volume : Measure (OtherConfiguration i))) (fun z : Position × OtherConfiguration i =>
        F (insertionMeasurableEquiv i z))
        (hF.comp (insertionMeasurableEquiv i).measurable).aemeasurable
      simp only [F, MeasurableEquiv.symm_apply_apply] at ht
      have hinv (x : Position) (y : OtherConfiguration i) :
          (insertionMeasurableEquiv i).symm (insertParticle i x y) = (x, y) := by
        rw [← insertionMeasurableEquiv_apply i (x, y), MeasurableEquiv.symm_apply_apply]
      simpa only [F, insertionMeasurableEquiv_apply, hinv, Measure.volume_eq_prod] using ht
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [spectator_spin_mass_ae i u] with x hx
      calc
        _ = ∫⁻ y : OtherConfiguration i,
            ∑ s : Fin q, p (x, y) * ‖oneParticleCurrying i u x s y‖ₑ ^ 2 := by
          apply lintegral_congr_ae
          filter_upwards [hx] with y hy
          rw [hy, Finset.mul_sum]
        _ = _ := lintegral_finsetSum _ (fun s _ =>
          ((hp.comp (measurable_const.prodMk measurable_id)).mul
            ((Lp.stronglyMeasurable (oneParticleCurrying i u x s)).enorm.pow_const 2)))

/-- Kernels wholly in the spectator coordinates disintegrate without a spin factor. -/
theorem lintegral_spectator_weight {N q : ℕ} (i : Fin N) (u : State N q)
    (p : OtherConfiguration i → ℝ≥0∞) (hp : Measurable p) :
    (∫⁻ X : Configuration N,
      p (((insertionMeasurableEquiv i).symm X).2) * ‖u X‖ₑ ^ 2) =
      ∫⁻ x : Position, ∑ s : Fin q, ∫⁻ y : OtherConfiguration i,
        p y * ‖oneParticleCurrying i u x s y‖ₑ ^ 2 :=
  lintegral_spectator_spin i u (fun z => p z.2) (hp.comp measurable_snd)

/-- The sum of the sector expectations is a measurable function up to null sets,
despite the representative choices made by L² currying. -/
theorem spectator_spin_expectation_aemeasurable {N q : ℕ} (i : Fin N) (u : State N q)
    (p : Position × OtherConfiguration i → ℝ≥0∞) (hp : Measurable p) :
    AEMeasurable (fun x : Position => ∑ s : Fin q,
      ∫⁻ y : OtherConfiguration i, p (x, y) * ‖oneParticleCurrying i u x s y‖ₑ ^ 2) volume := by
  have hm : Measurable (fun z : Position × OtherConfiguration i =>
      p z * ‖u (insertParticle i z.1 z.2)‖ₑ ^ 2) :=
    hp.mul (((Lp.stronglyMeasurable u).comp_measurable
      (measurePreserving_insertParticle i).measurable).enorm.pow_const 2)
  have heq : (fun x : Position => ∑ s : Fin q,
      ∫⁻ y : OtherConfiguration i, p (x, y) * ‖oneParticleCurrying i u x s y‖ₑ ^ 2) =ᵐ[volume]
      fun x => ∫⁻ y : OtherConfiguration i, p (x, y) * ‖u (insertParticle i x y)‖ₑ ^ 2 := by
    filter_upwards [spectator_spin_mass_ae i u] with x hx
    have hsum := lintegral_finsetSum (μ := (volume : Measure (OtherConfiguration i)))
      (s := (Finset.univ : Finset (Fin q)))
      (f := fun s y => p (x, y) * ‖oneParticleCurrying i u x s y‖ₑ ^ 2)
      (fun s _ => (hp.comp (measurable_prodMk_left (x := x))).mul
        ((Lp.stronglyMeasurable (oneParticleCurrying i u x s)).enorm.pow_const 2))
    rw [← hsum]
    apply lintegral_congr_ae
    filter_upwards [hx] with y hy
    rw [hy, Finset.mul_sum]
  exact (hm.lintegral_prod_right).aemeasurable.congr heq.symm

end LiebThirring
end
