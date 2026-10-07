/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.MultiplierContinuity
public import LiebThirring.Sobolev.WeakFormDensity

/-!
# Product rule for bounded scalar weak multipliers

A complex scalar function with a bounded weak coordinate derivative satisfies the product rule
on the weak Sobolev graph.  The proof first treats compactly supported Schwartz states and then
passes to arbitrary states through compact smooth form approximation.
-/

public section

open MeasureTheory Filter LineDeriv
open scoped ContDiff Topology SchwartzMap FourierTransform

namespace LiebThirring.Sobolev

/-- Distributional coordinate derivative for a complex scalar function. -/
@[expose] def HasScalarWeakDerivative {N : ℕ} (a : Fin N × Fin 3)
    (b db : Configuration N → ℂ) : Prop :=
  ∀ φ : Configuration N → ℂ, HasCompactSupport φ → ContDiff ℝ ∞ φ →
    (∫ x, db x * φ x) = -(∫ x, b x * fderiv ℝ φ x (coordinateVector a))

/-- The `L²` derivative predicted by the scalar weak product rule. -/
@[expose] noncomputable def scalarWeakProductDerivative {N q : ℕ}
    (b db : Configuration N → ℂ) (B D : ℝ)
    (hB : ∀ x, ‖b x‖ ≤ B) (hD : ∀ x, ‖db x‖ ≤ D)
    (hb : AEStronglyMeasurable b) (hdb : AEStronglyMeasurable db)
    (u g : State N q) : State N q :=
  boundedSMul b g B hB hb + boundedSMul db u D hD hdb

theorem scalarWeakProductDerivative_coeFn {N q : ℕ}
    (b db : Configuration N → ℂ) (B D : ℝ)
    (hB : ∀ x, ‖b x‖ ≤ B) (hD : ∀ x, ‖db x‖ ≤ D)
    (hb : AEStronglyMeasurable b) (hdb : AEStronglyMeasurable db)
    (u g : State N q) :
    ⇑(scalarWeakProductDerivative b db B D hB hD hb hdb u g) =ᵐ[volume]
      fun x => b x • g x + db x • u x := by
  filter_upwards [Lp.coeFn_add (boundedSMul b g B hB hb) (boundedSMul db u D hD hdb),
    boundedSMul_coeFn b g B hB hb, boundedSMul_coeFn db u D hD hdb] with x hadd hbg hdu
  change (boundedSMul b g B hB hb + boundedSMul db u D hD hdb : State N q) x = _
  rw [hadd]
  simp only [Pi.add_apply, hbg, hdu]

private theorem fderiv_inner_apply_direction {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] (η f : E → F) (hη : ContDiff ℝ ∞ η)
    (hf : ContDiff ℝ ∞ f) (x v : E) :
    fderiv ℝ (fun y => inner ℂ (η y) (f y)) x v =
      inner ℂ (η x) (fderiv ℝ f x v) + inner ℂ (fderiv ℝ η x v) (f x) := by
  exact fderiv_inner_apply ℂ
    (hη.differentiable (by simp) x) (hf.differentiable (by simp) x) v

private theorem integrable_bounded_mul_compact {N : ℕ}
    (b φ : Configuration N → ℂ) (B : ℝ) (hB : ∀ x, ‖b x‖ ≤ B)
    (hb : AEStronglyMeasurable b) (hφK : HasCompactSupport φ) (hφ : Continuous φ) :
    Integrable (fun x => b x * φ x) := by
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hφK
  exact hφi.bdd_mul hb (Filter.Eventually.of_forall hB)

private theorem hasWeakDerivative_scalar_weak_product_schwartz {N q : ℕ}
    {a : Fin N × Fin 3} (b db : Configuration N → ℂ) (B D : ℝ)
    (hB : ∀ x, ‖b x‖ ≤ B) (hD : ∀ x, ‖db x‖ ≤ D)
    (hb : AEStronglyMeasurable b) (hdb : AEStronglyMeasurable db)
    (hweak : HasScalarWeakDerivative a b db)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    HasWeakDerivative a (boundedSMul b (f.toLp 2 volume) B hB hb)
      (scalarWeakProductDerivative b db B D hB hD hb hdb
        (f.toLp 2 volume) (schwartzCoordinateDerivativeL2 f a)) := by
  intro η hηK hη
  let dη := fun x => fderiv ℝ η x (coordinateVector a)
  let df := fun x => fderiv ℝ f x (coordinateVector a)
  let φ := fun x => inner ℂ (η x) (f x)
  have hdηK : HasCompactSupport dη := hηK.fderiv_apply ℝ _
  have hdη : ContDiff ℝ ∞ dη := (hη.fderiv_right (by simp)).clm_apply contDiff_const
  have hdf : ContDiff ℝ ∞ df := (f.smooth ⊤).fderiv_right (by simp) |>.clm_apply contDiff_const
  have hφK : HasCompactSupport φ := hηK.mono (by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hzero
    dsimp only [φ] at hx
    simp [hzero] at hx)
  have hφ : ContDiff ℝ ∞ φ := hη.inner ℂ (f.smooth ⊤)
  have hηdfK : HasCompactSupport (fun x => inner ℂ (η x) (df x)) := hηK.mono (by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hzero
    simp [hzero] at hx)
  have hdηfK : HasCompactSupport (fun x => inner ℂ (dη x) (f x)) := hdηK.mono (by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hzero
    simp [hzero] at hx)
  have hi₁ := integrable_bounded_mul_compact b (fun x => inner ℂ (η x) (df x)) B hB hb
    hηdfK (hη.continuous.inner hdf.continuous)
  have hi₂ := integrable_bounded_mul_compact b (fun x => inner ℂ (dη x) (f x)) B hB hb
    hdηfK (hdη.continuous.inner (f.smooth ⊤).continuous)
  let dfL2 : State N q := (lineDerivOp (coordinateVector a) f).toLp 2 volume
  have hdfL2 : HasWeakDerivative a (f.toLp 2 volume) dfL2 := by
    rw [hasWeakDerivative_iff_fourier_eq_symbol]
    have hderiv : 𝓕 dfL2 = (𝓕 (lineDerivOp (coordinateVector a) f)).toLp 2 volume :=
      SchwartzMap.toLp_fourier_eq _
    have hstate : 𝓕 (f.toLp 2 volume) = (𝓕 f).toLp 2 volume :=
      SchwartzMap.toLp_fourier_eq f
    filter_upwards [(𝓕 (lineDerivOp (coordinateVector a) f)).coeFn_toLp 2 volume,
      (𝓕 f).coeFn_toLp 2 volume] with ξ hd hu
    rw [hderiv, hstate, hd, hu, fourier_lineDeriv_coordinate]
  have hderivEq : schwartzCoordinateDerivativeL2 f a = dfL2 :=
    (hasWeakDerivative_schwartzCoordinateDerivativeL2 f a).unique hdfL2
  have hs := hweak φ hφK hφ
  have hsplit : (∫ x, b x * fderiv ℝ φ x (coordinateVector a)) =
      (∫ x, b x * inner ℂ (η x) (df x)) +
        (∫ x, b x * inner ℂ (dη x) (f x)) := by
    dsimp only [φ, dη, df]
    simp_rw [fderiv_inner_apply_direction η f hη (f.smooth ⊤), mul_add]
    exact integral_add hi₁ hi₂
  rw [hsplit] at hs
  have hleft : (∫ x, inner ℂ (η x)
      (scalarWeakProductDerivative b db B D hB hD hb hdb
        (f.toLp 2 volume) (schwartzCoordinateDerivativeL2 f a) x)) =
      (∫ x, b x * inner ℂ (η x) (df x)) + (∫ x, db x * φ x) := by
    rw [hderivEq]
    rw [← integral_add hi₁
      (integrable_bounded_mul_compact db φ D hD hdb hφK hφ.continuous)]
    apply integral_congr_ae
    filter_upwards [scalarWeakProductDerivative_coeFn b db B D hB hD hb hdb
        (f.toLp 2 volume) dfL2,
      (lineDerivOp (coordinateVector a) f).coeFn_toLp 2 volume,
      (f.memLp 2 volume).coeFn_toLp] with x hx hdx hfx
    rw [hx, inner_add_right, inner_smul_right, inner_smul_right]
    change _ = b x * inner ℂ (η x) (df x) + db x * φ x
    rw [show dfL2 x = df x by exact hdx,
      show (f.toLp 2 volume : State N q) x = f x by exact hfx]
  have hright : (∫ x, inner ℂ (dη x)
      (boundedSMul b (f.toLp 2 volume) B hB hb x)) =
      ∫ x, b x * inner ℂ (dη x) (f x) := by
    apply integral_congr_ae
    filter_upwards [boundedSMul_coeFn b (f.toLp 2 volume) B hB hb,
      (f.memLp 2 volume).coeFn_toLp] with x hbx hfx
    rw [hbx, inner_smul_right]
    exact congrArg (fun z => b x * inner ℂ (dη x) z) hfx
  change _ = -(∫ x, inner ℂ (dη x) (boundedSMul b (f.toLp 2 volume) B hB hb x))
  rw [hleft, hright, hs, neg_add]
  abel

/-- A bounded complex scalar multiplier with bounded weak derivatives obeys the weak product rule
in every coordinate on the full weak `H¹` graph. -/
theorem hasWeakDerivative_scalar_weak_product {N q : ℕ} {u : State N q}
    (g : (Fin N × Fin 3) → State N q) (hu : ∀ a, HasWeakDerivative a u (g a))
    (b : Configuration N → ℂ) (db : (Fin N × Fin 3) → Configuration N → ℂ)
    (B : ℝ) (D : (Fin N × Fin 3) → ℝ)
    (hB : ∀ x, ‖b x‖ ≤ B) (hD : ∀ a x, ‖db a x‖ ≤ D a)
    (hb : AEStronglyMeasurable b) (hdb : ∀ a, AEStronglyMeasurable (db a))
    (hweak : ∀ a, HasScalarWeakDerivative a b (db a)) :
    ∀ a, HasWeakDerivative a (boundedSMul b u B hB hb)
      (scalarWeakProductDerivative b (db a) B (D a) hB (hD a) hb (hdb a) u (g a)) := by
  choose f _hfK hfu hfg using
    exists_compact_smooth_weakDerivative_sequence u g hu
  intro a
  apply HasWeakDerivative.closed_of_tendsto
    (fun n => hasWeakDerivative_scalar_weak_product_schwartz b (db a) B (D a) hB (hD a)
      hb (hdb a) (hweak a) (f n))
  · exact tendsto_boundedSMul b B hB hb hfu
  · change Tendsto (fun n => boundedSMul b (schwartzCoordinateDerivativeL2 (f n) a) B hB hb +
        boundedSMul (db a) ((f n).toLp 2 volume) (D a) (hD a) (hdb a)) atTop
      (𝓝 (boundedSMul b (g a) B hB hb + boundedSMul (db a) u (D a) (hD a) (hdb a)))
    exact (tendsto_boundedSMul b B hB hb (hfg a)).add
      (tendsto_boundedSMul (db a) (D a) (hD a) (hdb a) hfu)

end LiebThirring.Sobolev

end
