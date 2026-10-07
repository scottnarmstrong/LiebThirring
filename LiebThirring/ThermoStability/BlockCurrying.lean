/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Kinetic.CurryingState
public import LiebThirring.Fourier.Functoriality

/-! # Interchanging arbitrary finite-dimensional L² blocks and Fourier transformation

Generalization of `Assembly.RealFormCurrying` from a single three-dimensional position
to an arbitrary Euclidean block, for the quantum stability.

Product currying supplies genuine L² classes in both orders. The interchange
of a partial Fourier transform is proved on scalar tensors and extended by
L² density; it does not assert pointwise Fourier integration for an L² state.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal FourierTransform

namespace LiebThirring.ThermoStability

variable {α E V : Type*} [MeasurableSpace α]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {ν : Measure α} [SFinite ν]
  [SecondCountableTopology (Lp E 2 ν)]
  [SecondCountableTopology (Lp E 2 (volume : Measure V))]

/-- Interchange the outer spatial variable and the remaining L² variable. -/
@[expose] noncomputable def blockSwapCurrying :
    Lp (Lp E 2 ν) 2 (volume : Measure V) ≃ₗᵢ[ℂ]
      Lp (Lp E 2 (volume : Measure V)) 2 ν :=
  (l2CurryLinearIsometryEquiv (μ := (volume : Measure V)) (ν := ν)
    (E := E)).symm |>.trans
    (l2PullbackEquiv (E := E) (MeasurableEquiv.prodComm (α := α) (β := V))
      Measure.measurePreserving_swap) |>.trans
    (l2CurryLinearIsometryEquiv (μ := ν) (ν := (volume : Measure V)) (E := E))

/-- Exchanging slices is currying the swapped product class. -/
theorem blockSwapCurrying_apply (u : Lp (Lp E 2 ν) 2 (volume : Measure V)) :
    blockSwapCurrying u = l2Curry
      (l2PullbackEquiv (E := E)
        (MeasurableEquiv.prodComm (α := α) (β := V)) Measure.measurePreserving_swap
        ((l2CurryLinearIsometryEquiv (μ := (volume : Measure V))
          (ν := ν) (E := E)).symm u)) := rfl

/-- The exchanged class agrees with the uncurried product representative,
in the order needed to apply the one-body estimate on each remaining slice. -/
theorem blockSwapCurrying_ae_uncurry
    (u : Lp (Lp E 2 ν) 2 (volume : Measure V)) :
    ∀ᵐ y ∂ν, ∀ᵐ x : V, blockSwapCurrying u y x =
      ((l2CurryLinearIsometryEquiv (μ := (volume : Measure V))
        (ν := ν) (E := E)).symm u) (x, y) := by
  let f := (l2CurryLinearIsometryEquiv (μ := (volume : Measure V))
    (ν := ν) (E := E)).symm u
  let g := l2PullbackEquiv (E := E)
    (MeasurableEquiv.prodComm (α := α) (β := V)) Measure.measurePreserving_swap f
  change ∀ᵐ y ∂ν, ∀ᵐ x : V, l2Curry g y x = f (x, y)
  filter_upwards [l2Curry_ae g, Measure.ae_ae_of_ae_prod (l2PullbackEquiv_ae
    (MeasurableEquiv.prodComm (α := α) (β := V)) Measure.measurePreserving_swap f)]
    with y hy ht
  filter_upwards [hy, ht] with x hx htx
  exact hx.trans htx

/-- Weighted spatial mass is unchanged by exchanging the slice order. -/
theorem blockSwapCurrying_weighted_norm_sq
    (u : Lp (Lp E 2 ν) 2 (volume : Measure V))
    (w : V → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ y, ∫⁻ x : V, w x * ‖blockSwapCurrying u y x‖ₑ ^ 2 ∂(volume : Measure V) ∂ν) =
      ∫⁻ x : V, w x * ‖u x‖ₑ ^ 2 := by
  let f := (l2CurryLinearIsometryEquiv (μ := (volume : Measure V))
    (ν := ν) (E := E)).symm u
  have hc : ∀ᵐ x : V, ∀ᵐ y ∂ν, u x y = f (x, y) := by
    have h := l2Curry_ae f
    rw [show l2Curry f = u from
      (l2CurryLinearIsometryEquiv (μ := (volume : Measure V))
        (ν := ν) (E := E)).apply_symm_apply u] at h
    exact h
  calc
    _ = ∫⁻ y, ∫⁻ x : V, w x * ‖f (x, y)‖ₑ ^ 2 ∂(volume : Measure V) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [blockSwapCurrying_ae_uncurry u] with y hy
      exact lintegral_congr_ae (hy.mono fun x hx => congrArg (fun a : E => w x * ‖a‖ₑ ^ 2) hx)
    _ = ∫⁻ x : V, ∫⁻ y, w x * ‖f (x, y)‖ₑ ^ 2 ∂ν := by
      exact (lintegral_lintegral_swap
        ((hw.comp measurable_fst).mul ((Lp.stronglyMeasurable f).enorm.pow_const 2)).aemeasurable).symm
    _ = ∫⁻ x : V, w x * ‖u x‖ₑ ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [hc] with x hx
      rw [lintegral_const_mul (w x)
        (f := fun y => ‖f (x, y)‖ₑ ^ 2)
        (((Lp.stronglyMeasurable f).comp_measurable
          (measurable_prodMk_left (x := x))).enorm.pow_const 2),
        ← lintegral_l2_enorm_sq (u x)]
      congr 1
      exact lintegral_congr_ae (hx.mono fun y hy => congrArg (fun a : E => ‖a‖ₑ ^ 2) hy.symm)

/-- Scalar tensor insertion into a Hilbert-valued spatial L² space. -/
@[expose] noncomputable def blockScalarInsertion
    (f : Lp ℂ 2 (volume : Measure V)) : E →L[ℂ] Lp E 2 (volume : Measure V) :=
  ((ContinuousLinearMap.lsmul ℂ ℂ (E := E)).flip.compLpL₂ 2 volume).flip f

omit [CompleteSpace E] [SecondCountableTopology (Lp E 2 (volume : Measure V))] in
theorem blockScalarInsertion_ae (f : Lp ℂ 2 (volume : Measure V)) (v : E) :
    blockScalarInsertion f v =ᵐ[volume] fun x => f x • v :=
  (ContinuousLinearMap.toSpanSingleton ℂ v).coeFn_compLp f

omit [CompleteSpace E] [SecondCountableTopology (Lp E 2 ν)]
  [SecondCountableTopology (Lp E 2 (volume : Measure V))] in
private theorem memLp_blockTensor (f : Lp ℂ 2 (volume : Measure V))
    (v : Lp E 2 ν) :
    MemLp (fun z : V × α => f z.1 • v z.2) 2 ((volume : Measure V).prod ν) := by
  have hm : StronglyMeasurable (fun z : V × α => f z.1 • v z.2) :=
    ((Lp.stronglyMeasurable f).comp_measurable measurable_fst).smul
      ((Lp.stronglyMeasurable v).comp_measurable measurable_snd)
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    hm.aestronglyMeasurable).mpr
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_smul, mul_pow]
  rw [lintegral_prod_mul ((Lp.stronglyMeasurable f).enorm.pow_const 2).aemeasurable
    ((Lp.stronglyMeasurable v).enorm.pow_const 2).aemeasurable,
    lintegral_l2_enorm_sq, lintegral_l2_enorm_sq]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
    (ENNReal.pow_lt_top ENNReal.coe_lt_top)

/-- Slice interchange on an elementary scalar tensor. -/
theorem blockSwapCurrying_tensor (f : Lp ℂ 2 (volume : Measure V))
    (v : Lp E 2 ν) :
    blockSwapCurrying ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp f) =
      (blockScalarInsertion f).compLp v := by
  let h := memLp_blockTensor f v
  let w := h.toLp (fun z : V × α => f z.1 • v z.2)
  have hw : ∀ᵐ x : V, ∀ᵐ y ∂ν, w (x, y) = f x • v y :=
    Measure.ae_ae_of_ae_prod h.coeFn_toLp
  have hc : l2Curry w = (ContinuousLinearMap.toSpanSingleton ℂ v).compLp f := by
    apply Lp.ext
    filter_upwards [l2Curry_ae w,
      (ContinuousLinearMap.toSpanSingleton ℂ v).coeFn_compLp f, hw] with x hx ht hwx
    rw [ht]
    apply Lp.ext
    filter_upwards [hx, hwx, Lp.coeFn_smul (f x) v] with y hxy hwy hsy
    exact hxy.trans (hwy.trans hsy.symm)
  have hinv : (l2CurryLinearIsometryEquiv (μ := (volume : Measure V))
      (ν := ν) (E := E)).symm ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp f) = w := by
    rw [← hc]
    exact (l2CurryLinearIsometryEquiv (μ := (volume : Measure V))
      (ν := ν) (E := E)).symm_apply_apply w
  rw [blockSwapCurrying_apply, hinv]
  apply Lp.ext
  have hp := (Measure.measurePreserving_swap (μ := ν)
    (ν := (volume : Measure V))).quasiMeasurePreserving.ae h.coeFn_toLp
  filter_upwards [l2Curry_ae
      (l2PullbackEquiv (E := E) (MeasurableEquiv.prodComm (α := α) (β := V))
        Measure.measurePreserving_swap w),
    Measure.ae_ae_of_ae_prod (l2PullbackEquiv_ae
      (MeasurableEquiv.prodComm (α := α) (β := V)) Measure.measurePreserving_swap w),
    Measure.ae_ae_of_ae_prod hp,
    (blockScalarInsertion f).coeFn_compLp v] with y hy ht hw' hr
  rw [hr]
  apply Lp.ext
  filter_upwards [hy, ht, hw', blockScalarInsertion_ae f (v y)]
    with x hyx htx hwx hrx
  exact hyx.trans (htx.trans (hwx.trans hrx.symm))

theorem continuousLinearMap_ext_scalarTensor
    {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (A B : Lp H 2 (volume : Measure V) →L[ℂ] K)
    (h : ∀ (f : Lp ℂ 2 (volume : Measure V)) (v : H),
      A ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp f) =
        B ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp f)) : A = B := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.induction (p := (2 : ℝ≥0∞)) (μ := (volume : Measure V))
    (by norm_num) (fun u => A u = B u)
  · intro v s hs hμs
    let f : Lp ℂ 2 (volume : Measure V) := indicatorConstLp 2 hs hμs.ne 1
    have heq : Lp.simpleFunc.indicatorConst 2 hs hμs.ne v =
        (ContinuousLinearMap.toSpanSingleton ℂ v).compLp f := by
      rw [Lp.simpleFunc.coe_indicatorConst]
      apply Lp.ext
      filter_upwards [show ∀ᵐ x : V,
          (indicatorConstLp 2 hs hμs.ne v : Lp H 2 volume) x = s.indicator (fun _ => v) x
          from indicatorConstLp_coeFn,
        (ContinuousLinearMap.toSpanSingleton ℂ v).coeFn_compLp f,
        show ∀ᵐ x : V, f x = s.indicator (fun _ => (1 : ℂ)) x
          from indicatorConstLp_coeFn] with x hx ht hf
      rw [hx, ht, hf]
      by_cases hxs : x ∈ s
      · simp only [Set.indicator_of_mem hxs, ContinuousLinearMap.toSpanSingleton_apply,
          one_smul]
      · simp only [Set.indicator_of_notMem hxs, ContinuousLinearMap.toSpanSingleton_apply,
          zero_smul]
    rw [heq]
    exact h f v
  · intro f g hf hg hd hAf hAg
    simpa only [map_add] using congrArg₂ (· + ·) hAf hAg
  · exact isClosed_eq A.continuous B.continuous

/-- Partial Fourier transformation commutes with exchanging the slice order. -/
theorem blockSwapCurrying_fourier
    (u : Lp (Lp E 2 ν) 2 (volume : Measure V)) :
    blockSwapCurrying (𝓕 u) =
      (Lp.fourierTransformₗᵢ V E).toContinuousLinearEquiv.toContinuousLinearMap.compLp
        (blockSwapCurrying u) := by
  let S := (blockSwapCurrying (V := V) (E := E) (ν := ν)).toContinuousLinearEquiv.toContinuousLinearMap
  let F := (Lp.fourierTransformₗᵢ V E).toContinuousLinearEquiv.toContinuousLinearMap
  let Fout := (Lp.fourierTransformₗᵢ V (Lp E 2 ν)).toContinuousLinearEquiv.toContinuousLinearMap
  have heq : S.comp Fout = (F.compLpL 2 ν).comp S := by
    apply continuousLinearMap_ext_scalarTensor
    intro f v
    change blockSwapCurrying (𝓕 ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp f)) =
      F.compLp (blockSwapCurrying ((ContinuousLinearMap.toSpanSingleton ℂ v).compLp f))
    rw [Fourier.fourier_compLp, blockSwapCurrying_tensor, blockSwapCurrying_tensor]
    apply Lp.ext
    filter_upwards [(blockScalarInsertion (𝓕 f)).coeFn_compLp v,
      F.coeFn_compLp ((blockScalarInsertion f).compLp v),
      (blockScalarInsertion f).coeFn_compLp v] with y hl hr hv
    rw [hl, hr, hv]
    change (ContinuousLinearMap.toSpanSingleton ℂ (v y)).compLp (𝓕 f) =
      𝓕 ((ContinuousLinearMap.toSpanSingleton ℂ (v y)).compLp f)
    exact (Fourier.fourier_compLp _ f).symm
  exact congrArg (fun T => T u) heq

/-- The integral of the slice Fourier energies is the outer partial Fourier energy. -/
theorem blockSwapCurrying_fourier_weighted_norm_sq
    (u : Lp (Lp E 2 ν) 2 (volume : Measure V))
    (w : V → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ y, ∫⁻ ξ : V, w ξ *
      ‖(𝓕 (blockSwapCurrying u y) : Lp E 2 volume) ξ‖ₑ ^ 2
      ∂(volume : Measure V) ∂ν) =
      ∫⁻ ξ : V, w ξ * ‖(𝓕 u : Lp (Lp E 2 ν) 2 volume) ξ‖ₑ ^ 2 := by
  rw [← blockSwapCurrying_weighted_norm_sq (𝓕 u) w hw,
    blockSwapCurrying_fourier]
  apply lintegral_congr_ae
  filter_upwards [(Lp.fourierTransformₗᵢ V E).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
    (blockSwapCurrying u)] with y hy
  rw [hy]
  rfl

/-- Target isometries preserve all weighted extended L² masses. -/
theorem blockTargetIsometry_weighted_norm_sq
    {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (A : H ≃ₗᵢ[ℂ] K) (u : Lp H 2 (volume : Measure V))
    (w : V → ℝ≥0∞) :
    (∫⁻ x : V, w x *
      (‖A.toContinuousLinearEquiv.toContinuousLinearMap.compLp u x‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x : V, w x * (‖u x‖₊ : ℝ≥0∞) ^ 2 := by
  apply lintegral_congr_ae
  filter_upwards [A.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp u] with x hx
  rw [hx]
  exact congrArg (fun a : ℝ≥0 => w x * (a : ℝ≥0∞) ^ 2) (A.nnnorm_map (u x))

end LiebThirring.ThermoStability
end
