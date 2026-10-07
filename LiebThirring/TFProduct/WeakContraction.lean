/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.ContractionTests
public import LiebThirring.TFProduct.FieldTensorMap
public import LiebThirring.TFProduct.LocalTestAnnihilator
public import LiebThirring.TFProduct.PartialContraction
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Weak derivatives of partial contractions
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff Topology ENNReal

namespace LiebThirring.TFProduct

open TFCubes

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasureSpace G]
  [FiniteDimensional ℝ G] [BorelSpace G]
  [IsLocallyFiniteMeasure (volume : Measure G)]

/-- Pairing a partial contraction with a retained-variable test is the pairing of the original
state with the literal product test. -/
theorem inner_localTestFunctionL2_partialContraction (Ω : Set E) (Θ : Set G)
    (η : E → ℂ) (ψ : G → ℂ)
    (hηc : HasCompactSupport η) (hηs : ContDiff ℝ ∞ η)
    (hψc : HasCompactSupport ψ) (hψs : ContDiff ℝ ∞ ψ)
    (u : RegionState (E × G) ℂ (Ω ×ˢ Θ)) :
    inner ℂ (localTestFunctionL2 Ω η hηc hηs)
        (partialContraction Ω Θ (localTestFunctionL2 Θ ψ hψc hψs) u) =
      inner ℂ
        (localTestFunctionL2 (Ω ×ˢ Θ) (contractionProductTest η ψ)
          (HasCompactSupport.contractionProductTest hηc hψc) (ContDiff.contractionProductTest hηs hψs)) u := by
  rw [partialContraction, partialContractionCLM]
  change inner ℂ (localTestFunctionL2 Ω η hηc hηs)
      (fieldCoefficient (volume.restrict Ω) (localTestFunctionL2 Θ ψ hψc hψs)
        (l2Curry (productRegionToProd Ω Θ u))) = _
  rw [← inner_fieldTensor]
  let p := localTestFunctionL2 (Ω ×ˢ Θ) (contractionProductTest η ψ)
    (HasCompactSupport.contractionProductTest hηc hψc) (ContDiff.contractionProductTest hηs hψs)
  have htensor : fieldTensor (volume.restrict Ω)
      (localTestFunctionL2 Ω η hηc hηs) (localTestFunctionL2 Θ ψ hψc hψs) =
      l2Curry (productRegionToProd Ω Θ p) := by
    apply Lp.ext
    have htransport := Measure.ae_ae_of_ae_prod (productRegionToProd_ae Ω Θ p)
    have hproduct0 : p =ᵐ[volume.restrict (Ω ×ˢ Θ)] contractionProductTest η ψ :=
      (((ContDiff.contractionProductTest hηs hψs).continuous.memLp_of_hasCompactSupport
          (μ := volume) (p := 2)
        (HasCompactSupport.contractionProductTest hηc hψc)).restrict (Ω ×ˢ Θ)).coeFn_toLp
    have hμ : (volume.restrict Ω).prod (volume.restrict Θ) =
        volume.restrict (Ω ×ˢ Θ) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have heq := congrArg (fun μ : Measure (E × G) =>
      (fun z => p z) =ᵐ[μ] contractionProductTest η ψ) hμ
    have hproductProd : p =ᵐ[(volume.restrict Ω).prod (volume.restrict Θ)]
        contractionProductTest η ψ := heq.mpr hproduct0
    have hproduct := Measure.ae_ae_of_ae_prod hproductProd
    filter_upwards [fieldTensor_ae (volume.restrict Ω)
      (localTestFunctionL2 Ω η hηc hηs) (localTestFunctionL2 Θ ψ hψc hψs),
      l2Curry_ae (productRegionToProd Ω Θ p), htransport, hproduct,
      ((hηs.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hηc).restrict Ω).coeFn_toLp]
      with x hfield hcurry htransportx hproductx hηx'
    rw [hfield]
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (localTestFunctionL2 Ω η hηc hηs x)
        (localTestFunctionL2 Θ ψ hψc hψs), hcurry, htransportx,
      ((hψs.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hψc).restrict Θ).coeFn_toLp,
      hproductx]
      with y hfieldy hcurryy htransporty hψy hprody
    rw [hfieldy, hcurryy, htransporty]
    change
      (localTestFunctionL2 Ω η hηc hηs x) •
          (localTestFunctionL2 Θ ψ hψc hψs y) = p (x, y)
    rw [hprody]
    simp only [localTestFunctionL2]
    rw [hηx', hψy]
    rfl
  rw [htensor]
  exact ((l2CurryLinearIsometry (μ := volume.restrict Ω)
    (ν := volume.restrict Θ) (E := ℂ)).inner_map_map
      (productRegionToProd Ω Θ p) (productRegionToProd Ω Θ u)).trans
        ((productRegionToProd Ω Θ).inner_map_map p u)

/-- Contraction against a compact smooth spectator preserves a retained-variable weak
derivative. -/
theorem hasWeakDerivativeOn_partialContraction_of_compactSmooth
    (Ω : Set E) (Θ : Set G) (v : E) (ψ : G → ℂ)
    (hψc : HasCompactSupport ψ) (hψs : ContDiff ℝ ∞ ψ) (hψΘ : tsupport ψ ⊆ Θ)
    {u g : RegionState (E × G) ℂ (Ω ×ˢ Θ)}
    (hweak : HasWeakDerivativeOn (Ω ×ˢ Θ) (v, 0) u g) :
    HasWeakDerivativeOn Ω v
      (partialContraction Ω Θ (localTestFunctionL2 Θ ψ hψc hψs) u)
      (partialContraction Ω Θ (localTestFunctionL2 Θ ψ hψc hψs) g) := by
  rw [hasWeakDerivativeOn_iff_inner]
  intro η hηc hηs hηΩ
  rw [inner_localTestFunctionL2_partialContraction Ω Θ η ψ hηc hηs hψc hψs]
  let dη : E → ℂ := fun x => fderiv ℝ η x v
  have hdηc : HasCompactSupport dη := hηc.fderiv_apply ℝ v
  have hdηs : ContDiff ℝ ∞ dη :=
    (hηs.fderiv_right (by simp)).clm_apply contDiff_const
  rw [inner_localTestFunctionL2_partialContraction Ω Θ dη ψ hdηc hdηs hψc hψs]
  have hpC : HasCompactSupport (contractionProductTest η ψ) :=
    HasCompactSupport.contractionProductTest hηc hψc
  have hpS : ContDiff ℝ ∞ (contractionProductTest η ψ) :=
    ContDiff.contractionProductTest hηs hψs
  have hpΩ : tsupport (contractionProductTest η ψ) ⊆ Ω ×ˢ Θ :=
    tsupport_contractionProductTest_subset_prod hηΩ hψΘ
  have h := hasWeakDerivativeOn_iff_inner.mp hweak
    (contractionProductTest η ψ) hpC hpS hpΩ
  rw [h]
  congr 2
  apply Lp.ext
  have hdc : HasCompactSupport
      (fun z => fderiv ℝ (contractionProductTest η ψ) z (v, 0)) :=
    hpC.fderiv_apply ℝ (v, 0)
  have hds : ContDiff ℝ ∞
      (fun z => fderiv ℝ (contractionProductTest η ψ) z (v, 0)) :=
    (hpS.fderiv_right (by simp)).clm_apply contDiff_const
  filter_upwards [((hds.continuous.memLp_of_hasCompactSupport hdc).restrict
      (Ω ×ˢ Θ)).coeFn_toLp,
    (((ContDiff.contractionProductTest hdηs hψs).continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.contractionProductTest hdηc hψc)).restrict
        (Ω ×ˢ Θ)).coeFn_toLp]
    with z hz hprod
  simp only [localTestFunctionL2]
  rw [hz, hprod]
  exact fderiv_contractionProductTest_apply η ψ hηs hψs z.1 z.2 v

/-- On an open spectator region, contraction against every local L² spectator preserves a weak
derivative in a retained-variable direction. -/
theorem hasWeakDerivativeOn_partialContraction (Ω : Set E) (Θ : Set G)
    (hΘ : IsOpen Θ) (v : E) (φ : RegionState G ℂ Θ)
    {u g : RegionState (E × G) ℂ (Ω ×ˢ Θ)}
    (hweak : HasWeakDerivativeOn (Ω ×ˢ Θ) (v, 0) u g) :
    HasWeakDerivativeOn Ω v
      (partialContraction Ω Θ φ u) (partialContraction Ω Θ φ g) := by
  rw [hasWeakDerivativeOn_iff_inner]
  intro η hηc hηs hηΩ
  let dη : E → ℂ := fun x => fderiv ℝ η x v
  have hdηc : HasCompactSupport dη := hηc.fderiv_apply ℝ v
  have hdηs : ContDiff ℝ ∞ dη :=
    (hηs.fderiv_right (by simp)).clm_apply contDiff_const
  let Gg := l2Curry (productRegionToProd Ω Θ g)
  let Gu := l2Curry (productRegionToProd Ω Θ u)
  let Aη : RegionState G ℂ Θ →L[ℂ]
      RegionState E (RegionState G ℂ Θ) Ω :=
    fieldTensorRightCLM (volume.restrict Ω) (localTestFunctionL2 Ω η hηc hηs)
  let Adη : RegionState G ℂ Θ →L[ℂ]
      RegionState E (RegionState G ℂ Θ) Ω :=
    fieldTensorRightCLM (volume.restrict Ω) (localTestFunctionL2 Ω dη hdηc hdηs)
  let p : RegionState G ℂ Θ := Aη.adjoint Gg + Adη.adjoint Gu
  have hp : p = 0 := by
    apply localTest_orthogonal_eq_zero hΘ p
    intro ψ hψc hψs hψΘ
    have hc := hasWeakDerivativeOn_partialContraction_of_compactSmooth
      Ω Θ v ψ hψc hψs hψΘ hweak
    have heq := hasWeakDerivativeOn_iff_inner.mp hc η hηc hηs hηΩ
    change inner ℂ (localTestFunctionL2 Θ ψ hψc hψs) p = 0
    simp only [p, inner_add_right]
    rw [ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (fieldTensor (volume.restrict Ω)
        (localTestFunctionL2 Ω η hηc hηs) (localTestFunctionL2 Θ ψ hψc hψs)) Gg +
      inner ℂ (fieldTensor (volume.restrict Ω)
        (localTestFunctionL2 Ω dη hdηc hdηs) (localTestFunctionL2 Θ ψ hψc hψs)) Gu = 0
    rw [inner_fieldTensor, inner_fieldTensor]
    change inner ℂ (localTestFunctionL2 Ω η hηc hηs)
        (partialContraction Ω Θ (localTestFunctionL2 Θ ψ hψc hψs) g) +
      inner ℂ (localTestFunctionL2 Ω dη hdηc hdηs)
        (partialContraction Ω Θ (localTestFunctionL2 Θ ψ hψc hψs) u) = 0
    rw [heq]
    dsimp only [dη]
    exact neg_add_cancel _
  have hall := congrArg (fun q : RegionState G ℂ Θ => inner ℂ φ q) hp
  simp only [p, inner_add_right, inner_zero_right] at hall
  rw [ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right] at hall
  change inner ℂ (fieldTensor (volume.restrict Ω)
      (localTestFunctionL2 Ω η hηc hηs) φ) Gg +
    inner ℂ (fieldTensor (volume.restrict Ω)
      (localTestFunctionL2 Ω dη hdηc hdηs) φ) Gu = 0 at hall
  rw [inner_fieldTensor, inner_fieldTensor] at hall
  change inner ℂ (localTestFunctionL2 Ω η hηc hηs)
      (partialContraction Ω Θ φ g) =
    -inner ℂ (localTestFunctionL2 Ω dη hdηc hdηs)
      (partialContraction Ω Θ φ u)
  exact eq_neg_of_add_eq_zero_left hall

end LiebThirring.TFProduct

end
