/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeBasisProduct

/-! # Orthonormal product families in scalar L² -/

@[expose] public section

open MeasureTheory

namespace LiebThirring.TFCubes

variable {X Y ι κ : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]

/-- The pointwise product family associated with two Hilbert bases. -/
noncomputable def hilbertBasisProductFamily
    (B : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (C : HilbertBasis κ ℂ (Lp ℂ 2 ν)) :
    ι × κ → Lp ℂ 2 (μ.prod ν) :=
  fun p => lpProd (B p.1) (C p.2)

theorem orthonormal_hilbertBasisProductFamily
    (B : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (C : HilbertBasis κ ℂ (Lp ℂ 2 ν)) :
    Orthonormal ℂ (hilbertBasisProductFamily B C) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i, j⟩ ⟨i', j'⟩
  rw [show inner ℂ (hilbertBasisProductFamily B C (i, j))
      (hilbertBasisProductFamily B C (i', j')) =
      inner ℂ (B i) (B i') * inner ℂ (C j) (C j') by
    exact inner_lpProd _ _ _ _]
  rw [orthonormal_iff_ite.mp B.orthonormal i i',
    orthonormal_iff_ite.mp C.orthonormal j j']
  by_cases hi : i = i' <;> by_cases hj : j = j' <;> simp [hi, hj]

private theorem continuousLinearMap_eq_zero_of_hilbertBasis
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (B : HilbertBasis ι ℂ E) (L : E →L[ℂ] F) (hL : ∀ i, L (B i) = 0) : L = 0 := by
  ext x
  have hs := (B.hasSum_repr x).mapL L
  have hz : HasSum (fun _i : ι => (0 : F)) 0 := hasSum_zero
  apply hs.unique
  convert hz using 1
  funext i
  simp only [map_smul, hL, smul_zero]

/-- Orthogonality to all product basis vectors extends to products of
arbitrary vectors in the two factor spaces. -/
theorem inner_lpProd_eq_zero_of_basis
    (B : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (C : HilbertBasis κ ℂ (Lp ℂ 2 ν))
    (u : Lp ℂ 2 (μ.prod ν))
    (hu : ∀ i j, inner ℂ (lpProd (B i) (C j)) u = 0) :
    ∀ f g, inner ℂ (lpProd f g) u = 0 := by
  intro f g
  let Ru : Lp ℂ 2 (μ.prod ν) →L[ℂ] ℂ := innerSL ℂ u
  have hright (j : κ) : Ru.comp (lpProdRight (C j)) = 0 := by
    apply continuousLinearMap_eq_zero_of_hilbertBasis B
    intro i
    change inner ℂ u (lpProd (B i) (C j)) = 0
    exact inner_eq_zero_symm.mpr (hu i j)
  have hleft : (Ru.comp (lpProdLeft f)) = 0 := by
    apply continuousLinearMap_eq_zero_of_hilbertBasis C
    intro j
    have hj := DFunLike.congr_fun (hright j) f
    change inner ℂ u (lpProd f (C j)) = 0 at hj ⊢
    exact hj
  have := DFunLike.congr_fun hleft g
  have he : inner ℂ u (lpProd f g) = 0 := by
    change inner ℂ u (lpProd f g) = 0 at this
    exact this
  exact inner_eq_zero_symm.mp he

omit [SigmaFinite μ] in
theorem inner_lpProd_indicator_eq_setIntegral [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set X} {t : Set Y} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (u : Lp ℂ 2 (μ.prod ν)) :
    inner ℂ
      (lpProd (indicatorConstLp 2 hs (by finiteness) (1 : ℂ))
        (indicatorConstLp 2 ht (by finiteness) (1 : ℂ))) u =
      ∫ z in s ×ˢ t, u z ∂μ.prod ν := by
  rw [L2.inner_def, ← integral_indicator (hs.prod ht)]
  apply integral_congr_ae
  filter_upwards [lpProd_coeFn
      (indicatorConstLp 2 hs (by finiteness) (1 : ℂ))
      (indicatorConstLp 2 ht (by finiteness) (1 : ℂ)),
    Measure.quasiMeasurePreserving_fst.ae
      (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := by finiteness) (c := (1 : ℂ))),
    Measure.quasiMeasurePreserving_snd.ae
      (indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := by finiteness) (c := (1 : ℂ)))] with z hp hsf htf
  rw [hp]
  simp only [RCLike.inner_apply', hsf, htf]
  by_cases hzs : z.1 ∈ s <;> by_cases hzt : z.2 ∈ t <;>
    simp [Set.indicator, hzs, hzt]

theorem eq_zero_of_inner_hilbertBasisProductFamily [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (C : HilbertBasis κ ℂ (Lp ℂ 2 ν))
    (u : Lp ℂ 2 (μ.prod ν))
    (hu : ∀ p, inner ℂ (hilbertBasisProductFamily B C p) u = 0) : u = 0 := by
  have hall : ∀ f g, inner ℂ (lpProd f g) u = 0 :=
    inner_lpProd_eq_zero_of_basis B C u fun i j => hu (i, j)
  have uint : Integrable u (μ.prod ν) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      integrableOn_Lp_of_measure_ne_top (s := Set.univ) u
        fact_one_le_two_ennreal.elim (by finiteness)
  have hrect {s : Set X} (hs : MeasurableSet s) {t : Set Y} (ht : MeasurableSet t) :
      ∫ z in s ×ˢ t, u z ∂μ.prod ν = 0 := by
    rw [← inner_lpProd_indicator_eq_setIntegral hs ht u]
    exact hall _ _
  have hset : ∀ s : Set (X × Y), MeasurableSet s → ∫ z in s, u z ∂μ.prod ν = 0 := by
    intro s hs
    induction s, hs using MeasurableSpace.induction_on_inter
      generateFrom_prod.symm isPiSystem_prod with
    | empty => simp
    | basic s hs =>
        obtain ⟨a, ha, b, hb, rfl⟩ := hs
        exact hrect ha hb
    | compl s hs ih =>
        have huniv := hrect (s := Set.univ) MeasurableSet.univ
          (t := Set.univ) MeasurableSet.univ
        rw [Set.univ_prod_univ] at huniv
        have hadd := integral_add_compl hs uint
        simp only [Measure.restrict_univ] at huniv
        rw [ih, zero_add, huniv] at hadd
        exact hadd
    | iUnion f hdis hmeas ih =>
        rw [integral_iUnion hmeas hdis uint.integrableOn]
        simp only [ih, tsum_zero]
  have huae := uint.ae_eq_zero_of_forall_setIntegral_eq_zero
    (fun s hs _ => hset s hs)
  exact Lp.ext (huae.trans (Lp.coeFn_zero ℂ 2 (μ.prod ν)).symm)

theorem hilbertBasisProductFamily_orthogonal_eq_bot [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (C : HilbertBasis κ ℂ (Lp ℂ 2 ν)) :
    (Submodule.span ℂ (Set.range (hilbertBasisProductFamily B C)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  rw [Submodule.mem_bot]
  apply eq_zero_of_inner_hilbertBasisProductFamily B C u
  rintro p
  exact Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self p)) hu

/-- The Hilbert basis obtained by taking pointwise products of two scalar L²
Hilbert bases. -/
noncomputable def hilbertBasisProduct [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (C : HilbertBasis κ ℂ (Lp ℂ 2 ν)) :
    HilbertBasis (ι × κ) ℂ (Lp ℂ 2 (μ.prod ν)) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_hilbertBasisProductFamily B C)
    (hilbertBasisProductFamily_orthogonal_eq_bot B C)

@[simp]
theorem hilbertBasisProduct_apply [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (C : HilbertBasis κ ℂ (Lp ℂ 2 ν)) (p : ι × κ) :
    hilbertBasisProduct B C p = lpProd (B p.1) (C p.2) := by
  rw [hilbertBasisProduct, HilbertBasis.coe_mkOfOrthogonalEqBot]
  rfl

end LiebThirring.TFCubes

end


