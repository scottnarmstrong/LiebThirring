/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeBasisTriple
public import LiebThirring.TFCubes.CubeConfiguration

@[expose] public section

/-! # Coordinate-indexed cube Hilbert bases

This module reindexes the iterated three-factor construction by `Fin 3` and
transports product bases from coordinate space to the physical cube.
-/

namespace LiebThirring.TFCubes

variable {ι ι' E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Reindex a Hilbert basis along an equivalence of index types. -/
noncomputable def reindexHilbertBasis (B : HilbertBasis ι ℂ E) (e : ι ≃ ι') :
    HilbertBasis ι' ℂ E :=
  HilbertBasis.mkOfOrthogonalEqBot
    (B.orthonormal.comp e.symm e.symm.injective) (by
      have hrange : Set.range (B ∘ e.symm) = Set.range B := by
        exact e.symm.surjective.range_comp B
      rw [hrange, ← Submodule.orthogonal_closure, B.dense_span,
        Submodule.top_orthogonal_eq_bot])

@[simp]
theorem reindexHilbertBasis_apply (B : HilbertBasis ι ℂ E) (e : ι ≃ ι') (i : ι') :
    reindexHilbertBasis B e i = B (e.symm i) := by
  rw [reindexHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]
  rfl

/-- Transport a Hilbert basis through a linear isometric equivalence. -/
noncomputable def mapHilbertBasis {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F]
    (U : E ≃ₗᵢ[ℂ] F) (B : HilbertBasis ι ℂ E) : HilbertBasis ι ℂ F :=
  HilbertBasis.ofRepr (U.symm.trans B.repr)

omit [CompleteSpace E] in
@[simp]
theorem mapHilbertBasis_apply {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F]
    (U : E ≃ₗᵢ[ℂ] F) (B : HilbertBasis ι ℂ E) (i : ι) :
    mapHilbertBasis U B i = U (B i) := by
  classical
  apply (mapHilbertBasis U B).repr.injective
  rw [HilbertBasis.repr_self]
  symm
  change (U.symm.trans B.repr) (U (B i)) = _
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply,
    B.repr_self]

/-- Reindex three coordinates by the literal `Fin 3` function type. -/
def finThreeEquivTriple (ι : Type*) : (Fin 3 → ι) ≃ ((ι × ι) × ι) where
  toFun k := ((k 0, k 1), k 2)
  invFun p := fun i => Fin.cases p.1.1 (fun j => Fin.cases p.1.2 (fun _ => p.2) j) i
  left_inv k := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨⟨a, b⟩, c⟩; rfl

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- A homogeneous three-coordinate product basis, indexed by `Fin 3 → ι`. -/
noncomputable def hilbertBasisFinThreeProduct (B : HilbertBasis ι ℂ (Lp ℂ 2 μ)) :
    HilbertBasis (Fin 3 → ι) ℂ (Lp ℂ 2 ((μ.prod μ).prod μ)) :=
  reindexHilbertBasis (hilbertBasisTripleProduct B B B) (finThreeEquivTriple ι).symm

@[simp]
theorem hilbertBasisFinThreeProduct_apply (B : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (k : Fin 3 → ι) :
    hilbertBasisFinThreeProduct B k =
      lpProd (lpProd (B (k 0)) (B (k 1))) (B (k 2)) := by
  rw [hilbertBasisFinThreeProduct, reindexHilbertBasis_apply,
    hilbertBasisTripleProduct_apply]
  rfl

/-- Canonical measurable identification of a left-associated triple product
with a function on `Fin 3`. -/
noncomputable def nestedTripleMeasurableEquiv (X : Type*) [MeasurableSpace X] :
    ((X × X) × X) ≃ᵐ (Fin 3 → X) :=
  (MeasurableEquiv.prodAssoc : ((X × X) × X) ≃ᵐ X × (X × X)).trans <|
    ((MeasurableEquiv.refl X).prodCongr
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => X)).symm).trans <|
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => X) 0).symm

@[simp]
theorem nestedTripleMeasurableEquiv_symm_apply (X : Type*) [MeasurableSpace X]
    (x : Fin 3 → X) :
    (nestedTripleMeasurableEquiv X).symm x = ((x 0, x 1), x 2) := rfl

theorem measurePreserving_nestedTripleMeasurableEquiv
    (X : Type*) [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (nestedTripleMeasurableEquiv X) ((μ.prod μ).prod μ)
      (Measure.pi fun _ : Fin 3 => μ) := by
  let e₁ : ((X × X) × X) ≃ᵐ X × (X × X) := MeasurableEquiv.prodAssoc
  let e₂ : X × (X × X) ≃ᵐ X × (Fin 2 → X) :=
    (MeasurableEquiv.refl X).prodCongr
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => X)).symm
  let e₃ : (X × (Fin 2 → X)) ≃ᵐ (Fin 3 → X) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => X) 0).symm
  have h₁ : MeasurePreserving e₁ ((μ.prod μ).prod μ) (μ.prod (μ.prod μ)) :=
    measurePreserving_prodAssoc μ μ μ
  have h₂ : MeasurePreserving e₂ (μ.prod (μ.prod μ))
      (μ.prod (Measure.pi fun _ : Fin 2 => μ)) :=
    MeasurePreserving.prod (MeasurePreserving.id μ)
      ((measurePreserving_piFinTwo (fun _ : Fin 2 => μ)).symm _)
  have h₃ : MeasurePreserving e₃ (μ.prod (Measure.pi fun _ : Fin 2 => μ))
      (Measure.pi fun _ : Fin 3 => μ) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) 0).symm _
  simpa only [nestedTripleMeasurableEquiv, e₁, e₂, e₃,
    MeasurableEquiv.coe_trans, Function.comp_def] using h₃.comp (h₂.comp h₁)

/-- The homogeneous three-coordinate product basis on the actual `Fin 3`
product measure. -/
noncomputable def hilbertBasisPiThreeProduct (B : HilbertBasis ι ℂ (Lp ℂ 2 μ)) :
    HilbertBasis (Fin 3 → ι) ℂ (Lp ℂ 2 (Measure.pi fun _ : Fin 3 => μ)) :=
  mapHilbertBasis
    (cubeMeasureL2Equiv (nestedTripleMeasurableEquiv X) _ _
      (measurePreserving_nestedTripleMeasurableEquiv X μ))
    (hilbertBasisFinThreeProduct B)

theorem hilbertBasisPiThreeProduct_ae (B : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (k : Fin 3 → ι) :
    hilbertBasisPiThreeProduct B k =ᵐ[Measure.pi fun _ : Fin 3 => μ]
      fun x => ∏ i : Fin 3, B (k i) (x i) := by
  let e := nestedTripleMeasurableEquiv X
  let hp := measurePreserving_nestedTripleMeasurableEquiv X μ
  let w := hilbertBasisFinThreeProduct B k
  have hw : w =ᵐ[(μ.prod μ).prod μ] fun y =>
      (B (k 0) y.1.1 * B (k 1) y.1.2) * B (k 2) y.2 := by
    have ho := lpProd_coeFn (lpProd (B (k 0)) (B (k 1))) (B (k 2))
    have hi := (Measure.quasiMeasurePreserving_fst (μ := μ.prod μ) (ν := μ)).ae
      (lpProd_coeFn (B (k 0)) (B (k 1)))
    filter_upwards [hilbertBasisFinThreeProduct_apply B k ▸ ho, hi] with y ho hi
    rw [ho, hi]
  have ht := Lp.coeFn_compMeasurePreserving w (hp.symm e)
  filter_upwards [ht, (hp.symm e).quasiMeasurePreserving.ae hw] with x ht hw
  rw [hilbertBasisPiThreeProduct, mapHilbertBasis_apply]
  change Lp.compMeasurePreserving e.symm (hp.symm e) w x = _
  rw [ht]
  simp only [Function.comp_apply]
  rw [hw]
  rw [nestedTripleMeasurableEquiv_symm_apply]
  rw [Fin.prod_univ_three]

variable {ι₀ ι₁ ι₂ : Type*}

/-- A heterogeneous three-coordinate product basis on the actual coordinate
product measure.  The three factors may have different index types and bases. -/
noncomputable def hilbertBasisPiThreeProductHet
    (B₀ : HilbertBasis ι₀ ℂ (Lp ℂ 2 μ))
    (B₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 μ))
    (B₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 μ)) :
    HilbertBasis ((ι₀ × ι₁) × ι₂) ℂ
      (Lp ℂ 2 (Measure.pi fun _ : Fin 3 => μ)) :=
  mapHilbertBasis
    (cubeMeasureL2Equiv (nestedTripleMeasurableEquiv X) _ _
      (measurePreserving_nestedTripleMeasurableEquiv X μ))
    (hilbertBasisTripleProduct B₀ B₁ B₂)

theorem hilbertBasisPiThreeProductHet_ae
    (B₀ : HilbertBasis ι₀ ℂ (Lp ℂ 2 μ))
    (B₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 μ))
    (B₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 μ)) (k : ((ι₀ × ι₁) × ι₂)) :
    hilbertBasisPiThreeProductHet B₀ B₁ B₂ k
      =ᵐ[Measure.pi fun _ : Fin 3 => μ] fun x =>
        (B₀ k.1.1 (x 0) * B₁ k.1.2 (x 1)) * B₂ k.2 (x 2) := by
  let e := nestedTripleMeasurableEquiv X
  let hp := measurePreserving_nestedTripleMeasurableEquiv X μ
  let w := hilbertBasisTripleProduct B₀ B₁ B₂ k
  have hw : w =ᵐ[(μ.prod μ).prod μ] fun y =>
      (B₀ k.1.1 y.1.1 * B₁ k.1.2 y.1.2) * B₂ k.2 y.2 := by
    have ho := lpProd_coeFn (lpProd (B₀ k.1.1) (B₁ k.1.2)) (B₂ k.2)
    have hi := (Measure.quasiMeasurePreserving_fst (μ := μ.prod μ) (ν := μ)).ae
      (lpProd_coeFn (B₀ k.1.1) (B₁ k.1.2))
    filter_upwards [hilbertBasisTripleProduct_apply B₀ B₁ B₂ k ▸ ho, hi] with y ho hi
    rw [ho, hi]
  have ht := Lp.coeFn_compMeasurePreserving w (hp.symm e)
  filter_upwards [ht, (hp.symm e).quasiMeasurePreserving.ae hw] with x ht hw
  rw [hilbertBasisPiThreeProductHet, mapHilbertBasis_apply]
  change Lp.compMeasurePreserving e.symm (hp.symm e) w x = _
  rw [ht]
  simp only [Function.comp_apply]
  rw [hw]
  rw [nestedTripleMeasurableEquiv_symm_apply]

end LiebThirring.TFCubes

end



