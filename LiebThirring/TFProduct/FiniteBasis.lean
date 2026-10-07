/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.HilbertProduct
public import LiebThirring.TFProduct.BasisTransport
public import LiebThirring.TFProduct.DiracBasis
public import LiebThirring.Kinetic.CurryingTransport
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! # Complete bases for finite products of scalar L² spaces

The empty product is the actual mass-one Dirac space. The successor step
uses measure-preserving finite-coordinate splitting and the complete Fubini
product basis, rather than a finite-dimensional tensor construction.
-/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace LiebThirring.TFProduct

variable {X ι : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
  [TopologicalSpace X] [SecondCountableTopology X] [BorelSpace X] [Countable ι]

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

omit [MeasurableSingletonClass X] [TopologicalSpace X] [SecondCountableTopology X]
  [BorelSpace X] in
theorem emptyProduct_identity_preserving (μ : Fin 0 → Measure X) :
    MeasurePreserving (MeasurableEquiv.refl (Fin 0 → X)) (Measure.pi μ)
      (Measure.dirac (fun i => Fin.elim0 i)) := by
  refine ⟨measurable_id, ?_⟩
  change Measure.map id (Measure.pi μ) = _
  rw [Measure.map_id]
  exact Measure.pi_of_empty μ (fun i => Fin.elim0 i)

/-- The complete constant basis of an empty product measure. -/
noncomputable def emptyProductHilbertBasis (μ : Fin 0 → Measure X) :
    HilbertBasis (Fin 0 → ι) ℂ (Lp ℂ 2 (Measure.pi μ)) :=
  mapHilbertBasis (diracHilbertBasis (J := Fin 0 → ι) (fun i => Fin.elim0 i))
    (l2PullbackEquiv (MeasurableEquiv.refl _) (emptyProduct_identity_preserving μ))

omit [Countable ι] [TopologicalSpace X] [SecondCountableTopology X] [BorelSpace X] in
theorem emptyProductHilbertBasis_ae (μ : Fin 0 → Measure X) (k : Fin 0 → ι) :
    emptyProductHilbertBasis μ k =ᵐ[Measure.pi μ] fun _ => (1 : ℂ) := by
  rw [emptyProductHilbertBasis, mapHilbertBasis_apply, diracHilbertBasis_apply]
  exact (l2PullbackEquiv_ae _ _ _).trans
    ((emptyProduct_identity_preserving μ).quasiMeasurePreserving.ae (diracOne_ae _))

/-- Adjoin one scalar factor to a complete finite product basis. -/
noncomputable def finiteProductBasisStep {n : ℕ} (μ : Fin (n + 1) → Measure X)
    [∀ i, SigmaFinite (μ i)]
    (B : HilbertBasis ι ℂ (Lp ℂ 2 (μ 0)))
    (C : HilbertBasis (Fin n → ι) ℂ
      (Lp ℂ 2 (Measure.pi fun j => μ ((0 : Fin (n + 1)).succAbove j)))) :
    HilbertBasis (Fin (n + 1) → ι) ℂ (Lp ℂ 2 (Measure.pi μ)) :=
  reindexHilbertBasis
    (mapHilbertBasis (productHilbertBasis B C)
      (l2PullbackEquiv (MeasurableEquiv.piFinSuccAbove (fun _ => X) 0)
        (measurePreserving_piFinSuccAbove μ 0)))
    (Fin.insertNthEquiv (fun _ : Fin (n + 1) => ι) 0).symm

/-- Iterate the complete product-basis construction over all particles. -/
noncomputable def finiteProductHilbertBasis :
    (n : ℕ) → (μ : Fin n → Measure X) → [∀ i, SigmaFinite (μ i)] →
      ((i : Fin n) → HilbertBasis ι ℂ (Lp ℂ 2 (μ i))) →
      HilbertBasis (Fin n → ι) ℂ (Lp ℂ 2 (Measure.pi μ))
  | 0, μ, _, _ => emptyProductHilbertBasis μ
  | n + 1, μ, _, B => finiteProductBasisStep μ (B 0)
      (finiteProductHilbertBasis n (fun j => μ ((0 : Fin (n + 1)).succAbove j))
        (fun j => B ((0 : Fin (n + 1)).succAbove j)))

omit [MeasurableSingletonClass X] in
/-- The successor basis has the product representative in split coordinates. -/
theorem finiteProductBasisStep_ae {n : ℕ} (μ : Fin (n + 1) → Measure X)
    [∀ i, SigmaFinite (μ i)]
    (B : HilbertBasis ι ℂ (Lp ℂ 2 (μ 0)))
    (C : HilbertBasis (Fin n → ι) ℂ
      (Lp ℂ 2 (Measure.pi fun j => μ ((0 : Fin (n + 1)).succAbove j))))
    (k : Fin (n + 1) → ι) :
    finiteProductBasisStep μ B C k =ᵐ[Measure.pi μ] fun x =>
      B (k 0) (x 0) * C (fun j => k ((0 : Fin (n + 1)).succAbove j))
        (fun j => x ((0 : Fin (n + 1)).succAbove j)) := by
  rw [finiteProductBasisStep, reindexHilbertBasis_apply, mapHilbertBasis_apply]
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
  let he := measurePreserving_piFinSuccAbove μ 0
  let p : ι × (Fin n → ι) := (k 0, fun j => k ((0 : Fin (n + 1)).succAbove j))
  exact (l2PullbackEquiv_ae e he (productHilbertBasis B C p)).trans
    (he.quasiMeasurePreserving.ae (productHilbertBasis_ae B C p))

/-- Every finite product basis vector is the literal product of factor representatives. -/
theorem finiteProductHilbertBasis_ae (n : ℕ) (μ : Fin n → Measure X)
    [∀ i, SigmaFinite (μ i)] (B : (i : Fin n) → HilbertBasis ι ℂ (Lp ℂ 2 (μ i)))
    (k : Fin n → ι) :
    finiteProductHilbertBasis n μ B k =ᵐ[Measure.pi μ]
      fun x => ∏ i : Fin n, B i (k i) (x i) := by
  induction n with
  | zero => exact emptyProductHilbertBasis_ae μ k
  | succ n ih =>
    let μ' : Fin n → Measure X := fun j => μ ((0 : Fin (n + 1)).succAbove j)
    let B' : (j : Fin n) → HilbertBasis ι ℂ (Lp ℂ 2 (μ' j)) :=
      fun j => B ((0 : Fin (n + 1)).succAbove j)
    let k' : Fin n → ι := fun j => k ((0 : Fin (n + 1)).succAbove j)
    have ht := ih μ' B' k'
    have hp := finiteProductBasisStep_ae μ (B 0)
      (finiteProductHilbertBasis n μ' B') k
    have hs : ∀ᵐ z ∂(μ 0).prod (Measure.pi μ'),
        finiteProductHilbertBasis n μ' B' k' z.2 = ∏ j, B' j (k' j) (z.2 j) :=
      Measure.quasiMeasurePreserving_snd.ae ht
    have hs' := (measurePreserving_piFinSuccAbove μ 0).quasiMeasurePreserving.ae hs
    filter_upwards [hp, hs'] with x hx hrest
    change finiteProductBasisStep μ (B 0) (finiteProductHilbertBasis n μ' B') k x = _
    change finiteProductHilbertBasis n μ' B' (fun j => k ((0 : Fin (n + 1)).succAbove j))
        (fun j => x ((0 : Fin (n + 1)).succAbove j)) =
      ∏ j, B ((0 : Fin (n + 1)).succAbove j) (k ((0 : Fin (n + 1)).succAbove j))
        (x ((0 : Fin (n + 1)).succAbove j)) at hrest
    rw [hx, hrest, Fin.prod_univ_succAbove _ 0]


end LiebThirring.TFProduct
end
