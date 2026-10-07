/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.ScalarAssignmentEnergy
public import LiebThirring.TFProduct.FieldForm
public import LiebThirring.TFProduct.NeumannBasis

/-!
# Assembly of the Neumann product spectral data

One-particle scalar cube bases and their genuine weak-form identities are
tensorized over particles and then over the finite spin Hilbert space.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace LiebThirring.TFProduct

open TFCubes TFSectors Sobolev TFLattice

/-- The spin-valued assignment form diagonalizes in the constructed product
basis. -/
theorem hasSum_assignment_form_of_scalarCubeBases {N q : ℕ}
    (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex)
    (B : (i : Fin N) → HilbertBasis (Fin 3 → ℕ) ℂ
      (RegionState Position ℂ (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)))
    (hfactor : ∀ i
      (u : RegionState Position ℂ (cubeInterior (latticeCorner ℓ.val (b i)) ℓ))
      (g : Fin 3 → RegionState Position ℂ
        (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)),
      (∀ a, HasWeakDerivativeOn (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)
        (EuclideanSpace.basisFun (Fin 3) ℝ a) u (g a)) →
      HasSum (fun k => scalarCubeEigenvalue ℓ k * ‖(B i).repr u k‖ ^ 2)
        (∑ a : Fin 3, ‖g a‖ ^ 2))
    (v : localFormGraph N q (openAssignmentCell ℓ.val b)) :
    HasSum (fun k : Fin N → ModeIndex q => productEigenvalue ℓ k *
      ‖(assignmentHilbertBasisOfScalarBases ℓ b B).repr
        ((v : LocalFormGraphAmbient N q (openAssignmentCell ℓ.val b)) none) k‖ ^ 2)
      (localGradientEnergy
        (v : LocalFormGraphAmbient N q (openAssignmentCell ℓ.val b))) := by
  let S := scalarAssignmentHilbertBasis ℓ b B
  let C := (EuclideanSpace.basisFun (SpinLabels N q) ℂ).toHilbertBasis
  have hs := hasSum_weighted_fieldForm (openAssignmentCell ℓ.val b) S C
    (fun k => ∑ i : Fin N, scalarCubeEigenvalue ℓ (k i))
    (fun k => Finset.sum_nonneg fun i _ => scalarCubeEigenvalue_nonneg ℓ (k i))
    (fun ia : Fin N × Fin 3 => coordinateVector ia)
    (fun u g hw => hasSum_scalarAssignment_energy ℓ b B hfactor u g hw)
    ((v : LocalFormGraphAmbient N q (openAssignmentCell ℓ.val b)) none)
    (fun ia => (v : LocalFormGraphAmbient N q (openAssignmentCell ℓ.val b)) (some ia))
    v.property
  have ht := (productModeIndexEquiv N q).hasSum_iff.mpr hs
  apply ht.congr_fun
  intro k
  rw [productEigenvalue_eq_sum_scalar]
  simp only [Function.comp_apply, HilbertBasis.repr_apply_apply,
    assignmentHilbertBasisOfScalarBases, reindexHilbertBasis_apply]
  rfl

/-- Construct the exact conditional product spectral datum from genuine
one-particle scalar cube bases and form identities. -/
noncomputable def neumannProductSpectralData_of_scalarCubeBases {N q : ℕ}
    (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex)
    (B : (i : Fin N) → HilbertBasis (Fin 3 → ℕ) ℂ
      (RegionState Position ℂ (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)))
    (hB : ∀ i k, B i k =ᵐ[
      volume.restrict (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)]
        neumannCubeSpatialMode ℓ (latticeCorner ℓ.val (b i)) k)
    (hfactor : ∀ i
      (u : RegionState Position ℂ (cubeInterior (latticeCorner ℓ.val (b i)) ℓ))
      (g : Fin 3 → RegionState Position ℂ
        (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)),
      (∀ a, HasWeakDerivativeOn (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)
        (EuclideanSpace.basisFun (Fin 3) ℝ a) u (g a)) →
      HasSum (fun k => scalarCubeEigenvalue ℓ k * ‖(B i).repr u k‖ ^ 2)
        (∑ a : Fin 3, ‖g a‖ ^ 2)) :
    NeumannProductSpectralData N q ℓ b where
  basis := assignmentHilbertBasisOfScalarBases ℓ b B
  basis_ae := assignmentHilbertBasisOfScalarBases_neumann_ae ℓ b B hB
  diagonal := hasSum_assignment_form_of_scalarCubeBases ℓ b B hfactor

end LiebThirring.TFProduct

end
