/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.SelectedBasis
public import LiebThirring.TFProduct.RetainedEnergy
public import LiebThirring.TFProduct.ScalarEigenvalue

/-! # Physical scalar energy of one selected particle

The only spectral premise is the one-particle cube form identity. Spatial
transport, all spectator contractions, completeness, and the nonnegative
sum interchange are internal theorems.
-/

@[expose] public section
open MeasureTheory
namespace LiebThirring.TFProduct
open TFCubes TFSectors Sobolev

/-- Tensorize one cube's physical Neumann form over all other particle positions. -/
theorem hasSum_scalarAssignment_particleEnergy {n : ℕ} (i : Fin (n + 1))
    (ℓ : {x : ℝ // 0 < x}) (b : Fin (n + 1) → LatticeIndex)
    (B : (j : Fin (n + 1)) → HilbertBasis (Fin 3 → ℕ) ℂ
      (RegionState Position ℂ (cubeInterior (latticeCorner ℓ.val (b j)) ℓ)))
    (hfactor : ∀ (u : RegionState Position ℂ (cubeInterior (latticeCorner ℓ.val (b i)) ℓ))
      (g : Fin 3 → RegionState Position ℂ (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)),
      (∀ a, HasWeakDerivativeOn (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)
        (EuclideanSpace.basisFun (Fin 3) ℝ a) u (g a)) →
      HasSum (fun k => scalarCubeEigenvalue ℓ k * ‖(B i).repr u k‖ ^ 2)
        (∑ a : Fin 3, ‖g a‖ ^ 2))
    (u : RegionState (Configuration (n + 1)) ℂ (openAssignmentCell ℓ.val b))
    (g : Fin 3 → RegionState (Configuration (n + 1)) ℂ (openAssignmentCell ℓ.val b))
    (hweak : ∀ a, HasWeakDerivativeOn (openAssignmentCell ℓ.val b)
      (coordinateVector (i, a)) u (g a)) :
    HasSum (fun k : Fin (n + 1) → Fin 3 → ℕ => scalarCubeEigenvalue ℓ (k i) *
      ‖(scalarAssignmentHilbertBasis ℓ b B).repr u k‖ ^ 2) (∑ a : Fin 3, ‖g a‖ ^ 2) := by
  let br : Fin n → LatticeIndex := fun j => b (i.succAbove j)
  let Br : (j : Fin n) → HilbertBasis (Fin 3 → ℕ) ℂ
      (RegionState Position ℂ (cubeInterior (latticeCorner ℓ.val (br j)) ℓ)) :=
    fun j => B (i.succAbove j)
  let U := selectedParticleL2Equiv i ℓ b
  have hs := hasSum_productRegion_retainedEnergy
    (cubeInterior (latticeCorner ℓ.val (b i)) ℓ) (openAssignmentCell ℓ.val br)
    (isOpen_openAssignmentCell ℓ.val br) (B i) (scalarAssignmentHilbertBasis ℓ br Br)
    (scalarCubeEigenvalue ℓ) (scalarCubeEigenvalue_nonneg ℓ)
    (EuclideanSpace.basisFun (Fin 3) ℝ) hfactor (U u) (fun a => U (g a))
    (fun a => selectedParticleL2Equiv_hasWeakDerivative i ℓ b a (hweak a))
  let e : (Fin (n + 1) → Fin 3 → ℕ) ≃ ((Fin 3 → ℕ) × (Fin n → Fin 3 → ℕ)) :=
    (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Fin 3 → ℕ) i).symm
  have ht := e.hasSum_iff.mpr hs
  have hresult : HasSum
      (fun k : Fin (n + 1) → Fin 3 → ℕ => scalarCubeEigenvalue ℓ (k i) *
        ‖(scalarAssignmentHilbertBasis ℓ b B).repr u k‖ ^ 2)
      (∑ a : Fin 3, ‖U (g a)‖ ^ 2) := by
    apply ht.congr_fun
    intro k
    symm
    change scalarCubeEigenvalue ℓ (k i) *
      ‖(productRegionHilbertBasis (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)
        (openAssignmentCell ℓ.val br) (B i) (scalarAssignmentHilbertBasis ℓ br Br)).repr
          (U u) (k i, fun j => k (i.succAbove j))‖ ^ 2 = _
    rw [← scalarAssignmentHilbertBasis_repr_eq_productRegion_repr i ℓ b B u k]
  simpa only [U, LinearIsometryEquiv.norm_map] using hresult

end LiebThirring.TFProduct
end
