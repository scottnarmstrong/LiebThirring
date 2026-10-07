/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.FiniteBasis
public import LiebThirring.TFProduct.AssignmentMeasure
public import LiebThirring.TFSectors.SpectralInput

/-! # Complete product bases on physical assignment cells

Only the actual one-particle scalar cube bases are inputs. The configuration
measure, finite particle product, global spin factor, and mode reindexing are
constructed here, including the zero-particle case.
-/

@[expose] public section
open MeasureTheory
namespace LiebThirring.TFProduct
open TFCubes TFSectors

/-- Separate all spatial frequencies from all particle spin labels. -/
def productModeIndexEquiv (N q : ℕ) :
    (Fin N → TFLattice.ModeIndex q) ≃ ((Fin N → Fin 3 → ℕ) × SpinLabels N q) where
  toFun k := (fun i => (k i).1, fun i => (k i).2)
  invFun p := fun i => (p.1 i, p.2 i)
  left_inv k := by funext i; exact Prod.eta _
  right_inv p := by cases p; rfl

/-- The complete scalar basis pulled back from the finite product of physical cubes. -/
noncomputable def scalarAssignmentHilbertBasis {N : ℕ}
    (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex)
    (B : (i : Fin N) → HilbertBasis (Fin 3 → ℕ) ℂ
      (RegionState Position ℂ (cubeInterior (latticeCorner ℓ.val (b i)) ℓ))) :
    HilbertBasis (Fin N → Fin 3 → ℕ) ℂ
      (RegionState (Configuration N) ℂ (openAssignmentCell ℓ.val b)) :=
  mapHilbertBasis (finiteProductHilbertBasis N
    (fun i => volume.restrict (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)) B)
    (l2PullbackEquiv (particlePositionsEquiv N)
      (measurePreserving_particlePositions_restrict_openAssignmentCell ℓ b))

theorem scalarAssignmentHilbertBasis_ae {N : ℕ}
    (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex)
    (B : (i : Fin N) → HilbertBasis (Fin 3 → ℕ) ℂ
      (RegionState Position ℂ (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)))
    (k : Fin N → Fin 3 → ℕ) :
    scalarAssignmentHilbertBasis ℓ b B k =ᵐ[volume.restrict (openAssignmentCell ℓ.val b)]
      fun x => ∏ i : Fin N, B i (k i) (particlePosition x i) := by
  rw [scalarAssignmentHilbertBasis, mapHilbertBasis_apply]
  let μ : Fin N → Measure Position :=
    fun i => volume.restrict (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)
  let e := particlePositionsEquiv N
  let he := measurePreserving_particlePositions_restrict_openAssignmentCell ℓ b
  exact (l2PullbackEquiv_ae e he (finiteProductHilbertBasis N μ B k)).trans
    (he.quasiMeasurePreserving.ae (finiteProductHilbertBasis_ae N μ B k))

/-- Attach the standard basis of the complete global spin Hilbert space. -/
noncomputable def assignmentHilbertBasisOfScalarBases {N q : ℕ}
    (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex)
    (B : (i : Fin N) → HilbertBasis (Fin 3 → ℕ) ℂ
      (RegionState Position ℂ (cubeInterior (latticeCorner ℓ.val (b i)) ℓ))) :
    HilbertBasis (Fin N → TFLattice.ModeIndex q) ℂ
      (ConfigurationRegionState N q (openAssignmentCell ℓ.val b)) :=
  reindexHilbertBasis
    (fieldHilbertBasis (volume.restrict (openAssignmentCell ℓ.val b))
      (scalarAssignmentHilbertBasis ℓ b B)
      (EuclideanSpace.basisFun (SpinLabels N q) ℂ).toHilbertBasis)
    (productModeIndexEquiv N q)

/-- Literal scalar products occupy exactly the prescribed global spin component. -/
theorem assignmentHilbertBasisOfScalarBases_ae {N q : ℕ}
    (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex)
    (B : (i : Fin N) → HilbertBasis (Fin 3 → ℕ) ℂ
      (RegionState Position ℂ (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)))
    (k : Fin N → TFLattice.ModeIndex q) :
    assignmentHilbertBasisOfScalarBases ℓ b B k =ᵐ[
      volume.restrict (openAssignmentCell ℓ.val b)] fun x =>
      EuclideanSpace.single (fun i => (k i).2)
        (∏ i : Fin N, B i (k i).1 (particlePosition x i)) := by
  classical
  rw [assignmentHilbertBasisOfScalarBases, reindexHilbertBasis_apply,
    fieldHilbertBasis_apply]
  have hs := scalarAssignmentHilbertBasis_ae ℓ b B (fun i => (k i).1)
  filter_upwards [fieldTensor_ae (volume.restrict (openAssignmentCell ℓ.val b))
    (scalarAssignmentHilbertBasis ℓ b B (fun i => (k i).1))
    ((EuclideanSpace.basisFun (SpinLabels N q) ℂ).toHilbertBasis (fun i => (k i).2)),
    hs] with x hx hscalar
  change fieldTensor (volume.restrict (openAssignmentCell ℓ.val b))
    (scalarAssignmentHilbertBasis ℓ b B (fun i => (k i).1))
    ((EuclideanSpace.basisFun (SpinLabels N q) ℂ).toHilbertBasis (fun i => (k i).2)) x = _
  rw [hx, hscalar]
  simp only [OrthonormalBasis.coe_toHilbertBasis, EuclideanSpace.basisFun_apply]
  apply PiLp.ext
  intro s
  by_cases h : s = fun i => (k i).2
  · simp only [PiLp.smul_apply, PiLp.single_apply, h, ite_true, mul_one,
      smul_eq_mul]
  · simp only [PiLp.smul_apply, PiLp.single_apply, h, ite_false, mul_zero,
      smul_eq_mul]

end LiebThirring.TFProduct
end
