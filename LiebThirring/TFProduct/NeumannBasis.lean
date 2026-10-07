/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.CellBasis
public import LiebThirring.TFProduct.ModeNormalization

/-! # Literal Neumann representatives of the complete particle product basis

The sole input is a complete scalar basis on each physical one-particle cube,
with the representative statement exposed by TF3d. All particle and spin
tensorization and the agreement with the sector modes are proved here.
-/

@[expose] public section
open MeasureTheory
namespace LiebThirring.TFProduct
open TFCubes TFSectors

/-- The constructed complete product basis has exactly the sector mode representatives. -/
theorem assignmentHilbertBasisOfScalarBases_neumann_ae {N q : ℕ}
    (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex)
    (B : (i : Fin N) → HilbertBasis (Fin 3 → ℕ) ℂ
      (RegionState Position ℂ (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)))
    (hB : ∀ i k, B i k =ᵐ[volume.restrict (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)]
      neumannCubeSpatialMode ℓ (latticeCorner ℓ.val (b i)) k)
    (k : Fin N → TFLattice.ModeIndex q) :
    assignmentHilbertBasisOfScalarBases ℓ b B k =ᵐ[
      volume.restrict (openAssignmentCell ℓ.val b)] neumannProductMode ℓ b k := by
  let μ : Fin N → Measure Position :=
    fun i => volume.restrict (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)
  have hf : ∀ᵐ x ∂Measure.pi μ, ∀ i,
      B i (k i).1 (x i) = neumannCubeSpatialMode ℓ (latticeCorner ℓ.val (b i)) (k i).1 (x i) :=
    ae_all_iff.mpr fun i => (Measure.quasiMeasurePreserving_eval μ i).ae (hB i (k i).1)
  have hp := (measurePreserving_particlePositions_restrict_openAssignmentCell ℓ b).quasiMeasurePreserving.ae hf
  filter_upwards [assignmentHilbertBasisOfScalarBases_ae ℓ b B k, hp] with x hx hfactor
  rw [hx, neumannProductMode_eq_single_cubeSpatialMode]
  congr 1
  exact Finset.prod_congr rfl fun i _ => hfactor i

end LiebThirring.TFProduct
end
