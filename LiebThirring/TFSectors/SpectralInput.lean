/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.ProductModes
public import LiebThirring.TFSectors.SectorSpectralSums
public import LiebThirring.TFSectors.AssignmentGeometry
public import LiebThirring.TFCubes.LocalFormGraph

/-!
# Explicit conditional cube spectral theory input for the product Neumann form

The basis is linked to the literal product of normalized cosine-and-spin modes.
The diagonal identity has the sum of one-particle eigenvalues as its weight and
quantifies over all local form states. No fermionic or occupation bound is an
input here. This interface records the cube spectral conclusions used as explicit hypotheses.
-/

@[expose] public section
open MeasureTheory
namespace LiebThirring.TFSectors
open TFCubes TFLattice

/-- Literal product-basis completeness and unweighted physical diagonalization
on the assigned product cube: the spectral input of cube spectral theory. -/
structure NeumannProductSpectralData (N q : ℕ) (ℓ : {x : ℝ // 0 < x})
    (b : Fin N → LatticeIndex) where
  basis : HilbertBasis (Fin N → ModeIndex q) ℂ (ConfigurationRegionState N q (openAssignmentCell ℓ b))
  basis_ae : ∀ k, basis k =ᵐ[volume.restrict (openAssignmentCell ℓ b)] neumannProductMode ℓ b k
  diagonal : ∀ v : localFormGraph N q (openAssignmentCell ℓ b),
    HasSum (fun k => productEigenvalue ℓ k *
      ‖basis.repr ((v : LocalFormGraphAmbient N q (openAssignmentCell ℓ b)) none) k‖ ^ 2)
      (localGradientEnergy (v : LocalFormGraphAmbient N q (openAssignmentCell ℓ b)))

end LiebThirring.TFSectors
end
