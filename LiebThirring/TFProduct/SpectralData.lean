/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.SpectralAssembly
public import LiebThirring.TFProduct.CubeScalarForm

/-! # The physical N-particle Neumann cube spectral datum

The one-particle bases and weak form identity are discharged by the cube
theorems. No product spectral, form, or approximation hypothesis remains.
-/

@[expose] public section
namespace LiebThirring.TFProduct
open TFCubes TFSectors

/-- Complete Neumann product spectral data on every physical assignment cell. -/
noncomputable def neumannProductSpectralData {N q : ℕ}
    (ℓ : {x : ℝ // 0 < x}) (b : Fin N → LatticeIndex) :
    NeumannProductSpectralData N q ℓ b :=
  neumannProductSpectralData_of_scalarCubeBases ℓ b
    (fun i => neumannCubeScalarBasis ℓ (latticeCorner ℓ.val (b i)))
    (fun i => neumannCubeScalarBasis_ae ℓ (latticeCorner ℓ.val (b i)))
    (fun i => hasSum_scalarCube_form ℓ (latticeCorner ℓ.val (b i)))

end LiebThirring.TFProduct
end
