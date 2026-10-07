/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeBasisCoordinates
public import LiebThirring.TFCubes.CubeModesL2
public import LiebThirring.TFCubes.CubeParseval
public import LiebThirring.TFCubes.IntervalBasis

/-! # Complete physical Dirichlet and Neumann cube Hilbert bases

The actual scalar product bases are pulled back by translated Euclidean
coordinates and then tensored with the finite spin basis. Their representatives
are exactly the literal normalized cube modes, including all Neumann zero modes.
-/

@[expose] public section

open MeasureTheory Set
open scoped InnerProductSpace

namespace LiebThirring.TFCubes

/-- Pull an actual product of interval Hilbert bases back to the physical cube. -/
noncomputable def cubeScalarProductBasis {ι : Type*} (b : Position)
    (ℓ : {ℓ : ℝ // 0 < ℓ})
    (B : HilbertBasis ι ℂ (Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val)))) :
    HilbertBasis (Fin 3 → ι) ℂ (RegionState Position ℂ (cubeInterior b ℓ)) :=
  mapHilbertBasis (cubeCoordinateL2Equiv b ℓ) (hilbertBasisPiThreeProduct B)

/-- Literal product representatives of the physical scalar product basis. -/
theorem cubeScalarProductBasis_ae {ι : Type*} (b : Position)
    (ℓ : {ℓ : ℝ // 0 < ℓ})
    (B : HilbertBasis ι ℂ (Lp ℂ 2 (volume.restrict (Ioo 0 ℓ.val))))
    (φ : ι → ℝ → ℂ) (hφ : ∀ i, B i =ᵐ[volume.restrict (Ioo 0 ℓ.val)] φ i)
    (k : Fin 3 → ι) :
    cubeScalarProductBasis b ℓ B k =ᵐ[volume.restrict (cubeInterior b ℓ)]
      fun x => ∏ i : Fin 3, φ (k i) (x i - b i) := by
  have hfactor : ∀ᵐ x ∂cubeCoordinateMeasure ℓ, ∀ i : Fin 3,
      B (k i) (x i) = φ (k i) (x i) :=
    ae_all_iff.mpr fun i =>
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin 3 => volume.restrict (Ioo 0 ℓ.val)) i).ae
        (hφ (k i))
  have hproduct : hilbertBasisPiThreeProduct B k =ᵐ[cubeCoordinateMeasure ℓ]
      fun x => ∏ i : Fin 3, φ (k i) (x i) := by
    filter_upwards [hilbertBasisPiThreeProduct_ae B k, hfactor] with x hx hxf
    rw [hx]
    exact Finset.prod_congr rfl fun i _ => hxf i
  rw [cubeScalarProductBasis, mapHilbertBasis_apply]
  exact (cubeCoordinateL2LI_ae b ℓ (hilbertBasisPiThreeProduct B k)).trans
    ((measurePreserving_cubeCoordinates_restrict b ℓ).quasiMeasurePreserving.ae hproduct)

/-- The complete scalar cosine basis on an arbitrary translated cube. -/
noncomputable def neumannCubeScalarBasis (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) :=
  cubeScalarProductBasis b ℓ (neumannIntervalBasis ℓ)

theorem neumannCubeScalarBasis_ae (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (k : Fin 3 → ℕ) :
    neumannCubeScalarBasis ℓ b k =ᵐ[volume.restrict (cubeInterior b ℓ)]
      neumannCubeSpatialMode ℓ b k :=
  cubeScalarProductBasis_ae b ℓ (neumannIntervalBasis ℓ)
    (fun n x => (neumannIntervalMode ℓ n x : ℂ))
    (fun n => (neumannIntervalBasis_apply ℓ n) ▸ neumannIntervalModeL2_ae ℓ n) k

end LiebThirring.TFCubes

end
