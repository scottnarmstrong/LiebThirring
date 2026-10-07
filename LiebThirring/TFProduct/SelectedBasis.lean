/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.CellBasis
public import LiebThirring.TFProduct.ProductRegionBasis
public import LiebThirring.TFProduct.ParticleL2

/-!
# Product bases after splitting off a selected particle

The canonical scalar assignment basis becomes the product of the selected
one-particle cube basis and the canonical basis of the residual assignment.
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace

namespace LiebThirring.TFProduct

open TFCubes TFSectors

/-- The canonical assignment basis agrees with the selected-particle product
basis under the physical L² splitting isometry. -/
theorem selectedParticleL2Equiv_scalarAssignmentHilbertBasis {n : ℕ}
    (i : Fin (n + 1)) (ℓ : {x : ℝ // 0 < x})
    (b : Fin (n + 1) → LatticeIndex)
    (B : (r : Fin (n + 1)) → HilbertBasis (Fin 3 → ℕ) ℂ
      (RegionState Position ℂ (cubeInterior (latticeCorner ℓ.val (b r)) ℓ)))
    (k : Fin (n + 1) → Fin 3 → ℕ) :
    selectedParticleL2Equiv i ℓ b (scalarAssignmentHilbertBasis ℓ b B k) =
      productRegionHilbertBasis
        (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)
        (openAssignmentCell ℓ.val (fun j => b (i.succAbove j)))
        (B i)
        (scalarAssignmentHilbertBasis ℓ (fun j => b (i.succAbove j))
          (fun j => B (i.succAbove j)))
        (k i, fun j => k (i.succAbove j)) := by
  let Ω := cubeInterior (latticeCorner ℓ.val (b i)) ℓ
  let Θ := openAssignmentCell ℓ.val (fun j => b (i.succAbove j))
  let Crest := scalarAssignmentHilbertBasis ℓ (fun j => b (i.succAbove j))
    (fun j => B (i.succAbove j))
  let p : (Fin 3 → ℕ) × (Fin n → Fin 3 → ℕ) :=
    (k i, fun j => k (i.succAbove j))
  have hselected := selectedParticleL2Equiv_ae i ℓ b
    (scalarAssignmentHilbertBasis ℓ b B k)
  have hsplit :=
    (measurePreserving_particleSplitEquiv_restrict i ℓ b).quasiMeasurePreserving.ae
      (scalarAssignmentHilbertBasis_ae ℓ b B k)
  have hproduct := productRegionHilbertBasis_ae Ω Θ (B i) Crest p
  have hrest0 := scalarAssignmentHilbertBasis_ae ℓ
    (fun j => b (i.succAbove j)) (fun j => B (i.succAbove j))
    (fun j => k (i.succAbove j))
  have hrest := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict Ω) (ν := volume.restrict Θ)).ae hrest0
  have hμ : (volume.restrict Ω).prod (volume.restrict Θ) =
      volume.restrict (Ω ×ˢ Θ) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  rw [hμ] at hrest
  apply Lp.ext
  filter_upwards [hselected, hsplit, hproduct, hrest] with z hz hsplitz hprodz hrestz
  rw [hz, hprodz, hsplitz, hrestz]
  change (∏ r : Fin (n + 1),
      B r (k r) (particlePosition (particleSplitEquiv i z) r)) =
    B i (k i) z.1 *
      ∏ j : Fin n, B (i.succAbove j) (k (i.succAbove j))
        (particlePosition z.2 j)
  rw [Fin.prod_univ_succAbove _ i, particlePosition_particleSplit_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [particlePosition_particleSplit_succAbove]

/-- Coefficients in the assignment basis equal coefficients in the selected
particle product basis after applying the splitting isometry. -/
theorem scalarAssignmentHilbertBasis_repr_eq_productRegion_repr {n : ℕ}
    (i : Fin (n + 1)) (ℓ : {x : ℝ // 0 < x})
    (b : Fin (n + 1) → LatticeIndex)
    (B : (r : Fin (n + 1)) → HilbertBasis (Fin 3 → ℕ) ℂ
      (RegionState Position ℂ (cubeInterior (latticeCorner ℓ.val (b r)) ℓ)))
    (u : RegionState (Configuration (n + 1)) ℂ (openAssignmentCell ℓ.val b))
    (k : Fin (n + 1) → Fin 3 → ℕ) :
    (scalarAssignmentHilbertBasis ℓ b B).repr u k =
      (productRegionHilbertBasis
        (cubeInterior (latticeCorner ℓ.val (b i)) ℓ)
        (openAssignmentCell ℓ.val (fun j => b (i.succAbove j)))
        (B i)
        (scalarAssignmentHilbertBasis ℓ (fun j => b (i.succAbove j))
          (fun j => B (i.succAbove j)))).repr
        (selectedParticleL2Equiv i ℓ b u)
        (k i, fun j => k (i.succAbove j)) := by
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply,
    ← selectedParticleL2Equiv_scalarAssignmentHilbertBasis i ℓ b B k]
  exact (selectedParticleL2Equiv i ℓ b).inner_map_map
    (scalarAssignmentHilbertBasis ℓ b B k) u |>.symm

end LiebThirring.TFProduct

end
