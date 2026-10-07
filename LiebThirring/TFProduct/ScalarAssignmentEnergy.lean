/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.ScalarParticleEnergy

/-! # Scalar energy on a full assignment cell -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace LiebThirring.TFProduct

open TFCubes TFSectors Sobolev

/-- Sum the genuine one-cube form identities over all particle coordinates. -/
theorem hasSum_scalarAssignment_energy {N : ℕ}
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
    (u : RegionState (Configuration N) ℂ (openAssignmentCell ℓ.val b))
    (g : Fin N × Fin 3 →
      RegionState (Configuration N) ℂ (openAssignmentCell ℓ.val b))
    (hweak : ∀ ia, HasWeakDerivativeOn (openAssignmentCell ℓ.val b)
      (coordinateVector ia) u (g ia)) :
    HasSum (fun k : Fin N → Fin 3 → ℕ =>
      (∑ i : Fin N, scalarCubeEigenvalue ℓ (k i)) *
        ‖(scalarAssignmentHilbertBasis ℓ b B).repr u k‖ ^ 2)
      (∑ ia : Fin N × Fin 3, ‖g ia‖ ^ 2) := by
  cases N with
  | zero =>
      simp
  | succ n =>
      have hs := hasSum_sum fun i (_hi : i ∈ Finset.univ) =>
        hasSum_scalarAssignment_particleEnergy i ℓ b B (hfactor i) u
          (fun a => g (i, a)) (fun a => hweak (i, a))
      simpa only [Finset.sum_mul, Fintype.sum_prod_type] using hs

end LiebThirring.TFProduct

end
