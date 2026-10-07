/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFProduct.ParticleSplit

/-! # Physical local L² transport in selected-particle coordinates -/

@[expose] public section
open MeasureTheory
namespace LiebThirring.TFProduct
open TFCubes TFSectors Sobolev

/-- Restricted physical scalar L² in selected-particle product coordinates. -/
noncomputable def selectedParticleL2Equiv {n : ℕ} (i : Fin (n + 1))
    (ℓ : {x : ℝ // 0 < x}) (b : Fin (n + 1) → LatticeIndex) :
    RegionState (Configuration (n + 1)) ℂ (openAssignmentCell ℓ.val b) ≃ₗᵢ[ℂ]
      RegionState (Position × Configuration n) ℂ
        (cubeInterior (latticeCorner ℓ.val (b i)) ℓ ×ˢ
          openAssignmentCell ℓ.val (fun j => b (i.succAbove j))) :=
  l2PullbackEquiv (particleSplitEquiv i).toHomeomorph.toMeasurableEquiv
    (measurePreserving_particleSplitEquiv_restrict i ℓ b)

theorem selectedParticleL2Equiv_ae {n : ℕ} (i : Fin (n + 1))
    (ℓ : {x : ℝ // 0 < x}) (b : Fin (n + 1) → LatticeIndex)
    (u : RegionState (Configuration (n + 1)) ℂ (openAssignmentCell ℓ.val b)) :
    selectedParticleL2Equiv i ℓ b u =ᵐ[volume.restrict
      (cubeInterior (latticeCorner ℓ.val (b i)) ℓ ×ˢ
        openAssignmentCell ℓ.val (fun j => b (i.succAbove j)))]
      fun z => u (particleSplitEquiv i z) :=
  l2PullbackEquiv_ae _ _ u

/-- The selected physical coordinate weak derivative becomes a retained-variable derivative. -/
theorem selectedParticleL2Equiv_hasWeakDerivative {n : ℕ} (i : Fin (n + 1))
    (ℓ : {x : ℝ // 0 < x}) (b : Fin (n + 1) → LatticeIndex) (a : Fin 3)
    {u g : RegionState (Configuration (n + 1)) ℂ (openAssignmentCell ℓ.val b)}
    (h : HasWeakDerivativeOn (openAssignmentCell ℓ.val b) (coordinateVector (i, a)) u g) :
    HasWeakDerivativeOn
      (cubeInterior (latticeCorner ℓ.val (b i)) ℓ ×ˢ
        openAssignmentCell ℓ.val (fun j => b (i.succAbove j)))
      (EuclideanSpace.basisFun (Fin 3) ℝ a, (0 : Configuration n))
      (selectedParticleL2Equiv i ℓ b u) (selectedParticleL2Equiv i ℓ b g) := by
  have ht := HasWeakDerivativeOn.continuousLinearEquiv_pullback_restrict (particleSplitEquiv i)
    (particleSplitEquiv_preimage_openAssignmentCell i ℓ b)
    (measurePreserving_particleSplitEquiv_restrict i ℓ b) h
  rw [particleSplitEquiv_symm_coordinateVector_self] at ht
  exact ht

end LiebThirring.TFProduct
end
