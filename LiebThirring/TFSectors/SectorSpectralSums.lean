/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFSectors.EigenvalueComparison
public import LiebThirring.TFCoulomb.SectorPairs

/-! # Distinct product-mode labels and their per-cube spectral sums -/

@[expose] public section
namespace LiebThirring.TFSectors
open TFLattice

/-- Fermionic admissibility of an ordered product-mode label. -/
def DistinctWithinCubes {N q : ℕ} (b : Fin N → LatticeIndex)
    (k : Fin N → ModeIndex q) : Prop :=
  ∀ i j, b i = b j → k i = k j → i = j

/-- One-particle mode labels occupied in a given assigned cube. -/
noncomputable def cubeModeSet {N q : ℕ} (b : Fin N → LatticeIndex)
    (k : Fin N → ModeIndex q) (β : LatticeIndex) : Finset (ModeIndex q) :=
  (Finset.univ.filter (fun i => b i = β)).image k

/-- The unweighted physical eigenvalue of a product mode. -/
noncomputable def productEigenvalue {N q : ℕ} (ℓ : {x : ℝ // 0 < x})
    (k : Fin N → ModeIndex q) : ℝ := ∑ i, cubeEigenvalue ℓ (k i)

theorem card_cubeModeSet {N q : ℕ} (b : Fin N → LatticeIndex)
    (k : Fin N → ModeIndex q) (hk : DistinctWithinCubes b k) (β : LatticeIndex) :
    (cubeModeSet b k β).card = TFCoulomb.sectorCount b β := by
  classical
  apply Finset.card_image_iff.mpr
  intro i hi j hj heq
  exact hk i j ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) heq

theorem sum_cubeModeSet {N q : ℕ} (ℓ : {x : ℝ // 0 < x})
    (b : Fin N → LatticeIndex) (k : Fin N → ModeIndex q)
    (hk : DistinctWithinCubes b k) (β : LatticeIndex) :
    (∑ p ∈ cubeModeSet b k β, cubeEigenvalue ℓ p) =
      ∑ i ∈ Finset.univ.filter (fun i => b i = β), cubeEigenvalue ℓ (k i) := by
  classical
  apply Finset.sum_image
  intro i hi j hj heq
  exact hk i j ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) heq

theorem productEigenvalue_ge_occupationSum_of_filled_bound {N q : ℕ} (hq : 1 ≤ q)
    (ℓ : {x : ℝ // 0 < x}) (Cq : ℝ)
    (hsharp : ∀ s : Finset (ModeIndex q), IsFilled (fun _ => True) s →
      (tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ ((5 : ℝ) / 3) -
        Cq * ℓ.val⁻¹ ^ 2 * (s.card : ℝ) ^ ((4 : ℝ) / 3) ≤
          ∑ p ∈ s, cubeEigenvalue ℓ p)
    (b : Fin N → LatticeIndex) (k : Fin N → ModeIndex q)
    (hk : DistinctWithinCubes b k) :
    (∑ β ∈ TFCoulomb.occupiedCubes b,
      ((tfKineticConstant ⟨q, hq⟩).val * ℓ.val⁻¹ ^ 2 *
        (TFCoulomb.sectorCount b β : ℝ) ^ ((5 : ℝ) / 3) -
      Cq * ℓ.val⁻¹ ^ 2 * (TFCoulomb.sectorCount b β : ℝ) ^ ((4 : ℝ) / 3))) ≤
      productEigenvalue ℓ k := by
  classical
  calc
    _ ≤ ∑ β ∈ TFCoulomb.occupiedCubes b,
        ∑ i ∈ Finset.univ.filter (fun i => b i = β), cubeEigenvalue ℓ (k i) := by
      apply Finset.sum_le_sum
      intro β _
      have h := sum_cubeEigenvalue_ge_of_filled_bound hq ℓ Cq hsharp (cubeModeSet b k β)
      rwa [card_cubeModeSet b k hk β, sum_cubeModeSet ℓ b k hk β] at h
    _ = productEigenvalue ℓ k := by
      exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem b hi) _

end LiebThirring.TFSectors
end
