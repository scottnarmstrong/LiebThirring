/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.ClusterTensor
public import LiebThirring.ThermoClusters.Pointwise
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.GroupTheory.Perm.Subgroup

/-! # Disjoint spatial allocations distinguish shuffle cosets

If one configuration lies in two allocations to disjoint cluster regions,
the corresponding permutations differ only by within-cluster permutations.
This is the support orthogonality behind the cluster assembly, and includes empty blocks.
-/

public section
open Set
namespace LiebThirring

/-- Two allocations of the same coordinates to disjoint regions determine one coset. -/
theorem shuffleCoset_eq_of_region_allocations {α β : Type*} [Fintype α] [Fintype β]
    (v : α ⊕ β → Position) (Ω₁ Ω₂ : Set Position) (hΩ : Disjoint Ω₁ Ω₂)
    (σ τ : Equiv.Perm (α ⊕ β))
    (_hσ₁ : ∀ i, v (σ (Sum.inl i)) ∈ Ω₁) (hσ₂ : ∀ j, v (σ (Sum.inr j)) ∈ Ω₂)
    (hτ₁ : ∀ i, v (τ (Sum.inl i)) ∈ Ω₁) (_hτ₂ : ∀ j, v (τ (Sum.inr j)) ∈ Ω₂) :
    (Quotient.mk'' σ : Equiv.Perm.ModSumCongr α β) = Quotient.mk'' τ := by
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply]
  apply Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
  rintro _ ⟨i, rfl⟩
  rcases he : (σ⁻¹ * τ) (Sum.inl i) with j | j
  · exact ⟨j, rfl⟩
  · have he' : σ (Sum.inr j) = τ (Sum.inl i) := by
      rw [← he]
      simp
    exact (Set.disjoint_left.mp hΩ (hτ₁ i) (he' ▸ hσ₂ j)).elim

end LiebThirring
end
