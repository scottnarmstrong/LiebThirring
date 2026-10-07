/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.ClusterShuffles
public import LiebThirring.ThermoClusters.Allocations
public import LiebThirring.ThermoClusters.TensorSupport

/-! # Spatial orthogonality of the actual binary shuffle terms

Closed supports of different electron or nuclear allocations are disjoint.
The proof uses only the stated cluster confinement and disjointness of the
spatial regions, not an assumed orthogonality conclusion.

-/

public section
open MeasureTheory WithLp Set Function
open scoped SchwartzMap
namespace LiebThirring

variable {n₁ n₂ m₁ m₂ q : ℕ}
variable (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
  (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
  (hfc : HasCompactSupport (fun X => f X)) (hhc : HasCompactSupport (fun X => h X))
  (hfa : quantum_antisymmetric (f.toLp 2 volume))
  (hha : quantum_antisymmetric (h.toLp 2 volume))
  (hfs : nuclear_symmetric (f.toLp 2 volume))
  (hhs : nuclear_symmetric (h.toLp 2 volume))
  (Ω₁ Ω₂ : Set Position)
  (hfp : tsupport f ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω₁) ∧
    (∀ k, particlePosition X.snd k ∈ Ω₁)})
  (hhp : tsupport h ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω₂) ∧
    (∀ k, particlePosition X.snd k ∈ Ω₂)})

private theorem binaryShuffleTerm_mem_product_support
    (σ : Equiv.Perm (Fin n₁ ⊕ Fin n₂)) (τ : Equiv.Perm (Fin m₁ ⊕ Fin m₂))
    (X : QuantumConfiguration (n₁+n₂) (m₁+m₂))
    (hX : X ∈ tsupport (binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs
      (Quotient.mk'' σ) (Quotient.mk'' τ))) :
    quantumPermutation (finSumFinEquiv.permCongr σ) (finSumFinEquiv.permCongr τ) X ∈
      tsupport (clusterProduct (fun X => f X) (fun X => h X)) := by
  rw [binaryClusterShuffleTerm_mk_mk] at hX
  have hp : X ∈ tsupport (quantumSchwartzPermutation (finSumFinEquiv.permCongr σ)
      (finSumFinEquiv.permCongr τ) (clusterProductSchwartz f h hfc hhc)) :=
    tsupport_smul_subset_right (fun _ => (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ))
      (fun Y => quantumSchwartzPermutation (finSumFinEquiv.permCongr σ)
        (finSumFinEquiv.permCongr τ) (clusterProductSchwartz f h hfc hhc) Y) hX
  rw [tsupport_quantumSchwartzPermutation] at hp
  exact hp

include hfp hhp in
/-- Each actual shuffle term confines its allocated labels to the original regions. -/
theorem binaryClusterShuffleTerm_allocations
    (σ : Equiv.Perm (Fin n₁ ⊕ Fin n₂)) (τ : Equiv.Perm (Fin m₁ ⊕ Fin m₂))
    (X : QuantumConfiguration (n₁+n₂) (m₁+m₂))
    (hX : X ∈ tsupport (binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs
      (Quotient.mk'' σ) (Quotient.mk'' τ))) :
    (∀ i, particlePosition X.fst (finSumFinEquiv (σ (Sum.inl i))) ∈ Ω₁) ∧
    (∀ j, particlePosition X.fst (finSumFinEquiv (σ (Sum.inr j))) ∈ Ω₂) ∧
    (∀ i, particlePosition X.snd (finSumFinEquiv (τ (Sum.inl i))) ∈ Ω₁) ∧
    (∀ j, particlePosition X.snd (finSumFinEquiv (τ (Sum.inr j))) ∈ Ω₂) := by
  have hp := binaryShuffleTerm_mem_product_support f h hfc hhc hfa hha hfs hhs σ τ X hX
  have hs := tsupport_clusterProduct_subset (fun X => f X) (fun X => h X) hp
  have h₁ := hfp hs.1
  have h₂ := hhp hs.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have hi : particlePosition X.fst
        ((finSumFinEquiv.permCongr σ) (Fin.castAdd n₂ i)) ∈ Ω₁ := h₁.1 i
    simpa [Equiv.permCongr_apply] using hi
  · intro i
    have hi : particlePosition X.fst
        ((finSumFinEquiv.permCongr σ) (Fin.natAdd n₁ i)) ∈ Ω₂ := h₂.1 i
    simpa [Equiv.permCongr_apply] using hi
  · intro i
    have hi : particlePosition X.snd
        ((finSumFinEquiv.permCongr τ) (Fin.castAdd m₂ i)) ∈ Ω₁ := h₁.2 i
    simpa [Equiv.permCongr_apply] using hi
  · intro i
    have hi : particlePosition X.snd
        ((finSumFinEquiv.permCongr τ) (Fin.natAdd m₁ i)) ∈ Ω₂ := h₂.2 i
    simpa [Equiv.permCongr_apply] using hi

include hfp hhp in
/-- Different electron/nuclear shuffle allocations have disjoint closed spatial supports. -/
theorem pairwiseDisjoint_binaryClusterShuffleTerm (hΩ : Disjoint Ω₁ Ω₂) :
    Pairwise (Disjoint on fun p :
      Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂) × Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂) =>
      tsupport (fun X => binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs p.1 p.2 X)) := by
  classical
  rintro ⟨e, a⟩ ⟨e', a'⟩ hne
  obtain ⟨σ, rfl⟩ := Quotient.exists_rep e
  obtain ⟨τ, rfl⟩ := Quotient.exists_rep a
  obtain ⟨σ', rfl⟩ := Quotient.exists_rep e'
  obtain ⟨τ', rfl⟩ := Quotient.exists_rep a'
  apply Set.disjoint_left.mpr
  intro X hX hX'
  have h₁ := binaryClusterShuffleTerm_allocations f h hfc hhc hfa hha hfs hhs
    Ω₁ Ω₂ hfp hhp σ τ X hX
  have h₂ := binaryClusterShuffleTerm_allocations f h hfc hhc hfa hha hfs hhs
    Ω₁ Ω₂ hfp hhp σ' τ' X hX'
  apply hne
  apply Prod.ext
  · exact shuffleCoset_eq_of_region_allocations
      (fun i => particlePosition X.fst (finSumFinEquiv i)) Ω₁ Ω₂ hΩ σ σ'
      h₁.1 h₁.2.1 h₂.1 h₂.2.1
  · exact shuffleCoset_eq_of_region_allocations
      (fun i => particlePosition X.snd (finSumFinEquiv i)) Ω₁ Ω₂ hΩ τ τ'
      h₁.2.2.1 h₁.2.2.2 h₂.2.2.1 h₂.2.2.2

include hfp hhp in
/-- Every actual shuffle term remains inside the union of the cluster regions. -/
theorem binaryClusterShuffleTerm_supported_union
    (e : Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂))
    (a : Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) :
    tsupport (binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e a) ⊆
      {X | (∀ i, particlePosition X.fst i ∈ Ω₁ ∪ Ω₂) ∧
        (∀ k, particlePosition X.snd k ∈ Ω₁ ∪ Ω₂)} := by
  obtain ⟨σ, rfl⟩ := Quotient.exists_rep e
  obtain ⟨τ, rfl⟩ := Quotient.exists_rep a
  intro X hX
  have hp := binaryShuffleTerm_mem_product_support f h hfc hhc hfa hha hfs hhs σ τ X hX
  have hu := clusterProduct_supported_union (fun X => f X) (fun X => h X) Ω₁ Ω₂ hfp hhp hp
  constructor
  · intro i
    simpa using hu.1 ((finSumFinEquiv.permCongr σ).symm i)
  · intro k
    simpa using hu.2 ((finSumFinEquiv.permCongr τ).symm k)

end LiebThirring
end
