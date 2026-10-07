/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.DisjointSum
public import LiebThirring.ThermoClusters.ShuffleSupport

/-!
# Norm and compact support of binary cluster assembly

Signed simultaneous particle permutations preserve the ordered product norm.
Finite sums of compact Schwartz terms remain compact and preserve confinement
in the common spatial region. These facts apply to the genuine electron and
nuclear shuffle quotients used in binary assembly.

-/

public section
open MeasureTheory WithLp Set
open scoped ENNReal NNReal SchwartzMap
namespace LiebThirring

/-- A signed shuffle representative has exactly the seed's L² norm. -/
theorem norm_sign_smul_quantumSchwartzPermutation_toLp {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M))
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    ‖(((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) •
      quantumSchwartzPermutation σ τ f).toLp 2 volume)‖ = ‖f.toLp 2 volume‖ := by
  change ‖SchwartzMap.toLpCLM ℂ (SpinAmplitudes N q) 2 volume
    (((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) • quantumSchwartzPermutation σ τ f))‖ = _
  rw [map_smul, norm_smul]
  change ‖((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ))‖ *
    ‖(quantumSchwartzPermutation σ τ f).toLp 2 volume‖ = _
  rw [quantumSchwartzPermutation_toLp, norm_quantumStatePermutation]
  have hs : ‖((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ))‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, one_mul]

/-- Signing and label permutation preserve compact Schwartz support. -/
theorem isCompact_tsupport_sign_smul_quantumSchwartzPermutation {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M))
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) (hf : IsCompact (tsupport f)) :
    IsCompact (tsupport (((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) •
      quantumSchwartzPermutation σ τ f))) := by
  apply (isCompact_tsupport_quantumSchwartzPermutation σ τ f hf).of_isClosed_subset
    (isClosed_tsupport _)
  exact tsupport_smul_subset_right (fun _ => ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ))) _

/-- The closed support of a finite joint Schwartz sum lies in the union of the closed supports. -/
theorem tsupport_quantumSchwartz_sum_subset_iUnion {ι : Type*} [Fintype ι] {N M q : ℕ}
    (f : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    tsupport (∑ i, f i : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) ⊆ ⋃ i, tsupport (f i) := by
  classical
  apply closure_minimal ?_ (isClosed_iUnion_of_finite (fun i => isClosed_tsupport (f i)))
  intro X hX
  by_contra hn
  have hz (i : ι) : f i X = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hi => hn (mem_iUnion.mpr ⟨i, hi⟩))
  apply hX
  simp only [sum_apply, hz, Finset.sum_const_zero]

/-- A finite joint Schwartz sum is compactly supported when every summand is. -/
theorem isCompact_tsupport_quantumSchwartz_sum {ι : Type*} [Fintype ι] {N M q : ℕ}
    (f : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hf : ∀ i, IsCompact (tsupport (f i))) :
    IsCompact (tsupport (∑ i, f i : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))) :=
  (isCompact_iUnion hf).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_quantumSchwartz_sum_subset_iUnion f)

/-- Common coordinate confinement passes to the finite joint Schwartz sum. -/
theorem quantumSchwartz_sum_supported_region {ι : Type*} [Fintype ι] {N M q : ℕ}
    (f : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) (Ω : Set Position)
    (hf : ∀ i, tsupport (f i) ⊆ {X | (∀ j, particlePosition X.fst j ∈ Ω) ∧
      (∀ k, particlePosition X.snd k ∈ Ω)}) :
    tsupport (∑ i, f i : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) ⊆
      {X | (∀ j, particlePosition X.fst j ∈ Ω) ∧ (∀ k, particlePosition X.snd k ∈ Ω)} := by
  intro X hX
  obtain ⟨i, hi⟩ := mem_iUnion.mp (tsupport_quantumSchwartz_sum_subset_iUnion f hX)
  exact hf i hi

section BinaryAssembly

variable {n₁ n₂ m₁ m₂ q : ℕ}
  (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
  (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
  (hfc : HasCompactSupport (fun X => f X)) (hhc : HasCompactSupport (fun X => h X))
  (hfa : quantum_antisymmetric (f.toLp 2 volume))
  (hha : quantum_antisymmetric (h.toLp 2 volume))
  (hfs : nuclear_symmetric (f.toLp 2 volume))
  (hhs : nuclear_symmetric (h.toLp 2 volume))

/-- Every actual binary shuffle term has the product of the two cluster norms. -/
theorem norm_binaryClusterShuffleTerm_toLp
    (e : Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂))
    (a : Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) :
    ‖(binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e a).toLp 2 volume‖ =
      ‖f.toLp 2 volume‖ * ‖h.toLp 2 volume‖ := by
  induction e using Quotient.inductionOn' with
  | h σ =>
    induction a using Quotient.inductionOn' with
    | h τ =>
      rw [binaryClusterShuffleTerm_mk_mk]
      have hs := norm_sign_smul_quantumSchwartzPermutation_toLp
        (finSumFinEquiv.permCongr σ) (finSumFinEquiv.permCongr τ)
        (clusterProductSchwartz f h hfc hhc)
      rw [Equiv.Perm.sign_permCongr] at hs
      rw [hs, norm_clusterProductSchwartz_toLp]

/-- Every actual binary shuffle term is compactly supported. -/
theorem isCompact_tsupport_binaryClusterShuffleTerm
    (e : Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂))
    (a : Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) :
    IsCompact (tsupport (binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e a)) := by
  induction e using Quotient.inductionOn' with
  | h σ =>
    induction a using Quotient.inductionOn' with
    | h τ =>
      rw [binaryClusterShuffleTerm_mk_mk]
      have hc : IsCompact (tsupport (clusterProductSchwartz f h hfc hhc)) :=
        hasCompactSupport_clusterProduct (fun X => f X) (fun X => h X) hfc hhc
      have hs := isCompact_tsupport_sign_smul_quantumSchwartzPermutation
        (finSumFinEquiv.permCongr σ) (finSumFinEquiv.permCongr τ)
        (clusterProductSchwartz f h hfc hhc) hc
      simpa only [Equiv.Perm.sign_permCongr] using hs

/-- The finite sum of actual binary shuffle terms is compactly supported. -/
theorem isCompact_tsupport_binaryClusterShuffleSum :
    IsCompact (tsupport (binaryClusterShuffleSum f h hfc hhc hfa hha hfs hhs)) := by
  classical
  unfold binaryClusterShuffleSum
  exact isCompact_tsupport_quantumSchwartz_sum
    (fun e : Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂) =>
      ∑ a : Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂),
        binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e a)
    (fun e => isCompact_tsupport_quantumSchwartz_sum
      (fun a : Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂) =>
        binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e a)
      (isCompact_tsupport_binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e))

/-- The actual normalized binary assembly is a compact Schwartz wave. -/
theorem isCompact_tsupport_binaryClusterAssembly :
    IsCompact (tsupport (binaryClusterAssembly f h hfc hhc hfa hha hfs hhs)) := by
  classical
  unfold binaryClusterAssembly
  apply (isCompact_tsupport_binaryClusterShuffleSum f h hfc hhc hfa hha hfs hhs).of_isClosed_subset
    (isClosed_tsupport _)
  exact tsupport_smul_subset_right (fun _ => (Real.sqrt
    (Fintype.card (Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂)) *
      Fintype.card (Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂))))⁻¹) _

/-- The assembled wave is confined to the union of the two original cluster regions. -/
theorem binaryClusterAssembly_supported_union (Ω₁ Ω₂ : Set Position)
    (hfp : tsupport f ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω₁) ∧
      (∀ k, particlePosition X.snd k ∈ Ω₁)})
    (hhp : tsupport h ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω₂) ∧
      (∀ k, particlePosition X.snd k ∈ Ω₂)}) :
    tsupport (binaryClusterAssembly f h hfc hhc hfa hha hfs hhs) ⊆
      {X | (∀ i, particlePosition X.fst i ∈ Ω₁ ∪ Ω₂) ∧
        (∀ k, particlePosition X.snd k ∈ Ω₁ ∪ Ω₂)} := by
  classical
  unfold binaryClusterAssembly
  refine (tsupport_smul_subset_right (fun _ => (Real.sqrt
    (Fintype.card (Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂)) *
      Fintype.card (Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂))))⁻¹) _).trans ?_
  unfold binaryClusterShuffleSum
  exact quantumSchwartz_sum_supported_region
    (fun e : Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂) =>
      ∑ a : Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂),
        binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e a) (Ω₁ ∪ Ω₂)
    (fun e => quantumSchwartz_sum_supported_region
      (fun a : Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂) =>
        binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e a) (Ω₁ ∪ Ω₂)
      (binaryClusterShuffleTerm_supported_union f h hfc hhc hfa hha hfs hhs
        Ω₁ Ω₂ hfp hhp e))

/-- Two normalized confined clusters in disjoint regions give a unit-norm actual binary assembly.
Closed support orthogonality is derived from the original region assumptions. -/
theorem norm_binaryClusterAssembly_toLp (Ω₁ Ω₂ : Set Position) (hΩ : Disjoint Ω₁ Ω₂)
    (hfp : tsupport f ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω₁) ∧
      (∀ k, particlePosition X.snd k ∈ Ω₁)})
    (hhp : tsupport h ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω₂) ∧
      (∀ k, particlePosition X.snd k ∈ Ω₂)})
    (hnf : ‖f.toLp 2 volume‖ = 1) (hnh : ‖h.toLp 2 volume‖ = 1) :
    ‖(binaryClusterAssembly f h hfc hhc hfa hha hfs hhs).toLp 2 volume‖ = 1 := by
  classical
  let : Fintype (Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂)) := inferInstance
  let : Fintype (Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) := inferInstance
  let F : Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂) ×
      Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂) →
      𝓢(QuantumConfiguration (n₁+n₂) (m₁+m₂), SpinAmplitudes (n₁+n₂) q) :=
    fun p => binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs p.1 p.2
  have hd := pairwiseDisjoint_binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs
    Ω₁ Ω₂ hfp hhp hΩ
  have hn (p) : ‖(F p).toLp 2 volume‖ = 1 := by
    dsimp only [F]
    rw [norm_binaryClusterShuffleTerm_toLp, hnf, hnh, one_mul]
  have hcard : 0 < Fintype.card (Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂) ×
      Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) := Fintype.card_pos
  have hnorm := quantumSchwartz_norm_toLp_normalized_sum hcard F hd hn
  simpa only [F, Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul,
    binaryClusterAssembly, binaryClusterShuffleSum] using hnorm

end BinaryAssembly

end LiebThirring
end
