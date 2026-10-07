/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.ClusterTensor

/-! # Closed supports of ordered cluster products

The actual closed support of the product lies in the product of the two
closed cluster supports. Consequently every global particle lies in the
union of the two cluster regions. Proof: cluster assembly.
-/

public section
open WithLp Set
open scoped SchwartzMap
namespace LiebThirring

/-- A product's closed support lies in the closed supports of both factors. -/
theorem tsupport_clusterProduct_subset {n₁ n₂ m₁ m₂ q : ℕ}
    (f : QuantumConfiguration n₁ m₁ → SpinAmplitudes n₁ q)
    (h : QuantumConfiguration n₂ m₂ → SpinAmplitudes n₂ q) :
    tsupport (clusterProduct f h) ⊆
      (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂) ⁻¹' (tsupport f ×ˢ tsupport h) := by
  apply closure_minimal ?_
    (((isClosed_tsupport f).prod (isClosed_tsupport h)).preimage
      (quantumClusterSplitHomeomorph n₁ n₂ m₁ m₂).continuous)
  intro X hX
  refine ⟨subset_tsupport f ?_, subset_tsupport h ?_⟩
  · intro hz
    change f (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst = 0 at hz
    apply hX
    ext s
    simp only [clusterProduct, clusterSpinTensor, hz, PiLp.toLp_apply, PiLp.zero_apply, zero_mul]
  · intro hz
    change h (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd = 0 at hz
    apply hX
    ext s
    simp only [clusterProduct, clusterSpinTensor, hz, PiLp.toLp_apply, PiLp.zero_apply, mul_zero]

/-- Closed support confinement passes from two joint factors to the union region. -/
theorem clusterProduct_supported_union {n₁ n₂ m₁ m₂ q : ℕ}
    (f : QuantumConfiguration n₁ m₁ → SpinAmplitudes n₁ q)
    (h : QuantumConfiguration n₂ m₂ → SpinAmplitudes n₂ q)
    (Ω₁ Ω₂ : Set Position)
    (hf : tsupport f ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω₁) ∧
      (∀ k, particlePosition X.snd k ∈ Ω₁)})
    (hh : tsupport h ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω₂) ∧
      (∀ k, particlePosition X.snd k ∈ Ω₂)}) :
    tsupport (clusterProduct f h) ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω₁ ∪ Ω₂) ∧
      (∀ k, particlePosition X.snd k ∈ Ω₁ ∪ Ω₂)} := by
  intro X hX
  obtain ⟨h₁, h₂⟩ := tsupport_clusterProduct_subset f h hX
  have hfX := hf h₁
  have hhX := hh h₂
  constructor
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Or.inl (hfX.1 j)
    · exact Or.inr (hhX.1 j)
  · intro k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · exact Or.inl (hfX.2 j)
    · exact Or.inr (hhX.2 j)

end LiebThirring
end
