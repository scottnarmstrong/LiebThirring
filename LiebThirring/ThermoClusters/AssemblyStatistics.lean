/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.ClusterShuffles

/-! # Global statistics of the genuine binary shuffle assembly

Left multiplication permutes the shuffle cosets. The electronic sign
contributes the global fermionic factor.
These are pointwise identities of the constructed wavefunction and therefore
imply both almost-everywhere statistics.

-/

public section
open MeasureTheory WithLp
open scoped SchwartzMap
namespace LiebThirring

/-- The Schwartz particle permutation is linear on finite sums. -/
theorem quantumSchwartzPermutation_sum {ι : Type*} [Fintype ι] {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M))
    (F : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    quantumSchwartzPermutation σ τ (∑ i, F i) = ∑ i, quantumSchwartzPermutation σ τ (F i) := by
  unfold quantumSchwartzPermutation
  rw [map_sum, map_sum]

/-- The Schwartz particle permutation commutes with real normalization factors. -/
theorem quantumSchwartzPermutation_real_smul {N M q : ℕ}
    (σ : Equiv.Perm (Fin N)) (τ : Equiv.Perm (Fin M)) (c : ℝ)
    (F : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    quantumSchwartzPermutation σ τ (c • F) = c • quantumSchwartzPermutation σ τ F := by
  ext X s
  change (c • F) (quantumPermutation σ τ X) (permuteSpins σ s) =
    c • F (quantumPermutation σ τ X) (permuteSpins σ s)
  rfl

private theorem shuffleCoset_sum_action {α β E : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [AddCommMonoid E]
    (σ : Equiv.Perm (α ⊕ β)) (F : Equiv.Perm.ModSumCongr α β → E) :
    (∑ e, F (σ • e)) = ∑ e, F e := by
  classical
  exact Fintype.sum_equiv
    { toFun := fun e => σ • e
      invFun := fun e => σ⁻¹ • e
      left_inv := fun e => by simp
      right_inv := fun e => by simp } _ _ (fun _ => rfl)

section BinaryAssembly
variable {n₁ n₂ m₁ m₂ q : ℕ}
variable (f : 𝓢(QuantumConfiguration n₁ m₁, SpinAmplitudes n₁ q))
  (h : 𝓢(QuantumConfiguration n₂ m₂, SpinAmplitudes n₂ q))
  (hfc : HasCompactSupport (fun X => f X)) (hhc : HasCompactSupport (fun X => h X))
  (hfa : quantum_antisymmetric (f.toLp 2 volume))
  (hha : quantum_antisymmetric (h.toLp 2 volume))
  (hfs : nuclear_symmetric (f.toLp 2 volume))
  (hhs : nuclear_symmetric (h.toLp 2 volume))

/-- Global permutations act on the actual shuffle term by the corresponding coset action. -/
theorem binaryClusterShuffleTerm_permutation
    (σ : Equiv.Perm (Fin n₁ ⊕ Fin n₂)) (τ : Equiv.Perm (Fin m₁ ⊕ Fin m₂))
    (e : Equiv.Perm.ModSumCongr (Fin n₁) (Fin n₂))
    (a : Equiv.Perm.ModSumCongr (Fin m₁) (Fin m₂)) :
    quantumSchwartzPermutation (finSumFinEquiv.permCongr σ) (finSumFinEquiv.permCongr τ)
        (binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e a) =
      ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) •
        binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs (σ • e) (τ • a) := by
  induction e using Quotient.inductionOn' with
  | h ρ =>
    induction a using Quotient.inductionOn' with
    | h η =>
      simp only [MulAction.Quotient.smul_mk, binaryClusterShuffleTerm_mk_mk,
        quantumSchwartzPermutation_smul, quantumSchwartzPermutation_comp]
      have hpe : finSumFinEquiv.permCongr σ * finSumFinEquiv.permCongr ρ =
          finSumFinEquiv.permCongr (σ*ρ) := by
        ext i
        simp only [Equiv.permCongr_apply, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
      have hpn : finSumFinEquiv.permCongr τ * finSumFinEquiv.permCongr η =
          finSumFinEquiv.permCongr (τ*η) := by
        ext i
        simp only [Equiv.permCongr_apply, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
      simp only [smul_eq_mul]
      rw [hpe, hpn, Equiv.Perm.sign_mul]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
        simp [hs, smul_smul]

/-- The finite shuffle sum has exactly the global electronic sign and nuclear invariance. -/
theorem binaryClusterShuffleSum_permutation
    (σ : Equiv.Perm (Fin n₁ ⊕ Fin n₂)) (τ : Equiv.Perm (Fin m₁ ⊕ Fin m₂)) :
    quantumSchwartzPermutation (finSumFinEquiv.permCongr σ) (finSumFinEquiv.permCongr τ)
        (binaryClusterShuffleSum f h hfc hhc hfa hha hfs hhs) =
      ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) •
        binaryClusterShuffleSum f h hfc hhc hfa hha hfs hhs := by
  unfold binaryClusterShuffleSum
  simp_rw [quantumSchwartzPermutation_sum, binaryClusterShuffleTerm_permutation,
    ← Finset.smul_sum, shuffleCoset_sum_action]
  congr 1
  exact shuffleCoset_sum_action σ (fun e => ∑ a,
    binaryClusterShuffleTerm f h hfc hhc hfa hha hfs hhs e a)

/-- Reciprocal square-root normalization preserves the constructed global statistics. -/
theorem binaryClusterAssembly_permutation
    (σ : Equiv.Perm (Fin (n₁+n₂))) (τ : Equiv.Perm (Fin (m₁+m₂))) :
    quantumSchwartzPermutation σ τ (binaryClusterAssembly f h hfc hhc hfa hha hfs hhs) =
      ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) •
        binaryClusterAssembly f h hfc hhc hfa hha hfs hhs := by
  obtain ⟨σ, rfl⟩ := finSumFinEquiv.permCongr.surjective σ
  obtain ⟨τ, rfl⟩ := finSumFinEquiv.permCongr.surjective τ
  unfold binaryClusterAssembly
  rw [quantumSchwartzPermutation_real_smul, binaryClusterShuffleSum_permutation,
    Equiv.Perm.sign_permCongr, smul_comm]

/-- The actual assembled L² state has the electronic antisymmetry. -/
theorem quantum_antisymmetric_binaryClusterAssembly :
    quantum_antisymmetric ((binaryClusterAssembly f h hfc hhc hfa hha hfs hhs).toLp 2 volume) := by
  apply quantum_antisymmetric_toLp_of_pointwise
  intro σ X s
  have he := binaryClusterAssembly_permutation f h hfc hhc hfa hha hfs hhs σ 1
  have hX := congrArg (fun F : 𝓢(QuantumConfiguration (n₁+n₂) (m₁+m₂),
      SpinAmplitudes (n₁+n₂) q) => F X s) he
  change binaryClusterAssembly f h hfc hhc hfa hha hfs hhs
      (toLp 2 (permutePositions σ X.fst, permutePositions 1 X.snd)) (permuteSpins σ s) =
    (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) •
      binaryClusterAssembly f h hfc hhc hfa hha hfs hhs X s at hX
  simpa only [permutePositions_one, smul_apply, PiLp.smul_apply, smul_eq_mul] using hX

/-- The actual assembled L² state has the nuclear symmetry. -/
theorem nuclear_symmetric_binaryClusterAssembly :
    nuclear_symmetric ((binaryClusterAssembly f h hfc hhc hfa hha hfs hhs).toLp 2 volume) := by
  apply nuclear_symmetric_toLp_of_pointwise
  intro τ X s
  have he := binaryClusterAssembly_permutation f h hfc hhc hfa hha hfs hhs 1 τ
  have hX := congrArg (fun F : 𝓢(QuantumConfiguration (n₁+n₂) (m₁+m₂),
      SpinAmplitudes (n₁+n₂) q) => F X s) he
  have hspin : permuteSpins (1 : Equiv.Perm (Fin (n₁+n₂))) s = s := rfl
  change binaryClusterAssembly f h hfc hhc hfa hha hfs hhs
      (toLp 2 (permutePositions 1 X.fst, permutePositions τ X.snd)) (permuteSpins 1 s) =
    (((Equiv.Perm.sign (1 : Equiv.Perm (Fin (n₁+n₂))) : ℤˣ) : ℤ) : ℂ) •
      binaryClusterAssembly f h hfc hhc hfa hha hfs hhs X s at hX
  simpa only [permutePositions_one, hspin, Equiv.Perm.sign_one, Units.val_one,
    Int.cast_one, one_smul] using hX
end BinaryAssembly

end LiebThirring
end
