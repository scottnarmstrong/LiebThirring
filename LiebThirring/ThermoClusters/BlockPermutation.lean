/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.ClusterTensor
public import LiebThirring.Kinetic.Permutation

/-! # Permutations internal to two particle blocks -/

public section
open MeasureTheory WithLp
namespace LiebThirring

/-- The permutation of `Fin (n₁+n₂)` induced by permutations within its two
standard consecutive blocks. -/
@[expose] def blockPermutation {n₁ n₂ : ℕ}
    (σ : Equiv.Perm (Fin n₁)) (τ : Equiv.Perm (Fin n₂)) :
    Equiv.Perm (Fin (n₁+n₂)) :=
  finSumFinEquiv.permCongr (Equiv.Perm.sumCongr σ τ)

@[simp] theorem blockPermutation_castAdd {n₁ n₂ : ℕ}
    (σ : Equiv.Perm (Fin n₁)) (τ : Equiv.Perm (Fin n₂)) (i : Fin n₁) :
    blockPermutation σ τ (Fin.castAdd n₂ i) = Fin.castAdd n₂ (σ i) := by
  simp [blockPermutation, Equiv.permCongr_apply]

@[simp] theorem blockPermutation_natAdd {n₁ n₂ : ℕ}
    (σ : Equiv.Perm (Fin n₁)) (τ : Equiv.Perm (Fin n₂)) (i : Fin n₂) :
    blockPermutation σ τ (Fin.natAdd n₁ i) = Fin.natAdd n₁ (τ i) := by
  simp [blockPermutation, Equiv.permCongr_apply]

@[simp] theorem blockPermutation_one {n₁ n₂ : ℕ} :
    blockPermutation (1 : Equiv.Perm (Fin n₁)) (1 : Equiv.Perm (Fin n₂)) = 1 := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

@[simp] theorem permutePositions_one {n : ℕ} (x : Configuration n) :
    permutePositions (1 : Equiv.Perm (Fin n)) x = x := by
  apply PiLp.ext
  rintro ⟨i, a⟩
  rfl

theorem configurationClusterSplit_permute_block {n₁ n₂ : ℕ}
    (σ : Equiv.Perm (Fin n₁)) (τ : Equiv.Perm (Fin n₂))
    (x : Configuration (n₁+n₂)) :
    configurationClusterSplit n₁ n₂ (permutePositions (blockPermutation σ τ) x) =
      toLp 2 (permutePositions σ (configurationClusterSplit n₁ n₂ x).fst,
        permutePositions τ (configurationClusterSplit n₁ n₂ x).snd) := by
  apply congrArg (toLp 2)
  apply Prod.ext
  · apply (configurationPositionEquiv n₁).injective
    rw [WithLp.ext_iff]
    funext i
    change particlePosition x (blockPermutation σ τ (Fin.castAdd n₂ i)) =
      particlePosition x (Fin.castAdd n₂ (σ i))
    rw [blockPermutation_castAdd]
  · apply (configurationPositionEquiv n₂).injective
    rw [WithLp.ext_iff]
    funext i
    change particlePosition x (blockPermutation σ τ (Fin.natAdd n₁ i)) =
      particlePosition x (Fin.natAdd n₁ (τ i))
    rw [blockPermutation_natAdd]

theorem clusterSpinEquiv_symm_permute_block {n₁ n₂ q : ℕ}
    (σ : Equiv.Perm (Fin n₁)) (τ : Equiv.Perm (Fin n₂))
    (s : SpinLabels (n₁+n₂) q) :
    (clusterSpinEquiv n₁ n₂ q).symm (permuteSpins (blockPermutation σ τ) s) =
      (permuteSpins σ ((clusterSpinEquiv n₁ n₂ q).symm s).1,
        permuteSpins τ ((clusterSpinEquiv n₁ n₂ q).symm s).2) := by
  apply Prod.ext
  · funext i
    change permuteSpins (blockPermutation σ τ) s (Fin.castAdd n₂ i) = _
    simp [clusterSpinEquiv, permuteSpins]
  · funext i
    change permuteSpins (blockPermutation σ τ) s (Fin.natAdd n₁ i) = _
    simp [clusterSpinEquiv, permuteSpins]

theorem quantumClusterSplit_permute_block {n₁ n₂ m₁ m₂ : ℕ}
    (σ₁ : Equiv.Perm (Fin n₁)) (σ₂ : Equiv.Perm (Fin n₂))
    (τ₁ : Equiv.Perm (Fin m₁)) (τ₂ : Equiv.Perm (Fin m₂))
    (X : QuantumConfiguration (n₁+n₂) (m₁+m₂)) :
    quantumClusterSplit n₁ n₂ m₁ m₂
        (toLp 2 (permutePositions (blockPermutation σ₁ σ₂) X.fst,
          permutePositions (blockPermutation τ₁ τ₂) X.snd)) =
      toLp 2
        (toLp 2 (permutePositions σ₁ (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst.fst,
          permutePositions τ₁ (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst.snd),
        toLp 2 (permutePositions σ₂ (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd.fst,
          permutePositions τ₂ (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd.snd)) := by
  apply congrArg (toLp 2)
  apply Prod.ext
  · apply congrArg (toLp 2)
    apply Prod.ext
    · change (configurationClusterSplit n₁ n₂
          (permutePositions (blockPermutation σ₁ σ₂) X.fst)).fst = _
      convert congrArg WithLp.fst
        (configurationClusterSplit_permute_block σ₁ σ₂ X.fst) using 1; rfl
    · change (configurationClusterSplit m₁ m₂
          (permutePositions (blockPermutation τ₁ τ₂) X.snd)).fst = _
      convert congrArg WithLp.fst
        (configurationClusterSplit_permute_block τ₁ τ₂ X.snd) using 1; rfl
  · apply congrArg (toLp 2)
    apply Prod.ext
    · change (configurationClusterSplit n₁ n₂
          (permutePositions (blockPermutation σ₁ σ₂) X.fst)).snd = _
      exact congrArg WithLp.snd (configurationClusterSplit_permute_block σ₁ σ₂ X.fst)
    · change (configurationClusterSplit m₁ m₂
          (permutePositions (blockPermutation τ₁ τ₂) X.snd)).snd = _
      exact congrArg WithLp.snd (configurationClusterSplit_permute_block τ₁ τ₂ X.snd)

end LiebThirring
end
