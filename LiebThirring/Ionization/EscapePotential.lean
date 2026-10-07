/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapeInsertion
public import LiebThirring.Defs.Coulomb
import LiebThirring.Kinetic.Permutation

/-! # Coulomb potentials under particle insertion and permutation

This module records the exact pointwise Coulomb decomposition after inserting a
selected particle at coordinate zero, together with permutation invariance of
the electron-electron and electron-nucleus potentials.
-/

public section

open scoped ENNReal NNReal

namespace LiebThirring

/-- Inserting a selected particle adds exactly its interaction with every old particle. -/
theorem electronRepulsion_escapeInsertPositions {N : ℕ}
    (p : Position) (y : Configuration N) :
    electronRepulsion (escapeInsertPositions p y) = electronRepulsion y +
      ∑ j : Fin N, coulombKernel p (particlePosition y j) := by
  unfold electronRepulsion
  simp only [Finset.sum_filter]
  simp_rw [Fin.sum_univ_succ]
  simp
  ac_rfl

/-- Inserting a selected particle adds exactly its attraction to every nucleus. -/
theorem attraction_escapeInsertPositions {N M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (p : Position) (y : Configuration N) :
    attraction z R (escapeInsertPositions p y) = attraction z R y +
      ∑ k : Fin M, (z k : ℝ≥0∞) * coulombKernel p (R k) := by
  rw [attraction, Fin.sum_univ_succ, attraction]
  simp only [particlePosition_escapeInsertPositions_zero,
    particlePosition_escapeInsertPositions_succ]
  ac_rfl

/-- Atomic specialization: the inserted particle contributes `Z / |p|`. -/
theorem attraction_escapeInsertPositions_atom {N : ℕ} (Z : ℝ≥0)
    (p : Position) (y : Configuration N) :
    attraction (fun _ : Fin 1 => Z) (fun _ => 0) (escapeInsertPositions p y) =
      attraction (fun _ : Fin 1 => Z) (fun _ => 0) y +
        (Z : ℝ≥0∞) * coulombKernel p 0 := by
  rw [attraction_escapeInsertPositions]
  simp

private def increasingPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  (Finset.univ.product Finset.univ).filter (fun ij => ij.1 < ij.2)

private def permuteIncreasingPair {N : ℕ} (σ : Equiv.Perm (Fin N))
    (ij : Fin N × Fin N) : Fin N × Fin N :=
  if σ ij.1 < σ ij.2 then (σ ij.1, σ ij.2) else (σ ij.2, σ ij.1)

private lemma sum_increasingPairs_eq {N : ℕ} (f : Fin N → Fin N → ℝ≥0∞) :
    (∑ ij ∈ increasingPairs N, f ij.1 ij.2) =
      ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j), f i j := by
  unfold increasingPairs
  simp only [Finset.sum_filter]
  exact Finset.sum_product Finset.univ Finset.univ
    (fun ij => if ij.1 < ij.2 then f ij.1 ij.2 else 0)

private lemma permuteIncreasingPair_mem {N : ℕ} (σ : Equiv.Perm (Fin N))
    {ij : Fin N × Fin N} (hij : ij ∈ increasingPairs N) :
    permuteIncreasingPair σ ij ∈ increasingPairs N := by
  simp only [increasingPairs, Finset.mem_filter] at hij ⊢
  simp only [permuteIncreasingPair]
  split_ifs with h
  · exact ⟨by simp, h⟩
  · exact ⟨by simp, lt_of_le_of_ne (not_lt.mp h) (σ.injective.ne hij.2.ne).symm⟩

private lemma permuteIncreasingPair_injective {N : ℕ} (σ : Equiv.Perm (Fin N))
    {a b : Fin N × Fin N} (ha : a ∈ increasingPairs N) (hb : b ∈ increasingPairs N)
    (h : permuteIncreasingPair σ a = permuteIncreasingPair σ b) : a = b := by
  simp only [increasingPairs, Finset.mem_filter] at ha hb
  replace ha := ha.2
  replace hb := hb.2
  simp only [permuteIncreasingPair] at h
  split_ifs at h with h₁ h₂
  · exact Prod.ext (σ.injective (congrArg Prod.fst h))
      (σ.injective (congrArg Prod.snd h))
  · have hfst := σ.injective (congrArg Prod.fst h)
    have hsnd := σ.injective (congrArg Prod.snd h)
    omega
  · have hfst := σ.injective (congrArg Prod.fst h)
    have hsnd := σ.injective (congrArg Prod.snd h)
    omega
  · exact Prod.ext (σ.injective (congrArg Prod.snd h))
      (σ.injective (congrArg Prod.fst h))

private lemma permuteIncreasingPair_surjective {N : ℕ} (σ : Equiv.Perm (Fin N))
    {b : Fin N × Fin N} (hb : b ∈ increasingPairs N) :
    ∃ a, ∃ _ha : a ∈ increasingPairs N, permuteIncreasingPair σ a = b := by
  let u := σ.symm b.1
  let v := σ.symm b.2
  have hb_lt : b.1 < b.2 := (Finset.mem_filter.mp hb).2
  by_cases huv : u < v
  · refine ⟨(u, v), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨by simp, huv⟩
    · simp only [permuteIncreasingPair, u, v, Equiv.apply_symm_apply, hb_lt,
        ↓reduceIte, Prod.eta]
  · have hvu : v < u := by
      apply lt_of_le_of_ne (not_lt.mp huv)
      intro h
      have : b.1 = b.2 := by simpa [u, v] using congrArg σ h.symm
      exact hb_lt.ne this
    refine ⟨(v, u), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨by simp, hvu⟩
    · simp only [permuteIncreasingPair, u, v, Equiv.apply_symm_apply,
        lt_asymm hb_lt, ↓reduceIte, Prod.eta]

private theorem sum_increasingPairs_perm {N : ℕ} (σ : Equiv.Perm (Fin N))
    (f : Fin N → Fin N → ℝ≥0∞) (hf : ∀ i j, f i j = f j i) :
    ∑ ij ∈ increasingPairs N, f (σ ij.1) (σ ij.2) =
      ∑ ij ∈ increasingPairs N, f ij.1 ij.2 := by
  apply Finset.sum_bij (fun a _ => permuteIncreasingPair σ a)
  · exact fun a ha => permuteIncreasingPair_mem σ ha
  · exact fun a ha b hb => permuteIncreasingPair_injective σ ha hb
  · exact fun b hb => permuteIncreasingPair_surjective σ hb
  · intro a _ha
    simp only [permuteIncreasingPair]
    split_ifs
    · rfl
    · exact hf _ _

/-- Electron repulsion is invariant under every particle-coordinate permutation. -/
theorem electronRepulsion_permutePositions {N : ℕ} (σ : Equiv.Perm (Fin N))
    (x : Configuration N) :
    electronRepulsion (permutePositions σ x) = electronRepulsion x := by
  have hs (i j : Fin N) :
      coulombKernel (particlePosition x i) (particlePosition x j) =
        coulombKernel (particlePosition x j) (particlePosition x i) := by
    simp only [coulombKernel, norm_sub_rev]
  unfold electronRepulsion
  simp_rw [particlePosition_permutePositions]
  rw [← sum_increasingPairs_eq, ← sum_increasingPairs_eq]
  exact sum_increasingPairs_perm σ (fun i j =>
    coulombKernel (particlePosition x i) (particlePosition x j)) hs

/-- Nuclear attraction is invariant under every particle-coordinate permutation. -/
theorem attraction_permutePositions {N M : ℕ} (σ : Equiv.Perm (Fin N))
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (x : Configuration N) :
    attraction z R (permutePositions σ x) = attraction z R x := by
  unfold attraction
  simp_rw [particlePosition_permutePositions]
  exact Equiv.sum_comp σ (fun i => ∑ k, (z k : ℝ≥0∞) *
    coulombKernel (particlePosition x i) (R k))

end LiebThirring

end
