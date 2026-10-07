/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.ClusterTensor
public import LiebThirring.Defs.Coulomb

/-! # Internal and cross potentials of an ordered joint product

Contiguous label blocks split each same-species pair sum into the two
internal pair sums and one cross sum; opposite-species pairs split into
four blocks. This is the pointwise Coulomb algebra for the cluster assembly.
-/

public section
open WithLp
open scoped ENNReal NNReal
namespace LiebThirring

/-- Unordered pairs split into internal pairs and cross pairs of contiguous blocks. -/
theorem cluster_orderedPairSum_add {A : Type*} [AddCommMonoid A] (n k : ℕ)
    (f : Fin (n+k) → Fin (n+k) → A) :
    (∑ i : Fin (n+k), ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j) =
    (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      f (Fin.castAdd k i) (Fin.castAdd k j)) +
    (∑ i : Fin k, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      f (Fin.natAdd n i) (Fin.natAdd n j)) +
    ∑ i : Fin n, ∑ j : Fin k, f (Fin.castAdd k i) (Fin.natAdd n j) := by
  classical
  have hll (i j : Fin n) : Fin.castAdd k i < Fin.castAdd k j ↔ i < j := by rfl
  have hrr (i j : Fin k) : Fin.natAdd n i < Fin.natAdd n j ↔ i < j := by
    simp only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left]
  have hlr (i : Fin n) (j : Fin k) : Fin.castAdd k i < Fin.natAdd n j := by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have hrl (i : Fin k) (j : Fin n) : ¬ Fin.natAdd n i < Fin.castAdd k j := by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  simp only [Finset.sum_filter, Fin.sum_univ_add, hll, hrr, hlr, hrl,
    ite_true, ite_false, Finset.sum_add_distrib, Finset.sum_const_zero, add_zero]
  ac_rfl

/-- Electron repulsion splits into the internal and cross electron pair potentials. -/
theorem electronRepulsion_configurationClusterSplit {n k : ℕ}
    (x : Configuration (n+k)) :
    electronRepulsion x =
      electronRepulsion (configurationClusterSplit n k x).fst +
      electronRepulsion (configurationClusterSplit n k x).snd +
      ∑ i : Fin n, ∑ j : Fin k,
        coulombKernel (particlePosition (configurationClusterSplit n k x).fst i)
          (particlePosition (configurationClusterSplit n k x).snd j) := by
  exact cluster_orderedPairSum_add n k (fun i j =>
        coulombKernel (particlePosition x i) (particlePosition x j))

/-- Constant-charge nuclear repulsion splits into two internal and one cross potential. -/
theorem nuclearRepulsion_configurationClusterSplit {n k : ℕ} (z : ℝ≥0)
    (x : Configuration (n+k)) :
    nuclearRepulsion (fun _ => z) (particlePosition x) =
      nuclearRepulsion (fun _ => z) (particlePosition (configurationClusterSplit n k x).fst) +
      nuclearRepulsion (fun _ => z) (particlePosition (configurationClusterSplit n k x).snd) +
      ∑ i : Fin n, ∑ j : Fin k,
        ((z : ℝ≥0∞)*(z : ℝ≥0∞)) *
          coulombKernel (particlePosition (configurationClusterSplit n k x).fst i)
            (particlePosition (configurationClusterSplit n k x).snd j) := by
  exact cluster_orderedPairSum_add n k (fun i j =>
        ((z : ℝ≥0∞)*(z : ℝ≥0∞)) * coulombKernel (particlePosition x i) (particlePosition x j))

/-- Attraction splits into both internal and both cross electron–nucleus potentials. -/
theorem attraction_quantumClusterSplit {n₁ n₂ m₁ m₂ : ℕ} (z : ℝ≥0)
    (X : QuantumConfiguration (n₁+n₂) (m₁+m₂)) :
    let Y := (quantumClusterSplit n₁ n₂ m₁ m₂ X).fst
    let Z := (quantumClusterSplit n₁ n₂ m₁ m₂ X).snd
    attraction (fun _ => z) (particlePosition X.snd) X.fst =
      attraction (fun _ => z) (particlePosition Y.snd) Y.fst +
      attraction (fun _ => z) (particlePosition Z.snd) Z.fst +
      (∑ i : Fin n₁, ∑ k : Fin m₂, (z : ℝ≥0∞) *
        coulombKernel (particlePosition Y.fst i) (particlePosition Z.snd k)) +
      (∑ i : Fin n₂, ∑ k : Fin m₁, (z : ℝ≥0∞) *
        coulombKernel (particlePosition Z.fst i) (particlePosition Y.snd k)) := by
  dsimp only
  simp only [attraction, Fin.sum_univ_add, Finset.sum_add_distrib]
  simp only [quantumClusterSplit, jointBlockInterchange]
  ac_rfl

end LiebThirring
end
