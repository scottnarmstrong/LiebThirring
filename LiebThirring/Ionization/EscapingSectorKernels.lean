/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.EscapingSectorSlices
public import LiebThirring.Ionization.EscapingExpectations
public import LiebThirring.Ionization.EscapingMass

/-! # Coulomb kernel comparisons for an escaping IMS sector -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal Classical

namespace LiebThirring

open Sobolev
open Variational

/-- A selected coordinate of subset insertion is the corresponding coordinate of the
ordered selected configuration. -/
theorem particlePosition_subsetOrderedInsertion_mem {N k : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (y : SubsetSpectatorConfiguration S) (x : Configuration k)
    (j : Fin k) :
    particlePosition (subsetOrderedInsertion S e (y, x)) (e j).val = particlePosition x j := by
  ext a
  change subsetOrderedInsertion S e (y, x) ((e j).val, a) = x (j, a)
  change subsetInsertionMeasurableEquiv S
    (configurationReindexMeasurableEquiv e x, y) ((e j).val, a) = _
  rw [subsetInsertion_apply_mem]
  simp only [configurationReindexMeasurableEquiv, MeasurableEquiv.trans_apply,
    MeasurableEquiv.toLp_symm_apply, MeasurableEquiv.toLp_apply]
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : S × Fin 3 => ℝ) (e.prodCongr (Equiv.refl (Fin 3))) x.ofLp (j, a)

private def sectorIncreasingPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ.product Finset.univ).filter (fun ij => ij.1 < ij.2)

private theorem electronRepulsion_eq_sectorIncreasingPairs {n : ℕ} (x : Configuration n) :
    electronRepulsion x = ∑ ij ∈ sectorIncreasingPairs n,
      coulombKernel (particlePosition x ij.1) (particlePosition x ij.2) := by
  unfold electronRepulsion sectorIncreasingPairs
  simp only [Finset.sum_filter]
  simpa using (Finset.sum_product (Finset.univ : Finset (Fin n))
    (Finset.univ : Finset (Fin n))
    (fun ij : Fin n × Fin n => if ij.1 < ij.2 then
      coulombKernel (particlePosition x ij.1) (particlePosition x ij.2) else 0)).symm

private def selectedPairEmbedding {N k : ℕ} (S : Set (Fin N)) (e : Fin k ≃ S)
    (ij : Fin k × Fin k) : Fin N × Fin N :=
  if (e ij.1).val < (e ij.2).val then ((e ij.1).val, (e ij.2).val)
  else ((e ij.2).val, (e ij.1).val)

private theorem selectedPairEmbedding_mem {N k : ℕ} (S : Set (Fin N)) (e : Fin k ≃ S)
    {ij : Fin k × Fin k} (hij : ij ∈ sectorIncreasingPairs k) :
    selectedPairEmbedding S e ij ∈ sectorIncreasingPairs N := by
  simp only [sectorIncreasingPairs, Finset.mem_filter] at hij ⊢
  simp only [selectedPairEmbedding]
  split_ifs with h
  · exact ⟨by simp, h⟩
  · exact ⟨by simp, lt_of_le_of_ne (not_lt.mp h)
      (fun heq => hij.2.ne (e.injective (Subtype.ext heq.symm)))⟩

private theorem selectedPairEmbedding_injective {N k : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) : Set.InjOn (selectedPairEmbedding S e) (sectorIncreasingPairs k) := by
  intro a ha b hb h
  have ha' : a.1 < a.2 := (Finset.mem_filter.mp ha).2
  have hb' : b.1 < b.2 := (Finset.mem_filter.mp hb).2
  simp only [selectedPairEmbedding] at h
  split_ifs at h with h₁ h₂
  · exact Prod.ext (e.injective (Subtype.ext (congrArg Prod.fst h)))
      (e.injective (Subtype.ext (congrArg Prod.snd h)))
  · have hfst := e.injective (Subtype.ext (congrArg Prod.fst h))
    have hsnd := e.injective (Subtype.ext (congrArg Prod.snd h))
    exfalso
    rw [hfst, hsnd] at ha'
    exact lt_asymm ha' hb'
  · have hfst := e.injective (Subtype.ext (congrArg Prod.snd h))
    have hsnd := e.injective (Subtype.ext (congrArg Prod.fst h))
    exfalso
    rw [hfst, hsnd] at ha'
    exact lt_asymm ha' hb'
  · exact Prod.ext (e.injective (Subtype.ext (congrArg Prod.snd h)))
      (e.injective (Subtype.ext (congrArg Prod.fst h)))

/-- Full electron repulsion dominates the repulsion internal to any selected block. -/
theorem electronRepulsion_subsetOrderedInsertion_le {N k : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (y : SubsetSpectatorConfiguration S) (x : Configuration k) :
    electronRepulsion x ≤ electronRepulsion (subsetOrderedInsertion S e (y, x)) := by
  rw [electronRepulsion_eq_sectorIncreasingPairs,
    electronRepulsion_eq_sectorIncreasingPairs]
  apply Finset.sum_le_sum_of_injOn (selectedPairEmbedding S e)
    (selectedPairEmbedding_injective S e)
  · exact Finset.image_subset_iff.mpr fun ij hij => selectedPairEmbedding_mem S e hij
  · intro ij hij
    simp only [selectedPairEmbedding]
    split_ifs
    · rw [particlePosition_subsetOrderedInsertion_mem,
        particlePosition_subsetOrderedInsertion_mem]
    · rw [particlePosition_subsetOrderedInsertion_mem,
        particlePosition_subsetOrderedInsertion_mem]
      simp only [coulombKernel, norm_sub_rev]
      exact le_rfl
  · intro _ _ _
    exact bot_le

private theorem coulombKernel_zero_le_inv_of_lt_norm {R : ℝ} (_hR : 0 < R)
    {x : Position} (hx : R < ‖x‖) :
    coulombKernel x 0 ≤ (ENNReal.ofReal R)⁻¹ := by
  unfold coulombKernel
  simp only [sub_zero]
  exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hx.le)

private theorem sum_selected_atomic_attraction {N k : ℕ} (Z : ℝ≥0)
    (S : Finset (Fin N)) (e : Fin k ≃ (S : Set (Fin N))) (X : Configuration N) :
    (∑ j : Fin k, (Z : ℝ≥0∞) * coulombKernel (particlePosition X (e j).val) 0) =
      ∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => i ∈ S),
        (Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0 := by
  apply Finset.sum_bij (fun j _ => (e j).val)
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e j).property⟩
  · intro a _ b _ hab
    exact e.injective (Subtype.ext hab)
  · intro i hi
    obtain ⟨-, hiS⟩ := Finset.mem_filter.mp hi
    obtain ⟨j, hj⟩ := e.surjective ⟨i, hiS⟩
    exact ⟨j, Finset.mem_univ _, congrArg Subtype.val hj⟩
  · intro _ _
    rfl

/-- Full atomic attraction dominates the attraction internal to the selected block. -/
theorem attraction_subsetOrderedInsertion_selected_le {N k : ℕ} (Z : ℝ≥0)
    (S : Finset (Fin N)) (e : Fin k ≃ (S : Set (Fin N)))
    (y : SubsetSpectatorConfiguration (S : Set (Fin N))) (x : Configuration k) :
    attraction (fun _ : Fin 1 => Z) (fun _ => 0) x ≤
      attraction (fun _ : Fin 1 => Z) (fun _ => 0)
        (subsetOrderedInsertion (S : Set (Fin N)) e (y, x)) := by
  classical
  let X := subsetOrderedInsertion (S : Set (Fin N)) e (y, x)
  rw [attraction, attraction]
  simp only [Fin.sum_univ_one]
  rw [show (∑ i : Fin N, (Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0) =
      (∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => i ∈ S),
        (Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0) +
      (∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => i ∉ S),
        (Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0) by
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ S) _).symm]
  rw [← sum_selected_atomic_attraction Z S e X]
  have hpos (j : Fin k) : particlePosition X (e j).val = particlePosition x j :=
    particlePosition_subsetOrderedInsertion_mem (S : Set (Fin N)) e y x j
  simp_rw [hpos]
  exact le_add_right le_rfl

/-- On the support of a sector, full atomic attraction is at most the selected-block
attraction plus `Z/R` for every complementary particle. -/
theorem attraction_subsetOrderedInsertion_le_of_sector_ne_zero {N k : ℕ}
    {R : ℝ} (hR : 0 < R) (Z : ℝ≥0) (S : Finset (Fin N))
    (e : Fin k ≃ (S : Set (Fin N)))
    (y : SubsetSpectatorConfiguration (S : Set (Fin N))) (x : Configuration k)
    (hsector : imsSectorWeight (imsChi R) (imsEta R) S
      (subsetOrderedInsertion (S : Set (Fin N)) e (y, x)) ≠ 0) :
    attraction (fun _ : Fin 1 => Z) (fun _ => 0)
        (subsetOrderedInsertion (S : Set (Fin N)) e (y, x)) ≤
      attraction (fun _ : Fin 1 => Z) (fun _ => 0) x +
        (N - k : ℝ≥0∞) * (Z : ℝ≥0∞) * (ENNReal.ofReal R)⁻¹ := by
  classical
  let X := subsetOrderedInsertion (S : Set (Fin N)) e (y, x)
  have hout (i : Fin N) (hi : i ∉ S) :
      (Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0 ≤
        (Z : ℝ≥0∞) * (ENNReal.ofReal R)⁻¹ := by
    exact mul_le_mul le_rfl (coulombKernel_zero_le_inv_of_lt_norm hR
      (norm_lt_particlePosition_of_imsSectorWeight_ne_zero hR S hsector hi)) bot_le bot_le
  rw [attraction, attraction]
  simp only [Fin.sum_univ_one]
  rw [show (∑ i : Fin N, (Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0) =
      (∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => i ∈ S),
        (Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0) +
      (∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => i ∉ S),
        (Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0) by
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ S) _).symm]
  rw [← sum_selected_atomic_attraction Z S e X]
  have hpos (j : Fin k) : particlePosition X (e j).val = particlePosition x j :=
    particlePosition_subsetOrderedInsertion_mem (S : Set (Fin N)) e y x j
  simp_rw [hpos]
  apply add_le_add_right
  calc
    (∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => i ∉ S),
        (Z : ℝ≥0∞) * coulombKernel (particlePosition X i) 0)
        ≤ ∑ _i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => i ∉ S),
          (Z : ℝ≥0∞) * (ENNReal.ofReal R)⁻¹ :=
      Finset.sum_le_sum fun i hi => hout i (Finset.mem_filter.mp hi).2
    _ = (N - k : ℝ≥0∞) * (Z : ℝ≥0∞) * (ENNReal.ofReal R)⁻¹ := by
      have hcardS : S.card = k := by
        simpa using Fintype.card_congr e.symm
      have hfilter : (Finset.univ : Finset (Fin N)).filter (fun i => i ∉ S) =
          Finset.univ \ S := by ext i; simp
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [hfilter, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin,
        Finset.inter_eq_left.mpr (Finset.subset_univ S), hcardS]
      push_cast
      ring

/-- The pulled-back selected repulsion expectation is bounded by the full repulsion
expectation for every state. -/
theorem lintegral_subsetSelectedRepulsion_le {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (v : State N q) :
    (∫⁻ X : Configuration N,
      electronRepulsion ((subsetOrderedInsertion S e).symm X).2 * ‖v X‖ₑ ^ 2) ≤
      ∫⁻ X : Configuration N, electronRepulsion X * ‖v X‖ₑ ^ 2 := by
  apply lintegral_mono
  intro X
  apply mul_le_mul_of_nonneg_right
  · let z := (subsetOrderedInsertion S e).symm X
    have h := electronRepulsion_subsetOrderedInsertion_le S e z.1 z.2
    rw [(subsetOrderedInsertion S e).apply_symm_apply X] at h
    exact h
  · exact bot_le

end LiebThirring

end
