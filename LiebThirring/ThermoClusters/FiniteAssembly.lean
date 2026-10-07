/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.BinaryEnergy
public import LiebThirring.ThermoClusters.FinitePairs

/-!
# Finite assembly of confined correlated clusters

Induction uses the actual normalized binary shuffle and the actual vacuum.
All statistics and normalization are contained in `SmoothRegionTrial`; the
kinetic energies and one-body number measures add exactly.
Lieb–Lebowitz (1972) II.C, Theorem 2.4, pp. 329–330;
Lieb–Lebowitz (1972) II.E, (2.25).
-/

public section
open MeasureTheory Set Function
open scoped ENNReal NNReal SchwartzMap
namespace LiebThirring

/-- One actual finite assembled trial realizes both additive kinetic energies,
both additive number measures, and the full pairwise charge-energy identity. -/
theorem exists_smoothRegionTrial_finite_assembly_energy (k q z : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (N M : Fin k → ℕ) (Ω : Fin k → Set Position)
    (f : ∀ i, SmoothRegionTrial (N i) (M i) q (Ω i))
    (hΩ : Pairwise (Disjoint on Ω)) :
    ∃ F : SmoothRegionTrial (∑ i, N i) (∑ i, M i) q (⋃ i, Ω i),
      quantumElectronKineticEnergy F.formDomain.val =
        ∑ i, quantumElectronKineticEnergy (f i).formDomain.val ∧
      quantumNuclearKineticEnergy F.formDomain.val =
        ∑ i, quantumNuclearKineticEnergy (f i).formDomain.val ∧
      quantumElectronMeasure F.formDomain.val =
        ∑ i, quantumElectronMeasure (f i).formDomain.val ∧
      quantumNuclearMeasure F.formDomain.val =
        ∑ i, quantumNuclearMeasure (f i).formDomain.val ∧
      quantumEnergy z m F.formDomain = (∑ i, quantumEnergy z m (f i).formDomain) +
        ∑ i, ∑ j with i < j, clusterChargeInteraction z
          (quantumElectronMeasure (f i).formDomain.val)
          (quantumNuclearMeasure (f i).formDomain.val)
          (quantumElectronMeasure (f j).formDomain.val)
          (quantumNuclearMeasure (f j).formDomain.val) := by
  classical
  induction k with
  | zero =>
    simp only [Fin.sum_univ_zero, add_zero]
    obtain ⟨F⟩ := exists_smoothRegionTrial_vacuum q (⋃ i, Ω i)
    exact ⟨F, quantumElectronKineticEnergy_vacuum _,
      quantumNuclearKineticEnergy_vacuum _,
      by simp only [quantumElectronMeasure, Fin.sum_univ_zero],
      by simp only [quantumNuclearMeasure, Fin.sum_univ_zero],
      quantumEnergy_vacuum z m _⟩
  | succ k ih =>
    have ht : Pairwise (Disjoint on fun i : Fin k => Ω i.succ) :=
      fun i j hij => hΩ (fun heq => hij (Fin.succ_inj.mp heq))
    obtain ⟨F, hFe, hFn, hFμ, hFν, hFE⟩ :=
      ih (fun i => N i.succ) (fun i => M i.succ)
        (fun i => Ω i.succ) (fun i => f i.succ) ht
    have hh : Disjoint (Ω 0) (⋃ i : Fin k, Ω i.succ) :=
      disjoint_iUnion_right.mpr (fun i => hΩ (Ne.symm (Fin.succ_ne_zero i)))
    have hr : (⋃ i : Fin (k+1), Ω i) = Ω 0 ∪ ⋃ i : Fin k, Ω i.succ := by
      ext X
      simp only [mem_iUnion, mem_union, Fin.exists_fin_succ]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hr]
    refine ⟨(f 0).assemble F hh, ?_, ?_, ?_, ?_, ?_⟩
    · rw [SmoothRegionTrial.electronKinetic_assemble, hFe, Fin.sum_univ_succ]
    · rw [SmoothRegionTrial.nuclearKinetic_assemble, hFn, Fin.sum_univ_succ]
    · rw [SmoothRegionTrial.electronMeasure_assemble, hFμ, Fin.sum_univ_succ]
    · rw [SmoothRegionTrial.nuclearMeasure_assemble, hFν, Fin.sum_univ_succ]
    · have hpair (i : Fin k) := SmoothRegionTrial.crossCoulomb_lt_top
        (f 0) (f i.succ) (hΩ (Ne.symm (Fin.succ_ne_zero i)))
      have hc := clusterChargeInteraction_sum_right z
        (quantumElectronMeasure (f 0).formDomain.val)
        (quantumNuclearMeasure (f 0).formDomain.val)
        (fun i : Fin k => quantumElectronMeasure (f i.succ).formDomain.val)
        (fun i : Fin k => quantumNuclearMeasure (f i.succ).formDomain.val)
        (fun i => (hpair i).1) (fun i => (hpair i).2.2.2)
        (fun i => (hpair i).2.1) (fun i => (hpair i).2.2.1)
      rw [SmoothRegionTrial.quantumEnergy_assemble, hFE, hFμ, hFν, hc,
        Fin.sum_univ_succ, sum_orderedPairs_fin_succ]
      ring

end LiebThirring
end
