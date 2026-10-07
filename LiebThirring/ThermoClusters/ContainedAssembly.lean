/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.FiniteAssembly

/-! # Finite cluster assembly inside a prescribed spatial region

This is the literal ambient-region version of the cluster assembly. All balls
and the optional arbitrary extra region are simply members of one finite
disjoint family. The same global trial has both statistics, unit norm,
compact support, additive kinetic energies and marginals, and the complete
energy formula. Source: Lieb–Lebowitz (1972) II.C, Theorem 2.4, pp. 329–330; II.E,
p. 331, before (2.25).
-/

public section
open MeasureTheory Set Function
open scoped ENNReal NNReal
namespace LiebThirring

/-- The finite source cluster family assembles into the ambient region with all
kinetic, marginal and full-energy identities realized by the same actual trial. -/
theorem exists_smoothRegionTrial_finite_assembly_in_region (k q z : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (N M : Fin k → ℕ)
    (Ω : Fin k → Set Position) (Λ : Set Position)
    (f : ∀ i, SmoothRegionTrial (N i) (M i) q (Ω i))
    (hΩ : Pairwise (Disjoint on Ω)) (hΛ : ∀ i, Ω i ⊆ Λ) :
    ∃ F : SmoothRegionTrial (∑ i, N i) (∑ i, M i) q Λ,
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
  obtain ⟨F, he, hn, hμ, hν, hE⟩ :=
    exists_smoothRegionTrial_finite_assembly_energy k q z m N M Ω f hΩ
  have hs : (⋃ i, Ω i) ⊆ Λ := iUnion_subset hΛ
  exact ⟨F.enlarge hs, he, hn, hμ, hν, hE⟩

end LiebThirring
end
