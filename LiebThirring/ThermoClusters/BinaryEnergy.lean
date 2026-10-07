/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.BinaryTrial
public import LiebThirring.ThermoClusters.ChargeEnergy

/-! # Full energy of the admissible binary cluster trial

The real Coulomb form and full joint energy split into the two
internal cluster energies and the four true marginal cross interactions.
The charge and nuclear mass parameters are unchanged. Both kinetic forms
are finite on the smooth trial carrier, and the author-approved Coulomb
finiteness theorem supplies the assembled real Coulomb form without an
additional finiteness hypothesis.

The grouped full-energy formula uses the actual signed-charge cross energy
from `ChargeEnergy`. Source: Lieb–Lebowitz (1972) II.C, Theorem 2.4,
pp. 329–330, and II.E (2.25).
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal SchwartzMap
namespace LiebThirring
variable {N₁ N₂ M₁ M₂ q : ℕ} {Ω₁ Ω₂ : Set Position}
  (f : SmoothRegionTrial N₁ M₁ q Ω₁) (h : SmoothRegionTrial N₂ M₂ q Ω₂)
  (hΩ : Disjoint Ω₁ Ω₂)

/-- The actual real Coulomb form of the admissible binary trial has the four marginal cross terms. -/
theorem SmoothRegionTrial.quantumCoulombEnergy_assemble (z : ℕ) :
    quantumCoulombEnergy z (f.assemble h hΩ).formDomain =
      quantumCoulombEnergy z f.formDomain + quantumCoulombEnergy z h.formDomain +
      (clusterCoulombInteraction (quantumElectronMeasure f.formDomain.val)
        (quantumElectronMeasure h.formDomain.val)).toReal +
      (z : ℝ)^2 * (clusterCoulombInteraction (quantumNuclearMeasure f.formDomain.val)
        (quantumNuclearMeasure h.formDomain.val)).toReal -
      (z : ℝ) * (clusterCoulombInteraction (quantumElectronMeasure f.formDomain.val)
        (quantumNuclearMeasure h.formDomain.val)).toReal -
      (z : ℝ) * (clusterCoulombInteraction (quantumNuclearMeasure f.formDomain.val)
        (quantumElectronMeasure h.formDomain.val)).toReal := by
  have hfinite := (f.assemble h hΩ).coulomb_lt_top z
  unfold quantumCoulombEnergy
  simpa only [SmoothRegionTrial.formDomain, SmoothRegionTrial.assemble] using
    binaryClusterAssembly_coulomb_toReal_of_finite f.val h.val f.property.1 h.property.1
    f.property.2.2.1 h.property.2.2.1 f.property.2.2.2.1 h.property.2.2.2.1
    Ω₁ Ω₂ f.property.2.1 h.property.2.1 hΩ z f.property.2.2.2.2 h.property.2.2.2.2
    hfinite.1 hfinite.2

/-- The literal full joint energy of the binary assembly is the two internal
full energies plus the four Coulomb cross terms, with the same charge and mass. -/
theorem SmoothRegionTrial.quantumEnergy_assemble_explicit (z : ℕ) (m : {m : ℝ≥0 // 0 < m}) :
    quantumEnergy z m (f.assemble h hΩ).formDomain =
      quantumEnergy z m f.formDomain + quantumEnergy z m h.formDomain +
      (clusterCoulombInteraction (quantumElectronMeasure f.formDomain.val)
        (quantumElectronMeasure h.formDomain.val)).toReal +
      (z : ℝ)^2 * (clusterCoulombInteraction (quantumNuclearMeasure f.formDomain.val)
        (quantumNuclearMeasure h.formDomain.val)).toReal -
      (z : ℝ) * (clusterCoulombInteraction (quantumElectronMeasure f.formDomain.val)
        (quantumNuclearMeasure h.formDomain.val)).toReal -
      (z : ℝ) * (clusterCoulombInteraction (quantumNuclearMeasure f.formDomain.val)
        (quantumElectronMeasure h.formDomain.val)).toReal := by
  unfold quantumEnergy
  rw [f.electronKinetic_assemble h hΩ, f.nuclearKinetic_assemble h hΩ,
    ENNReal.toReal_add f.formDomain.property.2.2.1.ne h.formDomain.property.2.2.1.ne,
    ENNReal.toReal_add f.formDomain.property.2.2.2.ne h.formDomain.property.2.2.2.ne,
    f.quantumCoulombEnergy_assemble h hΩ z]
  ring

/-- The full energy splits into the two internal energies and the actual
signed-charge interaction, with unchanged charge and mass parameters. -/
theorem SmoothRegionTrial.quantumEnergy_assemble (z : ℕ) (m : {m : ℝ≥0 // 0 < m}) :
    quantumEnergy z m (f.assemble h hΩ).formDomain =
      quantumEnergy z m f.formDomain + quantumEnergy z m h.formDomain +
      clusterChargeInteraction z (quantumElectronMeasure f.formDomain.val)
        (quantumNuclearMeasure f.formDomain.val) (quantumElectronMeasure h.formDomain.val)
        (quantumNuclearMeasure h.formDomain.val) := by
  rw [f.quantumEnergy_assemble_explicit h hΩ z m, clusterChargeInteraction]
  ring

end LiebThirring

end
