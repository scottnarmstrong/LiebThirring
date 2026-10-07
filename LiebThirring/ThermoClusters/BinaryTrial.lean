/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.Trials
public import LiebThirring.ThermoClusters.AssemblyNorm
public import LiebThirring.ThermoClusters.AssemblyStatistics
public import LiebThirring.ThermoClusters.AssemblyEnergy
public import LiebThirring.ThermoClusters.AssemblyMarginals
public import LiebThirring.ThermoClusters.SupportSeparation

/-! # The admissible binary cluster trial

Two normalized compact correlated trials confined to disjoint regions give
an actual normalized smooth trial with both statistics. The defining
wavefunction is the explicit signed-electron/unsigned-nucleus quotient
shuffle, with no orthogonality or invariance assumptions beyond the source
trials. Proof: cluster assembly; Lieb–Lebowitz (1972) II.C, Theorem 2.4, pp. 329–330.
-/

public section
open MeasureTheory Set
open scoped ENNReal SchwartzMap
namespace LiebThirring

variable {N₁ N₂ M₁ M₂ q : ℕ} {Ω₁ Ω₂ : Set Position}
  (f : SmoothRegionTrial N₁ M₁ q Ω₁) (h : SmoothRegionTrial N₂ M₂ q Ω₂)
  (hΩ : Disjoint Ω₁ Ω₂)

/-- The explicit double quotient shuffle is an admissible trial in the union region. -/
@[expose] noncomputable def SmoothRegionTrial.assemble :
    SmoothRegionTrial (N₁+N₂) (M₁+M₂) q (Ω₁ ∪ Ω₂) :=
  ⟨binaryClusterAssembly f.val h.val f.property.1 h.property.1
      f.property.2.2.1 h.property.2.2.1 f.property.2.2.2.1 h.property.2.2.2.1,
    isCompact_tsupport_binaryClusterAssembly _ _ _ _ _ _ _ _,
    binaryClusterAssembly_supported_union _ _ _ _ _ _ _ _ Ω₁ Ω₂
      f.property.2.1 h.property.2.1,
    quantum_antisymmetric_binaryClusterAssembly _ _ _ _ _ _ _ _,
    nuclear_symmetric_binaryClusterAssembly _ _ _ _ _ _ _ _,
    norm_binaryClusterAssembly_toLp _ _ _ _ _ _ _ _ Ω₁ Ω₂ hΩ
      f.property.2.1 h.property.2.1 f.property.2.2.2.2 h.property.2.2.2.2⟩

/-- Electron kinetic energy adds for the actual assembled normalized trial. -/
theorem SmoothRegionTrial.electronKinetic_assemble :
    quantumElectronKineticEnergy (f.assemble h hΩ).formDomain.val =
      quantumElectronKineticEnergy f.formDomain.val +
      quantumElectronKineticEnergy h.formDomain.val :=
  quantumElectronKineticEnergy_binaryClusterAssembly_of_normalized _ _ _ _ _ _ _ _
    Ω₁ Ω₂ f.property.2.1 h.property.2.1 hΩ f.property.2.2.2.2 h.property.2.2.2.2

/-- Nuclear kinetic energy adds for the actual assembled normalized trial. -/
theorem SmoothRegionTrial.nuclearKinetic_assemble :
    quantumNuclearKineticEnergy (f.assemble h hΩ).formDomain.val =
      quantumNuclearKineticEnergy f.formDomain.val +
      quantumNuclearKineticEnergy h.formDomain.val :=
  quantumNuclearKineticEnergy_binaryClusterAssembly_of_normalized _ _ _ _ _ _ _ _
    Ω₁ Ω₂ f.property.2.1 h.property.2.1 hΩ f.property.2.2.2.2 h.property.2.2.2.2

/-- The actual electron number measure is the sum of the two cluster number measures. -/
theorem SmoothRegionTrial.electronMeasure_assemble :
    quantumElectronMeasure (f.assemble h hΩ).formDomain.val =
      quantumElectronMeasure f.formDomain.val + quantumElectronMeasure h.formDomain.val :=
  quantumElectronMeasure_binaryClusterAssembly _ _ _ _ _ _ _ _
    Ω₁ Ω₂ f.property.2.1 h.property.2.1 hΩ f.property.2.2.2.2 h.property.2.2.2.2

/-- The actual nuclear number measure is the sum of the two cluster number measures. -/
theorem SmoothRegionTrial.nuclearMeasure_assemble :
    quantumNuclearMeasure (f.assemble h hΩ).formDomain.val =
      quantumNuclearMeasure f.formDomain.val + quantumNuclearMeasure h.formDomain.val :=
  quantumNuclearMeasure_binaryClusterAssembly _ _ _ _ _ _ _ _
    Ω₁ Ω₂ f.property.2.1 h.property.2.1 hΩ f.property.2.2.2.2 h.property.2.2.2.2

include hΩ in
/-- All four true cross pair integrals are finite from compact support and disjoint confinement. -/
theorem SmoothRegionTrial.crossCoulomb_lt_top :
    clusterCoulombInteraction (quantumElectronMeasure f.formDomain.val)
        (quantumElectronMeasure h.formDomain.val) < ⊤ ∧
    clusterCoulombInteraction (quantumElectronMeasure f.formDomain.val)
        (quantumNuclearMeasure h.formDomain.val) < ⊤ ∧
    clusterCoulombInteraction (quantumNuclearMeasure f.formDomain.val)
        (quantumElectronMeasure h.formDomain.val) < ⊤ ∧
    clusterCoulombInteraction (quantumNuclearMeasure f.formDomain.val)
        (quantumNuclearMeasure h.formDomain.val) < ⊤ :=
  four_clusterCoulombInteractions_schwartz_lt_top f.val h.val f.property.1 h.property.1
    Ω₁ Ω₂ hΩ f.property.2.1 h.property.2.1

end LiebThirring
end
