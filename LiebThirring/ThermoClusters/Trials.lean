/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoClusters.Domains
public import LiebThirring.ThermoForm.SmoothInfimum
public import LiebThirring.Thermodynamic.QuantumCoulombFinite
import LiebThirring.ThermoForm.Approximation

/-! # Compact normalized cluster trials in spatial regions

This is the region version of confined form estimates's `SmoothConfinedTrial`, with the same
joint Schwartz representative, statistics and normalization. Its form
and graph-closure inclusion reuse the joint-form API. The vacuum is obtained
from the existing normalized smooth core, including spin multiplicity zero.

-/

public section
open MeasureTheory WithLp Set
open scoped ENNReal NNReal SchwartzMap
namespace LiebThirring

/-- A normalized compact joint smooth trial with every particle in the spatial region. -/
@[expose] def SmoothRegionTrial (N M q : ℕ) (Ω : Set Position) : Type :=
  {f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q) //
    IsCompact (tsupport f) ∧
    tsupport f ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω) ∧
      (∀ k, particlePosition X.snd k ∈ Ω)} ∧
    quantum_antisymmetric (f.toLp 2 volume) ∧
    nuclear_symmetric (f.toLp 2 volume) ∧
    ‖f.toLp 2 (volume : Measure (QuantumConfiguration N M))‖ = 1}

/-- Reuse confined form estimates's finite-kinetic smooth core to view a region trial in the form carrier. -/
@[expose] noncomputable def SmoothRegionTrial.formDomain {N M q : ℕ} {Ω : Set Position}
    (f : SmoothRegionTrial N M q Ω) : QuantumFormDomain N M q :=
  ⟨f.val.toLp 2 volume, f.property.2.2.1, f.property.2.2.2.1,
    quantumElectronKineticEnergy_schwartz_lt_top f.val,
    quantumNuclearKineticEnergy_schwartz_lt_top f.val⟩

/-- A compact smooth trial belongs to the literal region graph closure. -/
theorem is_dirichlet_region_of_schwartz {N M q : ℕ}
    (m : {m : ℝ≥0 // 0 < m}) (Ω : Set Position)
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) (hc : IsCompact (tsupport f))
    (hp : tsupport f ⊆ {X | (∀ i, particlePosition X.fst i ∈ Ω) ∧
      (∀ k, particlePosition X.snd k ∈ Ω)})
    (ha : quantum_antisymmetric (f.toLp 2 volume)) (hn : nuclear_symmetric (f.toLp 2 volume)) :
    is_dirichlet_region m Ω (f.toLp 2 volume) := by
  intro ε hε
  refine ⟨f, hc, hp, ha, hn, ?_⟩
  rw [sub_self, quantumElectronKineticEnergy_zero, quantumNuclearKineticEnergy_zero]
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero,
    add_zero, mul_zero] using ENNReal.ofReal_pos.mpr hε

/-- A smooth region trial is an admissible trial for its actual Dirichlet region energy. -/
@[expose] noncomputable def SmoothRegionTrial.dirichletFormDomain {N M q : ℕ}
    (m : {m : ℝ≥0 // 0 < m}) {Ω : Set Position} (f : SmoothRegionTrial N M q Ω) :
    DirichletRegionFormDomain N M q m Ω :=
  ⟨f.formDomain, is_dirichlet_region_of_schwartz m Ω f.val f.property.1 f.property.2.1
    f.property.2.2.1 f.property.2.2.2.1⟩

/-- Trial normalization is exactly the state's normalization. -/
theorem SmoothRegionTrial.norm_formDomain {N M q : ℕ} {Ω : Set Position}
    (f : SmoothRegionTrial N M q Ω) : ‖f.formDomain.val‖ = 1 := f.property.2.2.2.2

/-- Both actual Coulomb expectations of a smooth cluster are finite. -/
theorem SmoothRegionTrial.coulomb_lt_top {N M q : ℕ} {Ω : Set Position}
    (f : SmoothRegionTrial N M q Ω) (z : ℕ) :
    quantumRepulsionEnergy z (f.val.toLp 2 volume) < ⊤ ∧
      quantumAttractionEnergy z (f.val.toLp 2 volume) < ⊤ :=
  quantum_coulomb_lt_top z f.formDomain

/-- The normalized smooth vacuum exists in every spatial region, including the empty one. -/
theorem exists_smoothRegionTrial_vacuum (q : ℕ) (Ω : Set Position) :
    Nonempty (SmoothRegionTrial 0 0 q Ω) := by
  let m : {m : ℝ≥0 // 0 < m} := ⟨1, by norm_num⟩
  let L : {L : ℝ // 0 < L} := ⟨1, by norm_num⟩
  obtain ⟨ψ, hψ⟩ := exists_normalized_dirichlet_vacuum q m L
  obtain ⟨f, hc, _, ha, hn, hnorm, _⟩ :=
    exists_normalized_schwartz_graph_approximation m L ψ hψ 1 (by norm_num)
  exact ⟨⟨f, hc, fun _X _ => ⟨fun i => Fin.elim0 i, fun k => Fin.elim0 k⟩, ha, hn, hnorm⟩⟩

/-- Enlarging a cluster region changes no wavefunction, normalization or energy. -/
@[expose] def SmoothRegionTrial.enlarge {N M q : ℕ} {Ω Ω' : Set Position}
    (hΩ : Ω ⊆ Ω') (f : SmoothRegionTrial N M q Ω) : SmoothRegionTrial N M q Ω' :=
  ⟨f.val, f.property.1, fun _X hX =>
    ⟨fun i => hΩ ((f.property.2.1 hX).1 i), fun k => hΩ ((f.property.2.1 hX).2 k)⟩,
    f.property.2.2⟩

end LiebThirring
end
