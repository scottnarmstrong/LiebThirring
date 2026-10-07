/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Thermodynamic.ConfinedGroundStateEnergy

/-!
# Dirichlet form domains for spatial regions

The ball form domain is generalized literally by requiring every
particle coordinate of each compact Schwartz approximant to lie in a spatial
region. Inclusion of regions reuses the same approximants and reverses the
order of the corresponding variational energies.

-/

public section

open MeasureTheory WithLp Set
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- Approximation by symmetric compact smooth states supported with every
spatial particle coordinate in `Ω`, in the full kinetic graph norm. -/
@[expose] def is_dirichlet_region {N M q : ℕ}
    (m : {m : ℝ≥0 // 0 < m}) (Ω : Set Position)
    (ψ : QuantumState N M q) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q),
      let φ : QuantumState N M q :=
        f.toLp 2 (volume : Measure (QuantumConfiguration N M))
      IsCompact (tsupport f) ∧
      tsupport f ⊆ {X | (∀ i : Fin N, particlePosition X.fst i ∈ Ω) ∧
        (∀ k : Fin M, particlePosition X.snd k ∈ Ω)} ∧
      quantum_antisymmetric φ ∧ nuclear_symmetric φ ∧
      ENNReal.ofReal (‖ψ - φ‖ ^ 2) +
        quantumElectronKineticEnergy (ψ - φ) +
        (nuclearKineticCoefficient m : ℝ≥0∞) *
          quantumNuclearKineticEnergy (ψ - φ) < ENNReal.ofReal ε

/-- Enlarging the spatial region preserves membership in its Dirichlet form
closure. -/
theorem is_dirichlet_region_mono {N M q : ℕ}
    {m : {m : ℝ≥0 // 0 < m}} {Ω Ω' : Set Position} (hΩ : Ω ⊆ Ω')
    {ψ : QuantumState N M q} (hψ : is_dirichlet_region m Ω ψ) :
    is_dirichlet_region m Ω' ψ := by
  intro ε hε
  obtain ⟨f, hc, hs, he, hn, hg⟩ := hψ ε hε
  exact ⟨f, hc,
    fun X hX => ⟨fun i => hΩ ((hs hX).1 i), fun k => hΩ ((hs hX).2 k)⟩,
    he, hn, hg⟩

/-- The unnormalized Dirichlet form domain associated with a spatial region. -/
@[expose] def DirichletRegionFormDomain (N M q : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (Ω : Set Position) : Type :=
  {ψ : QuantumFormDomain N M q // is_dirichlet_region m Ω ψ.val}

attribute [reducible] DirichletRegionFormDomain

/-- The complete-order variational infimum on a spatial region. Empty sectors
have value `⊤`, and sectors unbounded below have value `⊥`. -/
@[expose] noncomputable def dirichletRegionGroundStateEnergy (N M q z : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (Ω : Set Position) : EReal :=
  ⨅ ψ : {ψ : DirichletRegionFormDomain N M q m Ω // ‖ψ.val.val‖ = 1},
    (quantumEnergy z m ψ.val.val : EReal)

/-- The region variational infimum on a centered ball is the confined
ground-state energy. -/
theorem dirichletRegionGroundStateEnergy_ball (N M q z : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) :
    dirichletRegionGroundStateEnergy N M q z m
        (Metric.ball (0 : Position) L.val) =
      confinedGroundStateEnergy N M q z m L := by
  rfl

/-- Inclusion of spatial regions reverses the order of their variational
ground-state energies. -/
theorem dirichletRegionGroundStateEnergy_antitone {N M q z : ℕ}
    {m : {m : ℝ≥0 // 0 < m}} {Ω Ω' : Set Position} (hΩ : Ω ⊆ Ω') :
    dirichletRegionGroundStateEnergy N M q z m Ω' ≤
      dirichletRegionGroundStateEnergy N M q z m Ω := by
  unfold dirichletRegionGroundStateEnergy
  apply le_iInf
  intro ψ
  let ψ' : DirichletRegionFormDomain N M q m Ω' :=
    ⟨ψ.val.val, is_dirichlet_region_mono hΩ ψ.val.property⟩
  let u' : {u : DirichletRegionFormDomain N M q m Ω' // ‖u.val.val‖ = 1} :=
    ⟨ψ', ψ.property⟩
  exact iInf_le
    (fun u : {u : DirichletRegionFormDomain N M q m Ω' // ‖u.val.val‖ = 1} =>
      (quantumEnergy z m u.val.val : EReal)) u'

end LiebThirring

end
