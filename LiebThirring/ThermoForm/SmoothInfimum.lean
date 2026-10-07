/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.Infimum
public import LiebThirring.ThermoForm.SmoothCore

/-! # The confined variational problem on its smooth core

Argument thermodynamic confined form estimates. This module packages normalized compactly supported Schwartz
states with the prescribed electron and nuclear statistics, embeds them in the
Dirichlet form carrier, and records the easy inclusion inequality between the two infima.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- A normalized compactly supported smooth joint state inside the confinement ball, with the
prescribed electron and nuclear statistics. -/
@[expose] def SmoothConfinedTrial (N M q : ℕ) (L : {L : ℝ // 0 < L}) : Type :=
  {f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q) //
    IsCompact (tsupport f) ∧
    tsupport f ⊆ {X | (∀ i : Fin N, particlePosition X.fst i ∈
      Metric.ball (0 : Position) L.val) ∧
      (∀ k : Fin M, particlePosition X.snd k ∈ Metric.ball (0 : Position) L.val)} ∧
    quantum_antisymmetric (f.toLp 2 volume) ∧
    nuclear_symmetric (f.toLp 2 volume) ∧
    ‖f.toLp 2 (volume : Measure (QuantumConfiguration N M))‖ = 1}

/-- A smooth confined trial regarded as an element of the full finite-kinetic form domain. -/
@[expose] noncomputable def SmoothConfinedTrial.formDomain {N M q : ℕ}
    {L : {L : ℝ // 0 < L}} (f : SmoothConfinedTrial N M q L) :
    QuantumFormDomain N M q :=
  ⟨f.val.toLp 2 volume, f.property.2.2.1, f.property.2.2.2.1,
    quantumElectronKineticEnergy_schwartz_lt_top f.val,
    quantumNuclearKineticEnergy_schwartz_lt_top f.val⟩

/-- A smooth confined trial regarded as an element of the Dirichlet form carrier. -/
@[expose] noncomputable def SmoothConfinedTrial.dirichletFormDomain {N M q : ℕ}
    (m : {m : ℝ≥0 // 0 < m}) {L : {L : ℝ // 0 < L}}
    (f : SmoothConfinedTrial N M q L) : DirichletBallFormDomain N M q m L :=
  ⟨f.formDomain, is_dirichlet_ball_of_schwartz m L f.val f.property.1 f.property.2.1
    f.property.2.2.1 f.property.2.2.2.1⟩

@[simp] theorem SmoothConfinedTrial.norm_dirichletFormDomain {N M q : ℕ}
    (m : {m : ℝ≥0 // 0 < m}) {L : {L : ℝ // 0 < L}}
    (f : SmoothConfinedTrial N M q L) : ‖f.dirichletFormDomain m |>.val.val‖ = 1 :=
  f.property.2.2.2.2

/-- The real-energy infimum over normalized compactly supported smooth trials. -/
@[expose] noncomputable def smoothConfinedGroundStateEnergy (N M q z : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) : EReal :=
  ⨅ f : SmoothConfinedTrial N M q L,
    (quantumEnergy z m f.formDomain : EReal)

/-- Inclusion of smooth confined trials in the Dirichlet form domain gives one half of
the smooth-core characterization of the variational infimum. -/
theorem confinedGroundStateEnergy_le_smoothConfinedGroundStateEnergy
    (N M q z : ℕ) (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) :
    confinedGroundStateEnergy N M q z m L ≤
      smoothConfinedGroundStateEnergy N M q z m L := by
  apply le_iInf
  intro f
  exact confinedGroundStateEnergy_le_trial (f.dirichletFormDomain m)
    (SmoothConfinedTrial.norm_dirichletFormDomain m f)

end LiebThirring

end
