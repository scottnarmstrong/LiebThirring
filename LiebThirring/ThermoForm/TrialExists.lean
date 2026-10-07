/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.TrialConfined
public import LiebThirring.ThermoForm.Infimum

/-! # Normalized trials in every confined sector

Argument thermodynamic confined form estimates: dilation and normalization of the joint
Slater/boson smooth product give nonempty finite-energy sectors.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

theorem exists_normalized_dirichlet_ball_trial (N M q : ℕ) (hq : 1 ≤ q)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) :
    ∃ ψ : DirichletBallFormDomain N M q m L, ‖ψ.val.val‖ = 1 := by
  obtain ⟨f, hf, hc, hL, ha, hn⟩ := exists_compact_schwartz_joint_trial_in_ball N M q hq L
  let c : ℝ := ‖f.toLp 2 (volume : Measure (QuantumConfiguration N M))‖⁻¹
  let g := c • f
  have hga : quantum_antisymmetric (g.toLp 2 volume) := by
    apply quantum_antisymmetric_toLp_of_pointwise
    intro σ X s
    change (c : ℂ) * f (toLp 2 (permutePositions σ X.fst, X.snd)) (permuteSpins σ s) =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ((c : ℂ) * f X s)
    rw [ha]
    ring
  have hgn : nuclear_symmetric (g.toLp 2 volume) := by
    apply nuclear_symmetric_toLp_of_pointwise
    intro τ X s
    change (c : ℂ) * f (toLp 2 (X.fst, permutePositions τ X.snd)) s = (c : ℂ) * f X s
    rw [hn]
  let ψ : QuantumFormDomain N M q :=
    ⟨g.toLp 2 volume, hga, hgn, quantumElectronKineticEnergy_schwartz_lt_top g,
      quantumNuclearKineticEnergy_schwartz_lt_top g⟩
  have hgsub : tsupport g ⊆ tsupport f :=
    tsupport_smul_subset_right (fun _ => c) (fun X => f X)
  have hgc : IsCompact (tsupport g) := hc.of_isClosed_subset (isClosed_tsupport g) hgsub
  have hd : is_dirichlet_ball m L ψ.val :=
    is_dirichlet_ball_of_schwartz m L g hgc (hgsub.trans hL) hga hgn
  exact ⟨⟨ψ, hd⟩, quantum_norm_schwartz_toLp_normalize f hf⟩

theorem confinedGroundStateEnergy_ne_top (N M q : ℕ) (hq : 1 ≤ q) (z : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) :
    confinedGroundStateEnergy N M q z m L ≠ ⊤ := by
  obtain ⟨ψ, hψ⟩ := exists_normalized_dirichlet_ball_trial N M q hq m L
  exact confinedGroundStateEnergy_ne_top_of_trial ψ hψ

end LiebThirring

end
