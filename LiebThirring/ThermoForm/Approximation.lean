/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.NormalizedCore

/-! # Normalized compact smooth approximation in the full joint form norm -/

public section

open MeasureTheory WithLp Set
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- Every normalized confined form-domain state has normalized compact Schwartz approximants
with the prescribed two species statistics and arbitrarily small exact graph error. -/
theorem exists_normalized_schwartz_graph_approximation {N M q : ℕ}
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L})
    (ψ : DirichletBallFormDomain N M q m L) (hψ : ‖ψ.val.val‖ = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q),
      IsCompact (tsupport f) ∧
      tsupport f ⊆ {X | (∀ i : Fin N, particlePosition X.fst i ∈
        Metric.ball (0 : Position) L.val) ∧
        (∀ k : Fin M, particlePosition X.snd k ∈ Metric.ball (0 : Position) L.val)} ∧
      quantum_antisymmetric (f.toLp 2 volume) ∧
      nuclear_symmetric (f.toLp 2 volume) ∧
      ‖f.toLp 2 (volume : Measure (QuantumConfiguration N M))‖ = 1 ∧
      quantumGraphError m ψ.val.val (f.toLp 2 volume) < ENNReal.ofReal ε := by
  let C : ℝ≥0∞ := 16 * (1 + quantumElectronKineticEnergy ψ.val.val +
    (nuclearKineticCoefficient m : ℝ≥0∞) * quantumNuclearKineticEnergy ψ.val.val)
  have hCtop : C ≠ ⊤ := by
    dsimp only [C]
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ψ.val.property.2.2.1.ne⟩,
        ENNReal.mul_ne_top ENNReal.coe_ne_top ψ.val.property.2.2.2.ne⟩)
  have hC0 : C ≠ 0 := by
    dsimp only [C]
    positivity
  let δ : ℝ := min (1 / 8) (ε / (C.toReal + 1))
  have hden : 0 < C.toReal + 1 := by positivity
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε hden)
  have hδsmall : δ ≤ 1 / 8 := min_le_left _ _
  have hδε : (C.toReal + 1) * δ ≤ ε := by
    have := min_le_right (1 / 8) (ε / (C.toReal + 1))
    simpa only [δ, mul_comm] using (le_div_iff₀ hden).mp this
  obtain ⟨f, hfcompact, hfsupport, hfa, hfn, hferr⟩ := ψ.property δ hδ
  let φ : QuantumState N M q := f.toLp 2 volume
  have hnormsq : ‖ψ.val.val - φ‖ ^ 2 < δ := by
    apply (ENNReal.ofReal_lt_ofReal_iff hδ).mp
    exact (show ENNReal.ofReal (‖ψ.val.val - φ‖ ^ 2) ≤ quantumGraphError m ψ.val.val φ by
      dsimp only [quantumGraphError]
      exact le_add_right (le_add_right le_rfl)).trans_lt hferr
  have hdist : ‖ψ.val.val - φ‖ < 1 / 2 := by
    nlinarith only [hnormsq, hδsmall, norm_nonneg (ψ.val.val - φ)]
  have hφ : φ ≠ 0 := by
    intro hz
    rw [hz, sub_zero, hψ] at hdist
    norm_num at hdist
  let c : ℝ := ‖φ‖⁻¹
  let g : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q) := c • f
  have hgsub : tsupport g ⊆ tsupport f :=
    tsupport_smul_subset_right (fun _ => c) (fun X => f X)
  have hgc : IsCompact (tsupport g) :=
    hfcompact.of_isClosed_subset (isClosed_tsupport (fun X => g X)) hgsub
  have hga : quantum_antisymmetric (g.toLp 2 volume) := by
    change quantum_antisymmetric (((c : ℂ) • φ))
    exact quantum_antisymmetric_smul (c : ℂ) hfa
  have hgn : nuclear_symmetric (g.toLp 2 volume) := by
    change nuclear_symmetric (((c : ℂ) • φ))
    exact nuclear_symmetric_smul (c : ℂ) hfn
  have hfne : f ≠ 0 := by
    intro hf
    apply hφ
    have hh := congrArg (SchwartzMap.toLpCLM ℝ (SpinAmplitudes N q) 2
      (volume : Measure (QuantumConfiguration N M))) hf
    rw [map_zero] at hh
    exact hh
  have hgnorm : ‖g.toLp 2 (volume : Measure (QuantumConfiguration N M))‖ = 1 :=
    quantum_norm_schwartz_toLp_normalize f hfne
  have hCle : C ≤ ENNReal.ofReal (C.toReal + 1) := by
    calc
      C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hCtop).symm
      _ ≤ ENNReal.ofReal (C.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  have hfinal : quantumGraphError m ψ.val.val (g.toLp 2 volume) < ENNReal.ofReal ε := by
    have hgLp : g.toLp 2 (volume : Measure (QuantumConfiguration N M)) = (c : ℂ) • φ := by
      dsimp only [g, φ]
      change (SchwartzMap.toLpCLM ℝ (SpinAmplitudes N q) 2
        (volume : Measure (QuantumConfiguration N M))) (c • f) =
          (c : ℂ) • (SchwartzMap.toLpCLM ℝ (SpinAmplitudes N q) 2
            (volume : Measure (QuantumConfiguration N M))) f
      rw [map_smul]
      exact RCLike.real_smul_eq_coe_smul (K := ℂ) c _
    calc
      _ ≤ C * quantumGraphError m ψ.val.val φ := by
        rw [hgLp]
        simpa only [C, c] using
          quantumGraphError_normalize_le m ψ.val.val φ hψ hφ hdist
      _ < C * ENNReal.ofReal δ := by
        rw [mul_comm C, mul_comm C]
        exact ENNReal.mul_lt_mul_left hC0 hCtop hferr
      _ ≤ ENNReal.ofReal (C.toReal + 1) * ENNReal.ofReal δ :=
        by simpa only [mul_comm] using (mul_le_mul_right hCle) (ENNReal.ofReal δ)
      _ = ENNReal.ofReal ((C.toReal + 1) * δ) := by
        rw [ENNReal.ofReal_mul hden.le]
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hδε
  exact ⟨g, hgc, hgsub.trans hfsupport, hga, hgn, hgnorm, hfinal⟩

end LiebThirring

end
