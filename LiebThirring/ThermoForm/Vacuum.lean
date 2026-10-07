/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.Basic
public import LiebThirring.Thermodynamic.ConfinedGroundStateEnergy

/-! # The normalized confined vacuum

The zero-particle configuration has one point and the empty spin label exists
even when `q = 0`. Thus the vacuum statement requires no spin assumption.
This implements the vacuum part of the thermodynamic confined form estimates.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

theorem quantum_antisymmetric_no_electrons {M q : ℕ} (ψ : QuantumState 0 M q) :
    quantum_antisymmetric ψ := by
  intro σ
  have hσ : σ = Equiv.refl (Fin 0) := Subsingleton.elim _ _
  subst σ
  apply Filter.Eventually.of_forall
  intro X s
  have hX : toLp 2 (permutePositions (Equiv.refl (Fin 0)) X.fst, X.snd) = X := by
    apply (WithLp.equiv 2 _).injective
    exact Prod.ext (Subsingleton.elim _ _) rfl
  have hs : permuteSpins (Equiv.refl (Fin 0)) s = s := Subsingleton.elim _ _
  rw [hX, hs]
  simp only [Equiv.Perm.sign_refl, Units.val_one, Int.cast_one, one_mul]

theorem nuclear_symmetric_no_nuclei {N q : ℕ} (ψ : QuantumState N 0 q) :
    nuclear_symmetric ψ := by
  intro τ
  apply Filter.Eventually.of_forall
  intro X s
  have hX : toLp 2 (X.fst, permutePositions τ X.snd) = X := by
    apply (WithLp.equiv 2 _).injective
    exact Prod.ext rfl (Subsingleton.elim _ _)
  rw [hX]

/-- A nonzero smooth joint function has a nonzero L² class. -/
theorem quantum_schwartz_toLp_ne_zero {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) (hf : f ≠ 0) :
    f.toLp 2 (volume : Measure (QuantumConfiguration N M)) ≠ 0 := by
  intro h
  apply hf
  apply DFunLike.ext
  have heq : (fun x => f x) =ᵐ[volume] fun _ => (0 : SpinAmplitudes N q) := by
    filter_upwards [f.coeFn_toLp 2 (volume : Measure (QuantumConfiguration N M)),
      Lp.coeFn_zero (SpinAmplitudes N q) 2
        (volume : Measure (QuantumConfiguration N M))] with x hx hz
    rw [h] at hx
    exact hx.symm.trans hz
  intro x
  exact congrFun (Measure.eq_of_ae_eq heq f.continuous continuous_const) x

theorem quantum_norm_schwartz_toLp_normalize {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) (hf : f ≠ 0) :
    ‖((‖f.toLp 2 (volume : Measure (QuantumConfiguration N M))‖⁻¹ • f).toLp 2
      (volume : Measure (QuantumConfiguration N M)))‖ = 1 := by
  have hn : ‖f.toLp 2 (volume : Measure (QuantumConfiguration N M))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (quantum_schwartz_toLp_ne_zero f hf)
  change ‖(SchwartzMap.toLpCLM ℝ (SpinAmplitudes N q) 2
    (volume : Measure (QuantumConfiguration N M)))
      (‖f.toLp 2 (volume : Measure (QuantumConfiguration N M))‖⁻¹ • f)‖ = 1
  rw [map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ hn

theorem exists_normalized_dirichlet_vacuum (q : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) :
    ∃ ψ : DirichletBallFormDomain 0 0 q m L, ‖ψ.val.val‖ = 1 := by
  classical
  let : Subsingleton (QuantumConfiguration 0 0) :=
    (WithLp.equiv 2 (Configuration 0 × Configuration 0)).injective.subsingleton
  let v : SpinAmplitudes 0 q := toLp 2 (fun _ => (1 : ℂ))
  let f : 𝓢(QuantumConfiguration 0 0, SpinAmplitudes 0 q) :=
    (HasCompactSupport.of_compactSpace (fun _ : QuantumConfiguration 0 0 => v)).toSchwartzMap
      contDiff_const
  have hf : f ≠ 0 := by
    intro h
    have hv := congrArg (fun g : 𝓢(QuantumConfiguration 0 0, SpinAmplitudes 0 q) =>
      g 0 (fun i => Fin.elim0 i)) h
    exact one_ne_zero hv
  let g := ‖f.toLp 2 (volume : Measure (QuantumConfiguration 0 0))‖⁻¹ • f
  let φ : QuantumFormDomain 0 0 q :=
    ⟨g.toLp 2 (volume : Measure (QuantumConfiguration 0 0)),
      quantum_antisymmetric_no_electrons _, nuclear_symmetric_no_nuclei _,
      by rw [quantumElectronKineticEnergy_vacuum]; exact ENNReal.zero_lt_top,
      by rw [quantumNuclearKineticEnergy_vacuum]; exact ENNReal.zero_lt_top⟩
  have hd : is_dirichlet_ball m L φ.val := by
    intro ε hε
    refine ⟨g, (HasCompactSupport.of_compactSpace (fun X => g X)), ?_, φ.property.1, φ.property.2.1, ?_⟩
    · intro X _
      exact ⟨fun i => Fin.elim0 i, fun k => Fin.elim0 k⟩
    · change ENNReal.ofReal (‖φ.val - φ.val‖ ^ 2) +
        quantumElectronKineticEnergy (φ.val - φ.val) +
        (nuclearKineticCoefficient m : ℝ≥0∞) *
          quantumNuclearKineticEnergy (φ.val - φ.val) < ENNReal.ofReal ε
      rw [sub_self, quantumElectronKineticEnergy_zero, quantumNuclearKineticEnergy_zero]
      simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero,
        add_zero, mul_zero] using ENNReal.ofReal_pos.mpr hε
  exact ⟨⟨φ, hd⟩, quantum_norm_schwartz_toLp_normalize f hf⟩

theorem confinedGroundStateEnergy_vacuum_eq (q z : ℕ)
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) :
    confinedGroundStateEnergy 0 0 q z m L = 0 := by
  obtain ⟨ψ, hψ⟩ := exists_normalized_dirichlet_vacuum q m L
  let : Nonempty {ψ : DirichletBallFormDomain 0 0 q m L // ‖ψ.val.val‖ = 1} :=
    ⟨⟨ψ, hψ⟩⟩
  simp only [confinedGroundStateEnergy, quantumEnergy_vacuum, EReal.coe_zero, ciInf_const]

end LiebThirring

end
