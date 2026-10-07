/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.SmoothInfimum
public import LiebThirring.ThermoForm.Approximation
public import LiebThirring.ThermoForm.FormContinuity

/-! # Energy approximation by smooth confined trials

Argument thermodynamic confined form estimates. The order-theoretic step below turns convergence of real
energies along normalized smooth confined trials into the reverse variational inequality.
-/

public section

open Filter
open scoped ENNReal NNReal Topology

namespace LiebThirring

/-- A normalized smooth approximation chosen at graph-error scale `(n + 1)⁻¹`. -/
@[expose] noncomputable def smoothConfinedApproximation {N M q : ℕ}
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L})
    (ψ : DirichletBallFormDomain N M q m L) (hψ : ‖ψ.val.val‖ = 1)
    (n : ℕ) : SmoothConfinedTrial N M q L := by
  let h := exists_normalized_schwartz_graph_approximation m L ψ hψ
    ((n + 1 : ℝ)⁻¹) (by positivity)
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2.1,
    h.choose_spec.2.2.2.1, h.choose_spec.2.2.2.2.1⟩

theorem quantumGraphError_smoothConfinedApproximation_lt {N M q : ℕ}
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L})
    (ψ : DirichletBallFormDomain N M q m L) (hψ : ‖ψ.val.val‖ = 1)
    (n : ℕ) :
    quantumGraphError m ψ.val.val (smoothConfinedApproximation m L ψ hψ n).formDomain.val <
      ENNReal.ofReal ((n + 1 : ℝ)⁻¹) := by
  let h := exists_normalized_schwartz_graph_approximation m L ψ hψ
    ((n + 1 : ℝ)⁻¹) (by positivity)
  exact h.choose_spec.2.2.2.2.2

theorem tendsto_quantumGraphError_smoothConfinedApproximation {N M q : ℕ}
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L})
    (ψ : DirichletBallFormDomain N M q m L) (hψ : ‖ψ.val.val‖ = 1) :
    Tendsto (fun n => quantumGraphError m ψ.val.val
      (smoothConfinedApproximation m L ψ hψ n).formDomain.val) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => ENNReal.ofReal ((n + 1 : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using ENNReal.tendsto_ofReal
      (tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv
  · exact fun _ => bot_le
  · exact fun n => (quantumGraphError_smoothConfinedApproximation_lt m L ψ hψ n).le

/-- The chosen normalized smooth approximants converge in each component needed by energy
continuity. The subtraction is oriented as `approximant - state`. -/
theorem tendsto_smoothConfinedApproximation_difference {N M q : ℕ}
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L})
    (ψ : DirichletBallFormDomain N M q m L) (hψ : ‖ψ.val.val‖ = 1) :
    Tendsto (fun n => ‖((smoothConfinedApproximation m L ψ hψ n).formDomain - ψ.val).val‖)
        atTop (𝓝 0) ∧
      Tendsto (fun n => (quantumElectronKineticEnergy
        ((smoothConfinedApproximation m L ψ hψ n).formDomain - ψ.val).val).toReal)
        atTop (𝓝 0) ∧
      Tendsto (fun n => (quantumNuclearKineticEnergy
        ((smoothConfinedApproximation m L ψ hψ n).formDomain - ψ.val).val).toReal)
        atTop (𝓝 0) := by
  let v : ℕ → QuantumFormDomain N M q := fun n =>
    (smoothConfinedApproximation m L ψ hψ n).formDomain
  have hg : Tendsto (fun n => quantumGraphError m ψ.val.val (v n).val) atTop (𝓝 0) :=
    tendsto_quantumGraphError_smoothConfinedApproximation m L ψ hψ
  have hnormSq : Tendsto (fun n => ENNReal.ofReal (‖ψ.val.val - (v n).val‖ ^ 2))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg
    · exact fun _ => bot_le
    · intro n
      exact (le_add_right le_rfl).trans (le_add_right le_rfl)
  have hnormSqReal : Tendsto (fun n => ‖ψ.val.val - (v n).val‖ ^ 2) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hnormSq
    have heq : (fun n => (ENNReal.ofReal (‖ψ.val.val - (v n).val‖ ^ 2)).toReal) =
        (fun n => ‖ψ.val.val - (v n).val‖ ^ 2) :=
      funext (fun n => ENNReal.toReal_ofReal (sq_nonneg ‖ψ.val.val - (v n).val‖))
    simp only [Function.comp_def] at h
    rw [heq, ENNReal.toReal_zero] at h
    exact h
  have hnorm : Tendsto (fun n => ‖(v n).val - ψ.val.val‖) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hnormSqReal
    have heq : (fun n => √(‖ψ.val.val - (v n).val‖ ^ 2)) =
        (fun n => ‖(v n).val - ψ.val.val‖) := by
      funext n
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), norm_sub_rev]
    simp only [Function.comp_def] at h
    rw [heq, Real.sqrt_zero] at h
    exact h
  have heENN : Tendsto (fun n => quantumElectronKineticEnergy (ψ.val.val - (v n).val))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg
    · exact fun _ => bot_le
    · intro n
      exact (le_add_left le_rfl).trans (le_add_right le_rfl)
  have he : Tendsto (fun n =>
      (quantumElectronKineticEnergy ((v n).val - ψ.val.val)).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp heENN
    simp only [Function.comp_def] at h
    have hsymm (n : ℕ) : quantumElectronKineticEnergy ((v n).val - ψ.val.val) =
        quantumElectronKineticEnergy (ψ.val.val - (v n).val) := by
      rw [show (v n).val - ψ.val.val = (-1 : ℂ) • (ψ.val.val - (v n).val) by module,
        quantumElectronKineticEnergy_smul]
      norm_num
    simpa only [hsymm, ENNReal.toReal_zero] using h
  let a : ℝ≥0∞ := nuclearKineticCoefficient m
  have ha0 : a ≠ 0 := by
    rw [ENNReal.coe_ne_zero]
    exact inv_ne_zero (ne_of_gt m.property)
  have hat : a ≠ ⊤ := ENNReal.coe_ne_top
  have hnWeighted : Tendsto (fun n =>
      a * quantumNuclearKineticEnergy (ψ.val.val - (v n).val)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg
    · exact fun _ => bot_le
    · intro n
      exact le_add_left le_rfl
  have hnENN : Tendsto (fun n =>
      quantumNuclearKineticEnergy (ψ.val.val - (v n).val)) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hnWeighted (Or.inr (ENNReal.inv_ne_top.mpr ha0))
    simpa only [← mul_assoc, ENNReal.inv_mul_cancel ha0 hat, one_mul, mul_zero] using h
  have hn : Tendsto (fun n =>
      (quantumNuclearKineticEnergy ((v n).val - ψ.val.val)).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hnENN
    simp only [Function.comp_def] at h
    have hsymm (n : ℕ) : quantumNuclearKineticEnergy ((v n).val - ψ.val.val) =
        quantumNuclearKineticEnergy (ψ.val.val - (v n).val) := by
      rw [show (v n).val - ψ.val.val = (-1 : ℂ) • (ψ.val.val - (v n).val) by module,
        quantumNuclearKineticEnergy_smul]
      norm_num
    simpa only [hsymm, ENNReal.toReal_zero] using h
  exact ⟨hnorm, he, hn⟩

/-- A sequence of smooth confined trials whose energies converge to a form-domain energy
bounds the smooth infimum by that limiting energy. -/
theorem smoothConfinedGroundStateEnergy_le_of_tendsto {N M q z : ℕ}
    {m : {m : ℝ≥0 // 0 < m}} {L : {L : ℝ // 0 < L}}
    (ψ : DirichletBallFormDomain N M q m L)
    (f : ℕ → SmoothConfinedTrial N M q L)
    (h : Tendsto (fun n => quantumEnergy z m (f n).formDomain) atTop
      (𝓝 (quantumEnergy z m ψ.val))) :
    smoothConfinedGroundStateEnergy N M q z m L ≤ (quantumEnergy z m ψ.val : EReal) := by
  apply ge_of_tendsto' (EReal.tendsto_coe.mpr h)
  intro n
  exact iInf_le (fun g : SmoothConfinedTrial N M q L =>
    (quantumEnergy z m g.formDomain : EReal)) (f n)

/-- The energies of the chosen normalized smooth approximants converge to the original
Dirichlet form energy. -/
theorem tendsto_quantumEnergy_smoothConfinedApproximation {N M q z : ℕ}
    (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L})
    (ψ : DirichletBallFormDomain N M q m L) (hψ : ‖ψ.val.val‖ = 1) :
    Tendsto (fun n => quantumEnergy z m
      (smoothConfinedApproximation m L ψ hψ n).formDomain) atTop
      (𝓝 (quantumEnergy z m ψ.val)) := by
  obtain ⟨h0, he, hn⟩ := tendsto_smoothConfinedApproximation_difference m L ψ hψ
  exact tendsto_quantumEnergy_of_difference z m ψ.val
    (fun n => (smoothConfinedApproximation m L ψ hψ n).formDomain) h0 he hn

/-- Smooth normalized confined trials give no larger infimum than the full Dirichlet
form carrier. -/
theorem smoothConfinedGroundStateEnergy_le_confinedGroundStateEnergy
    (N M q z : ℕ) (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) :
    smoothConfinedGroundStateEnergy N M q z m L ≤
      confinedGroundStateEnergy N M q z m L := by
  unfold confinedGroundStateEnergy
  apply le_iInf
  intro ψ
  exact smoothConfinedGroundStateEnergy_le_of_tendsto ψ.val
    (smoothConfinedApproximation m L ψ.val ψ.property)
    (tendsto_quantumEnergy_smoothConfinedApproximation m L ψ.val ψ.property)

/-- Argument thermodynamic confined form estimates: the confined variational energy is unchanged when the
infimum is restricted to normalized compactly supported smooth states with the prescribed
statistics. -/
theorem confinedGroundStateEnergy_eq_smoothConfinedGroundStateEnergy
    (N M q z : ℕ) (m : {m : ℝ≥0 // 0 < m}) (L : {L : ℝ // 0 < L}) :
    confinedGroundStateEnergy N M q z m L =
      smoothConfinedGroundStateEnergy N M q z m L :=
  le_antisymm
    (confinedGroundStateEnergy_le_smoothConfinedGroundStateEnergy N M q z m L)
    (smoothConfinedGroundStateEnergy_le_confinedGroundStateEnergy N M q z m L)

end LiebThirring

end
