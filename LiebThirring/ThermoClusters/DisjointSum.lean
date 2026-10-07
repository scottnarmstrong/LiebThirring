/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.SchwartzEnergy
public import LiebThirring.Ionization.EscapeDisjoint
public import LiebThirring.Kinetic.CurryingProductBasic

/-!
# Finite sums of separated joint trials

Pairwise disjoint closed supports eliminate every spatial quadratic cross term.
The same separation holds for directional derivatives, so both Fourier
kinetic energies are additive through their smooth-core derivative identities.
the proof follows the separated-sum
argument already formalized in `Ionization.EscapeDisjoint`.
-/

public section
open MeasureTheory Set Function WithLp
open scoped ENNReal NNReal SchwartzMap
namespace LiebThirring

/-- A separated joint Schwartz sum has additive nonnegative weighted mass. -/
theorem quantumSchwartz_lintegral_weight_sum {ι : Type*} [Fintype ι] {N M q : ℕ}
    (p : QuantumConfiguration N M → ℝ≥0∞) (hp : Measurable p)
    (f : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun X => f i X))) :
    (∫⁻ X, p X * (‖(∑ i, f i) X‖₊ : ℝ≥0∞) ^ 2) =
      ∑ i, ∫⁻ X, p X * (‖f i X‖₊ : ℝ≥0∞) ^ 2 := by
  classical
  simp only [sum_apply]
  apply escape_lintegral_weight_sum p hp (fun i X => f i X)
    (fun i => (f i).continuous.measurable)
  intro i j hij
  exact (hf hij).mono subset_closure subset_closure

/-- Squared directional derivative masses add for separated joint Schwartz waves. -/
theorem quantumSchwartz_lintegral_fderiv_sum {ι : Type*} [Fintype ι] {N M q : ℕ}
    (f : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun X => f i X)))
    (v : QuantumConfiguration N M) :
    (∫⁻ X, (‖fderiv ℝ (fun Y => (∑ i, f i) Y) X v‖₊ : ℝ≥0∞) ^ 2) =
      ∑ i, ∫⁻ X, (‖fderiv ℝ (fun Y => f i Y) X v‖₊ : ℝ≥0∞) ^ 2 := by
  classical
  simp only [sum_apply]
  simp_rw [fderiv_fun_sum (fun i _ => (f i).differentiable.differentiableAt), sum_apply]
  simpa only [one_mul] using escape_lintegral_weight_sum (fun _ => 1)
    measurable_const (fun i X => fderiv ℝ (fun Y => f i Y) X v)
    (fun i => (((f i).smooth ⊤).continuous_fderiv (by simp)).clm_apply
      continuous_const |>.measurable)
    (escape_disjoint_fderiv (fun i X => f i X) hf v)

/-- The actual electron Fourier kinetic energy is additive on separated smooth summands. -/
theorem quantumElectronKineticEnergy_disjoint_schwartz_sum {ι : Type*} [Fintype ι]
    {N M q : ℕ} (f : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun X => f i X))) :
    quantumElectronKineticEnergy ((∑ i, f i).toLp 2 volume) =
      ∑ i, quantumElectronKineticEnergy ((f i).toLp 2 volume) := by
  classical
  simp only [quantumElectronKineticEnergy_schwartz]
  simp_rw [quantumSchwartz_lintegral_fderiv_sum f hf]
  calc
    _ = ∑ j : Fin N, ∑ i : ι, ∑ a : Fin 3, ∫⁻ X : QuantumConfiguration N M,
        (‖fderiv ℝ (fun Y => f i Y) X
          (toLp 2 (PiLp.single 2 (j, a) (1 : ℝ), (0 : Configuration M)))‖₊ : ℝ≥0∞) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The actual nuclear Fourier kinetic energy is additive on separated smooth summands. -/
theorem quantumNuclearKineticEnergy_disjoint_schwartz_sum {ι : Type*} [Fintype ι]
    {N M q : ℕ} (f : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun X => f i X))) :
    quantumNuclearKineticEnergy ((∑ i, f i).toLp 2 volume) =
      ∑ i, quantumNuclearKineticEnergy ((f i).toLp 2 volume) := by
  classical
  simp only [quantumNuclearKineticEnergy_schwartz]
  simp_rw [quantumSchwartz_lintegral_fderiv_sum f hf]
  calc
    _ = ∑ j : Fin M, ∑ i : ι, ∑ a : Fin 3, ∫⁻ X : QuantumConfiguration N M,
        (‖fderiv ℝ (fun Y => f i Y) X
          (toLp 2 ((0 : Configuration N), PiLp.single 2 (j, a) (1 : ℝ)))‖₊ : ℝ≥0∞) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Squared L² mass of a finite separated joint sum is the sum of its squared masses. -/
theorem quantumSchwartz_norm_toLp_sum_sq {ι : Type*} [Fintype ι] {N M q : ℕ}
    (f : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun X => f i X))) :
    ‖(∑ i, f i).toLp 2 (volume : Measure (QuantumConfiguration N M))‖ ^ 2 =
      ∑ i, ‖(f i).toLp 2 (volume : Measure (QuantumConfiguration N M))‖ ^ 2 := by
  classical
  have hm (g : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
      (∫⁻ X, (‖g X‖₊ : ℝ≥0∞) ^ 2) =
        (‖g.toLp 2 (volume : Measure (QuantumConfiguration N M))‖₊ : ℝ≥0∞) ^ 2 := by
    rw [← enorm_eq_nnnorm, ← lintegral_l2_enorm_sq]
    apply lintegral_congr_ae
    filter_upwards [g.coeFn_toLp 2 (volume : Measure (QuantumConfiguration N M))] with X hX
    rw [hX, enorm_eq_nnnorm]
  have he := quantumSchwartz_lintegral_weight_sum (fun _ => 1) measurable_const f hf
  simp only [one_mul, hm] at he
  have h := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.pow_ne_top ENNReal.coe_ne_top)] at h
  simpa only [ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm] using h

/-- Division by the square root of the number of separated unit summands normalizes the sum. -/
theorem quantumSchwartz_norm_toLp_normalized_sum {ι : Type*} [Fintype ι] {N M q : ℕ}
    (hι : 0 < Fintype.card ι)
    (f : ι → 𝓢(QuantumConfiguration N M, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun X => f i X)))
    (hn : ∀ i, ‖(f i).toLp 2 (volume : Measure (QuantumConfiguration N M))‖ = 1) :
    ‖((Real.sqrt (Fintype.card ι))⁻¹ • ∑ i, f i).toLp 2
      (volume : Measure (QuantumConfiguration N M))‖ = 1 := by
  classical
  have hmass := quantumSchwartz_norm_toLp_sum_sq f hf
  simp only [hn, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hmass
  have hnorm : ‖(∑ i, f i).toLp 2 (volume : Measure (QuantumConfiguration N M))‖ =
      Real.sqrt (Fintype.card ι) := by
    rw [← hmass, Real.sqrt_sq (norm_nonneg _)]
  change ‖SchwartzMap.toLpCLM ℝ (SpinAmplitudes N q) 2
    (volume : Measure (QuantumConfiguration N M)) ((Real.sqrt (Fintype.card ι))⁻¹ • ∑ i, f i)‖ = 1
  rw [map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  change (Real.sqrt (Fintype.card ι))⁻¹ *
    ‖(∑ i, f i).toLp 2 (volume : Measure (QuantumConfiguration N M))‖ = 1
  rw [hnorm]
  exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hι))

end LiebThirring
end
