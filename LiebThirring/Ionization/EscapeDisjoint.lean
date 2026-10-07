/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.TrialBasic
import LiebThirring.Kinetic.DensityBasic

/-!
# Separated trial summands

Spatially separated summands have exactly additive squared mass,
potential expectations and Dirichlet energy. Closed supports also separate
their derivatives, so no exchange or derivative cross term is discarded.
-/

public section

open MeasureTheory Set Function
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- At a point, disjoint supports leave at most one nonzero summand. -/
theorem escape_nnnorm_sum_sq {ι X H : Type*} [Fintype ι]
    [NormedAddCommGroup H] (f : ι → X → H)
    (hf : Pairwise (Disjoint on fun i => support (f i))) (x : X) :
    (‖∑ i, f i x‖₊ : ℝ≥0∞) ^ 2 = ∑ i, (‖f i x‖₊ : ℝ≥0∞) ^ 2 := by
  classical
  by_cases hx : ∃ i, f i x ≠ 0
  · obtain ⟨i, hi⟩ := hx
    have hz (j : ι) (hji : j ≠ i) : f j x = 0 := by
      by_contra hj
      exact Set.disjoint_left.mp (hf hji) hj hi
    rw [Finset.sum_eq_single i (fun j _ hji => hz j hji)
      (fun h => (h (Finset.mem_univ i)).elim)]
    rw [Finset.sum_eq_single i]
    · intro j _ hji
      rw [hz j hji, nnnorm_zero, ENNReal.coe_zero, zero_pow (by decide : 2 ≠ 0)]
    · intro h
      exact (h (Finset.mem_univ i)).elim
  · have hz (i : ι) : f i x = 0 := not_not.mp (not_exists.mp hx i)
    simp only [hz, Finset.sum_const_zero, nnnorm_zero, ENNReal.coe_zero,
      zero_pow (by decide : 2 ≠ 0)]

/-- Nonnegative weighted expectations are additive on disjoint measurable summands. -/
theorem escape_lintegral_weight_sum {ι X H : Type*} [Fintype ι]
    [MeasurableSpace X] [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
    {μ : Measure X} (p : X → ℝ≥0∞) (hp : Measurable p) (f : ι → X → H)
    (hm : ∀ i, Measurable (f i))
    (hf : Pairwise (Disjoint on fun i => support (f i))) :
    (∫⁻ x, p x * (‖∑ i, f i x‖₊ : ℝ≥0∞) ^ 2 ∂μ) =
      ∑ i, ∫⁻ x, p x * (‖f i x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  simp_rw [escape_nnnorm_sum_sq f hf, Finset.mul_sum]
  exact lintegral_finsetSum _ (fun i _ => hp.mul (((hm i).nnnorm.coe_nnreal_ennreal).pow_const 2))

/-- Closed support separation passes to every directional derivative. -/
theorem escape_disjoint_fderiv {ι E H : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : ι → E → H) (hf : Pairwise (Disjoint on fun i => tsupport (f i))) (v : E) :
    Pairwise (Disjoint on fun i => support (fun x => fderiv ℝ (f i) x v)) := by
  intro i j hij
  apply (hf hij).mono
  · exact (subset_closure.trans (tsupport_fderiv_apply_subset ℝ v))
  · exact (subset_closure.trans (tsupport_fderiv_apply_subset ℝ v))

/-- A Schwartz sum has additive weighted mass when its spatial supports separate. -/
theorem escape_schwartz_lintegral_weight_sum {ι N q : ℕ}
    (p : Configuration N → ℝ≥0∞) (hp : Measurable p)
    (f : Fin ι → 𝓢(Configuration N, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun x => f i x))) :
    (∫⁻ x, p x * (‖(∑ i, f i) x‖₊ : ℝ≥0∞) ^ 2) =
      ∑ i, ∫⁻ x, p x * (‖f i x‖₊ : ℝ≥0∞) ^ 2 := by
  simp only [sum_apply]
  apply escape_lintegral_weight_sum p hp (fun i x => f i x)
    (fun i => (f i).continuous.measurable)
  intro i j hij
  exact (hf hij).mono subset_closure subset_closure

/-- The Fourier kinetic form is exactly additive on separated Schwartz summands. -/
theorem escape_kineticEnergy_sum {ι N q : ℕ}
    (f : Fin ι → 𝓢(Configuration N, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun x => f i x))) :
    kineticEnergy ((∑ i, f i).toLp 2 (volume : Measure (Configuration N))) =
      ∑ i, kineticEnergy ((f i).toLp 2 (volume : Measure (Configuration N))) := by
  classical
  simp only [kineticEnergy_schwartz]
  have hd (v : Configuration N) :
      (∫⁻ x, (‖fderiv ℝ (fun y => (∑ i, f i) y) x v‖₊ : ℝ≥0∞) ^ 2) =
        ∑ i, ∫⁻ x, (‖fderiv ℝ (fun y => f i y) x v‖₊ : ℝ≥0∞) ^ 2 := by
    simp only [sum_apply]
    simp_rw [fderiv_fun_sum (fun i _ => (f i).differentiable.differentiableAt),
      sum_apply]
    simpa only [one_mul] using escape_lintegral_weight_sum (fun _ => 1)
      measurable_const (fun i x => fderiv ℝ (fun y => f i y) x v)
      (fun i => (((f i).smooth ⊤).continuous_fderiv (by simp)).clm_apply
        continuous_const |>.measurable)
      (escape_disjoint_fderiv (fun i x => f i x) hf v)
  simp_rw [hd]
  calc
    _ = ∑ j : Fin N, ∑ i : Fin ι, ∑ a : Fin 3, ∫⁻ x : Configuration N,
        (‖fderiv ℝ (fun y => f i y) x (PiLp.single 2 (j, a) (1 : ℝ))‖₊ : ℝ≥0∞) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Squared L² mass, before division by the square root of the number of terms. -/
theorem escape_norm_toLp_sum_sq {ι N q : ℕ}
    (f : Fin ι → 𝓢(Configuration N, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun x => f i x))) :
    ‖(∑ i, f i).toLp 2 (volume : Measure (Configuration N))‖ ^ 2 =
      ∑ i, ‖(f i).toLp 2 (volume : Measure (Configuration N))‖ ^ 2 := by
  have hm (g : 𝓢(Configuration N, SpinAmplitudes N q)) :
      (∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2) =
        (‖g.toLp 2 (volume : Measure (Configuration N))‖₊ : ℝ≥0∞) ^ 2 := by
    rw [← lintegral_state_norm_sq]
    apply lintegral_congr_ae
    filter_upwards [g.coeFn_toLp 2 (volume : Measure (Configuration N))] with x hx
    rw [hx]
  have he := escape_schwartz_lintegral_weight_sum (fun _ => 1) measurable_const f hf
  simp only [one_mul, hm] at he
  have h := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.pow_ne_top ENNReal.coe_ne_top)] at h
  simpa only [ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm] using h

/-- The prescribed `1 / sqrt(n)` coefficient normalizes `n` unit separated terms. -/
theorem escape_norm_toLp_normalized_sum {ι N q : ℕ} (hι : 0 < ι)
    (f : Fin ι → 𝓢(Configuration N, SpinAmplitudes N q))
    (hf : Pairwise (Disjoint on fun i => tsupport (fun x => f i x)))
    (hn : ∀ i, ‖(f i).toLp 2 (volume : Measure (Configuration N))‖ = 1) :
    ‖((Real.sqrt ι)⁻¹ • ∑ i, f i).toLp 2 (volume : Measure (Configuration N))‖ = 1 := by
  have hmass := escape_norm_toLp_sum_sq f hf
  simp only [hn, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hmass
  have hnorm : ‖(∑ i, f i).toLp 2 (volume : Measure (Configuration N))‖ = Real.sqrt ι := by
    rw [← hmass, Real.sqrt_sq (norm_nonneg _)]
  change ‖SchwartzMap.toLpCLM ℝ (SpinAmplitudes N q) 2
    (volume : Measure (Configuration N)) ((Real.sqrt ι)⁻¹ • ∑ i, f i)‖ = 1
  rw [map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  change (Real.sqrt ι)⁻¹ * ‖(∑ i, f i).toLp 2 (volume : Measure (Configuration N))‖ = 1
  rw [hnorm]
  exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hι))

end LiebThirring

end
