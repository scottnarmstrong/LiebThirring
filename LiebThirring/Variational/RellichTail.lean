/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Kinetic.CurryingProductBasic
public import LiebThirring.Sobolev.WeakEnergy

/-! # Fourier tails for local Rellich compactness

Frequency truncation of many-particle states and the uniform high-frequency estimate supplied by
the physical kinetic energy.
-/

public section

open Filter MeasureTheory
open scoped ENNReal NNReal FourierTransform Topology

namespace LiebThirring

/-- The raw Fourier representative of a state, restricted to a measurable set. -/
@[expose] noncomputable def fourierCutoffRaw {N q : ℕ} (s : Set (Configuration N))
    (u : State N q) : Configuration N → SpinAmplitudes N q :=
  s.indicator fun ξ => (𝓕 u : State N q) ξ

/-- A measurable Fourier cutoff belongs to `L²`. -/
theorem fourierCutoffRaw_memLp {N q : ℕ} (s : Set (Configuration N))
    (hs : MeasurableSet s) (u : State N q) : MemLp (fourierCutoffRaw s u) 2 volume := by
  exact (Lp.memLp (𝓕 u : State N q)).indicator hs

/-- The Fourier-side state obtained by restricting to a measurable set. -/
@[expose] noncomputable def fourierCutoff {N q : ℕ} (s : Set (Configuration N))
    (hs : MeasurableSet s) (u : State N q) : State N q :=
  (fourierCutoffRaw_memLp s hs u).toLp (fourierCutoffRaw s u)

/-- The `L²` Fourier cutoff has the expected representative almost everywhere. -/
theorem fourierCutoff_coeFn {N q : ℕ} (s : Set (Configuration N))
    (hs : MeasurableSet s) (u : State N q) :
    ⇑(fourierCutoff s hs u) =ᵐ[volume] fourierCutoffRaw s u := by
  exact MemLp.coeFn_toLp (fourierCutoffRaw_memLp s hs u)

/-- The inverse Fourier transform of the cutoff to the closed frequency ball. -/
@[expose] noncomputable def lowFrequencyState {N q : ℕ} (R : ℝ) (u : State N q) : State N q :=
  𝓕⁻ (fourierCutoff (Metric.closedBall 0 R) measurableSet_closedBall u)

/-- Fourier transforming a low-frequency state recovers its cutoff. -/
theorem fourier_lowFrequencyState {N q : ℕ} (R : ℝ) (u : State N q) :
    𝓕 (lowFrequencyState R u) =
      fourierCutoff (Metric.closedBall 0 R) measurableSet_closedBall u := by
  exact FourierTransform.fourier_fourierInv_eq _

/-- The Fourier transform of the truncation error is the raw high-frequency tail. -/
theorem fourier_sub_lowFrequencyState_coeFn {N q : ℕ} (R : ℝ) (u : State N q) :
    ⇑(𝓕 (u - lowFrequencyState R u) : State N q) =ᵐ[volume]
      (Metric.closedBall (0 : Configuration N) R)ᶜ.indicator
        (fun ξ => (𝓕 u : State N q) ξ) := by
  have hfourier : 𝓕 (u - lowFrequencyState R u) =
      (𝓕 u : State N q) - 𝓕 (lowFrequencyState R u) :=
    (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)).map_sub _ _
  rw [hfourier, fourier_lowFrequencyState]
  filter_upwards [Lp.coeFn_sub (𝓕 u : State N q)
      (fourierCutoff (Metric.closedBall 0 R) measurableSet_closedBall u),
    fourierCutoff_coeFn (Metric.closedBall 0 R) measurableSet_closedBall u] with ξ hsub hcut
  rw [hsub, Pi.sub_apply, hcut]
  by_cases hξ : ξ ∈ Metric.closedBall (0 : Configuration N) R
  · have hξc : ξ ∉ (Metric.closedBall (0 : Configuration N) R)ᶜ := fun hc => hc hξ
    simp only [fourierCutoffRaw, Set.indicator_of_mem hξ,
      Set.indicator_of_notMem hξc, sub_self]
  · simp only [fourierCutoffRaw, Set.indicator_of_notMem hξ,
      Set.indicator_of_mem (Set.mem_compl hξ), sub_zero]

/-- The physical kinetic form controls the squared `L²` mass above frequency `R`. -/
theorem lowFrequencyState_tail_enorm_sq {N q : ℕ} (R : ℝ) (hR : 0 ≤ R)
    (u : State N q) :
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * ENNReal.ofReal (R ^ 2) *
        ‖u - lowFrequencyState R u‖ₑ ^ 2 ≤ kineticEnergy u := by
  let v : State N q := 𝓕 (u - lowFrequencyState R u)
  have hv : ⇑v =ᵐ[volume] (Metric.closedBall (0 : Configuration N) R)ᶜ.indicator
      (fun ξ => (𝓕 u : State N q) ξ) :=
    fourier_sub_lowFrequencyState_coeFn R u
  have hmass : ‖u - lowFrequencyState R u‖ₑ ^ 2 =
      ∫⁻ ξ, ‖(Metric.closedBall (0 : Configuration N) R)ᶜ.indicator
        (fun η => (𝓕 u : State N q) η) ξ‖ₑ ^ 2 := by
    rw [← LinearIsometryEquiv.enorm_map
      (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q))]
    change ‖v‖ₑ ^ 2 = _
    rw [← lintegral_l2_enorm_sq v]
    exact lintegral_congr_ae (hv.fun_comp fun z => ‖z‖ₑ ^ 2)
  rw [hmass]
  rw [← lintegral_const_mul' _ _
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  change (∫⁻ ξ, _ * _ * ‖(Metric.closedBall (0 : Configuration N) R)ᶜ.indicator
    (fun η => (𝓕 u : State N q) η) ξ‖ₑ ^ 2) ≤ kineticEnergy u
  apply lintegral_mono
  intro ξ
  change ENNReal.ofReal ((2 * Real.pi) ^ 2) * ENNReal.ofReal (R ^ 2) *
      ‖(Metric.closedBall (0 : Configuration N) R)ᶜ.indicator
        (fun η => (𝓕 u : State N q) η) ξ‖ₑ ^ 2 ≤
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
      (‖(𝓕 u : State N q) ξ‖₊ : ℝ≥0∞) ^ 2
  by_cases hξ : ξ ∈ Metric.closedBall (0 : Configuration N) R
  · have hξc : ξ ∉ (Metric.closedBall (0 : Configuration N) R)ᶜ := fun hc => hc hξ
    rw [Set.indicator_of_notMem hξc, enorm_zero,
      zero_pow (show (2 : ℕ) ≠ 0 by norm_num), mul_zero]
    exact bot_le
  · rw [Set.indicator_of_mem (Set.mem_compl hξ), enorm_eq_nnnorm]
    gcongr
    rw [ENNReal.ofReal_pow hR]
    change ENNReal.ofReal R ^ 2 ≤ ‖ξ‖ₑ ^ 2
    rw [← ofReal_norm]
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal
      (le_of_not_ge (fun h => hξ (by simpa [Metric.mem_closedBall] using h)))) 2

/-- The exact real-valued Fourier-tail estimate, with the physical `(2π)²` convention. -/
theorem norm_sub_lowFrequencyState_sq_le {N q : ℕ} (R : ℝ) (hR : 0 < R)
    (u : State N q) (hu : kineticEnergy u < ⊤) :
    ‖u - lowFrequencyState R u‖ ^ 2 ≤
      (kineticEnergy u).toReal / ((2 * Real.pi) ^ 2 * R ^ 2) := by
  have h := ENNReal.toReal_mono hu.ne (lowFrequencyState_tail_enorm_sq R hR.le u)
  have hnorm : (‖u - lowFrequencyState R u‖ₑ ^ 2).toReal =
      ‖u - lowFrequencyState R u‖ ^ 2 := by
    rw [ENNReal.toReal_pow, ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal,
    ENNReal.toReal_ofReal, hnorm] at h
  · exact (le_div_iff₀ (mul_pos (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
      (sq_pos_of_pos hR))).2
      (by simpa only [mul_assoc, mul_comm, mul_left_comm] using h)
  · positivity
  · positivity

/-- A graph-norm bounded state has Fourier tail at most `1 / (2πR)` times its graph norm. -/
theorem norm_sub_lowFrequencyState_le_of_formGraph {N q : ℕ} (R : ℝ) (hR : 0 < R)
    (v : Sobolev.formGraph N q) :
    ‖((v : Sobolev.FormGraphAmbient N q) none) -
        lowFrequencyState R ((v : Sobolev.FormGraphAmbient N q) none)‖ ≤
      ‖v‖ / (2 * Real.pi * R) := by
  let u : State N q := (v : Sobolev.FormGraphAmbient N q) none
  have hu : kineticEnergy u < ⊤ := by
    rw [Sobolev.kineticEnergy_eq_formGraph_derivatives v]
    exact ENNReal.sum_lt_top.mpr fun a _ =>
      ENNReal.pow_lt_top ENNReal.coe_lt_top
  have hk : (kineticEnergy u).toReal ≤ ‖v‖ ^ 2 := by
    rw [Sobolev.formGraph_norm_sq_eq_mass_add_kineticEnergy v]
    exact le_add_of_nonneg_left (sq_nonneg ‖u‖)
  have hsq : ‖u - lowFrequencyState R u‖ ^ 2 ≤ (‖v‖ / (2 * Real.pi * R)) ^ 2 := by
    calc
      _ ≤ (kineticEnergy u).toReal / ((2 * Real.pi) ^ 2 * R ^ 2) :=
        norm_sub_lowFrequencyState_sq_le R hR u hu
      _ ≤ ‖v‖ ^ 2 / ((2 * Real.pi) ^ 2 * R ^ 2) :=
        div_le_div_of_nonneg_right hk (by positivity)
      _ = (‖v‖ / (2 * Real.pi * R)) ^ 2 := by
        rw [div_pow]
        congr 1
        ring
  exact ((sq_le_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg v)
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hR.le))).mp hsq)

end LiebThirring

end
