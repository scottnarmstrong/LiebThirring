/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.FormDensityFourier

/-!
# Compact smooth density in the kinetic form norm

A Schwartz approximation in the Fourier graph weight followed by a spatial
cutoff gives a compact smooth approximation on the state carrier.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal SchwartzMap FourierTransform ContDiff Topology

namespace LiebThirring.Sobolev

/-- The radial Fourier graph seminorm of a state. -/
@[expose] noncomputable def fourierGraphSeminorm {N q : ℕ} (u : State N q) : ℝ≥0∞ :=
  eLpNorm (fun ξ => (𝓕 u : State N q) ξ) 2 (radialFourierMeasure N)

private theorem fourier_state_sub {N q : ℕ} (u v : State N q) :
    (𝓕 (u - v) : State N q) = 𝓕 u - 𝓕 v :=
  (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q)).map_sub u v

/-- Fourier representative differences may be tested in any measure absolutely
continuous with respect to volume. -/
theorem eLpNorm_fourier_sub_schwartz {N q : ℕ} (u : State N q)
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    {μ : Measure (Configuration N)} (hμ : μ ≪ volume) :
    eLpNorm (fun ξ => (𝓕 (u - f.toLp 2 volume) : State N q) ξ) 2 μ =
      eLpNorm (fun ξ => (𝓕 u : State N q) ξ - (𝓕 f) ξ) 2 μ := by
  rw [fourier_state_sub, SchwartzMap.toLp_fourier_eq]
  apply eLpNorm_congr_ae
  apply hμ.ae_eq
  filter_upwards [Lp.coeFn_sub (𝓕 u) ((𝓕 f).toLp 2 volume),
    (𝓕 f).coeFn_toLp 2 volume] with ξ hsub hf
  rw [hsub, Pi.sub_apply, hf]

/-- The radial Fourier seminorm satisfies the triangle inequality for differences. -/
theorem fourierGraphSeminorm_sub_le {N q : ℕ} (u v : State N q) :
    fourierGraphSeminorm (u - v) ≤ fourierGraphSeminorm u + fourierGraphSeminorm v := by
  unfold fourierGraphSeminorm radialFourierMeasure
  rw [fourier_state_sub,
    eLpNorm_congr_ae ((withDensity_absolutelyContinuous _ _).ae_eq (Lp.coeFn_sub (𝓕 u) (𝓕 v)))]
  exact eLpNorm_sub_le (by norm_num)

/-- Compact smooth cutoffs of a Schwartz state converge in mass and in its Fourier
graph seminorm. -/
theorem exists_compact_smooth_schwartz_form_sequence {N q : ℕ}
    (η : 𝓢(Configuration N, SpinAmplitudes N q)) :
    ∃ f : ℕ → 𝓢(Configuration N, SpinAmplitudes N q), (∀ n, HasCompactSupport (f n)) ∧
      Tendsto (fun n => ‖(f n).toLp 2 volume - η.toLp 2 volume‖) atTop (𝓝 0) ∧
      Tendsto (fun n => fourierGraphSeminorm
        ((f n).toLp 2 volume - η.toLp 2 volume)) atTop (𝓝 0) := by
  obtain ⟨f, hf, h₀, h₁⟩ := exists_compact_smooth_schwartz_test_approximation η
  let g : ℕ → 𝓢(Configuration N, SpinAmplitudes N q) :=
    fun n => (hf n).1.toSchwartzMap (hf n).2
  have htoLp (n : ℕ) : (g n - η).toLp 2 volume =
      (g n).toLp 2 volume - η.toLp 2 volume := by
    exact (SchwartzMap.toLpCLM ℂ (SpinAmplitudes N q) 2 volume).map_sub (g n) η
  have hconv : Tendsto (fun n => (g n).toLp 2 volume) atTop (𝓝 (η.toLp 2 volume)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => (g n : Configuration N → SpinAmplitudes N q))
      (fun n => (g n).memLp 2 volume) η (η.memLp 2 volume)).mpr
    convert h₀ using 1
    rfl
  have hcoord (a : Fin N × Fin 3) : Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (g n - η) x (PiLp.single 2 a (1 : ℝ))) 2 volume) atTop (𝓝 0) := by
    have heq (n : ℕ) : (fun x => fderiv ℝ (g n - η) x (PiLp.single 2 a (1 : ℝ))) =
        (fun x => fderiv ℝ (f n) x (PiLp.single 2 a (1 : ℝ)) -
          fderiv ℝ η x (PiLp.single 2 a (1 : ℝ))) := by
      funext x
      change fderiv ℝ ((g n : Configuration N → SpinAmplitudes N q) - (η : Configuration N → SpinAmplitudes N q)) x _ = _
      rw [fderiv_sub (g n).differentiableAt η.differentiableAt, sub_apply]
      rfl
    simpa only [heq] using h₁ (PiLp.single 2 a (1 : ℝ))
  have hkin := tendsto_kineticEnergy_schwartz_of_directional (fun n => g n - η) hcoord
  refine ⟨g, fun n => (hf n).1, ?_, ?_⟩
  · simpa only [sub_self, norm_zero] using (hconv.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => η.toLp 2 volume) atTop
      (𝓝 (η.toLp 2 volume)))).norm
  · simpa only [fourierGraphSeminorm, htoLp] using
      tendsto_radialFourier_eLpNorm_of_kinetic (fun n => (g n - η).toLp 2 volume) hkin

/-- Every finite-kinetic-energy state has compact smooth approximants in the L² mass
and radial Fourier graph seminorm simultaneously. -/
theorem exists_compact_smooth_fourier_form_approximation {N q : ℕ} (u : State N q)
    (hu : kineticEnergy u < ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : 𝓢(Configuration N, SpinAmplitudes N q), HasCompactSupport f ∧
      ‖u - f.toLp 2 volume‖ ≤ ε ∧
      fourierGraphSeminorm (u - f.toLp 2 volume) ≤ ENNReal.ofReal ε := by
  obtain ⟨η, hη₀, hη₁⟩ := exists_schwartz_fourier_weighted_approximation u hu
    (half_pos hε)
  have hηnorm : ‖u - η.toLp 2 volume‖ ≤ ε / 2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (half_pos hε).le).mp
    rw [← Lp.norm_fourier_eq (u - η.toLp 2 volume), ofReal_norm, Lp.enorm_def,
      eLpNorm_fourier_sub_schwartz u η Measure.AbsolutelyContinuous.rfl]
    exact hη₀
  have hηgraph : fourierGraphSeminorm (u - η.toLp 2 volume) ≤ ENNReal.ofReal (ε / 2) := by
    rw [fourierGraphSeminorm, radialFourierMeasure, eLpNorm_fourier_sub_schwartz u η
      (withDensity_absolutelyContinuous _ _)]
    exact hη₁
  obtain ⟨f, hf, hf₀, hf₁⟩ := exists_compact_smooth_schwartz_form_sequence η
  have he₀ : ∀ᶠ n in atTop, ‖(f n).toLp 2 volume - η.toLp 2 volume‖ < ε / 2 :=
    hf₀.eventually_lt_const (half_pos hε)
  have he₁ : ∀ᶠ n in atTop, fourierGraphSeminorm
      ((f n).toLp 2 volume - η.toLp 2 volume) < ENNReal.ofReal (ε / 2) :=
    hf₁.eventually_lt_const (ENNReal.ofReal_pos.mpr (half_pos hε))
  obtain ⟨n, hn₀, hn₁⟩ := (he₀.and he₁).exists
  refine ⟨f n, hf n, ?_, ?_⟩
  · calc
      ‖u - (f n).toLp 2 volume‖ =
          ‖(u - η.toLp 2 volume) + (η.toLp 2 volume - (f n).toLp 2 volume)‖ := by congr 1; abel
      _ ≤ ‖u - η.toLp 2 volume‖ + ‖η.toLp 2 volume - (f n).toLp 2 volume‖ := norm_add_le _ _
      _ ≤ ε := by
        rw [norm_sub_rev (η.toLp 2 volume) ((f n).toLp 2 volume)]
        linarith only [hηnorm, hn₀]
  · calc
      fourierGraphSeminorm (u - (f n).toLp 2 volume) =
          fourierGraphSeminorm ((u - η.toLp 2 volume) -
            ((f n).toLp 2 volume - η.toLp 2 volume)) := by congr 1; abel
      _ ≤ fourierGraphSeminorm (u - η.toLp 2 volume) +
          fourierGraphSeminorm ((f n).toLp 2 volume - η.toLp 2 volume) :=
        fourierGraphSeminorm_sub_le _ _
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hηgraph hn₁.le
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; congr 1; ring

/-- Compact smooth states approximate a finite-energy state with quantitative kinetic
error. The `(2π)²` factor comes from the Fourier convention. -/
theorem exists_compact_smooth_form_approximation {N q : ℕ} (u : State N q)
    (hu : kineticEnergy u < ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : 𝓢(Configuration N, SpinAmplitudes N q), HasCompactSupport f ∧
      ‖u - f.toLp 2 volume‖ ≤ ε ∧
      kineticEnergy (u - f.toLp 2 volume) ≤ ENNReal.ofReal ((2 * Real.pi * ε) ^ 2) := by
  obtain ⟨f, hf, h₀, h₁⟩ := exists_compact_smooth_fourier_form_approximation u hu hε
  refine ⟨f, hf, h₀, ?_⟩
  rw [kineticEnergy_eq_radialFourier_eLpNorm]
  calc
    _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 2) * (ENNReal.ofReal ε) ^ 2 :=
      mul_le_mul' le_rfl (pow_le_pow_left' h₁ 2)
    _ = ENNReal.ofReal ((2 * Real.pi * ε) ^ 2) := by
      rw [← ENNReal.ofReal_pow hε.le, ← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      ring

end LiebThirring.Sobolev

end
