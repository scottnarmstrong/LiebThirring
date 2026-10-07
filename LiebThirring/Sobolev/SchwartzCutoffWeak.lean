/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.SchwartzCutoff
public import LiebThirring.Sobolev.WeakDerivative

/-!
# Extending compact smooth weak derivative tests to Schwartz tests

The cutoff approximation gives convergence in the test graph norm. The L²
inner product is continuous in this norm.
-/

public section

open MeasureTheory Filter
open scoped SchwartzMap ENNReal Topology ContDiff

namespace LiebThirring.Sobolev

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Continuity of an L² pairing under convergence of the L² seminorm of the error. -/
theorem tendsto_integral_inner_of_eLpNorm {μ : Measure E} {f : ℕ → E → F} {η : E → F}
    (hf : ∀ n, MemLp (f n) 2 μ) (hη : MemLp η 2 μ) (g : Lp F 2 μ)
    (ht : Tendsto (fun n => eLpNorm (fun x => f n x - η x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, inner ℂ (f n x) (g x) ∂μ) atTop
      (𝓝 (∫ x, inner ℂ (η x) (g x) ∂μ)) := by
  have hLp : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hη.toLp η)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf η hη).mpr ht
  have hi := hLp.inner (𝕜 := ℂ) (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => g) atTop (𝓝 g))
  have hleft (n : ℕ) : inner ℂ ((hf n).toLp (f n)) g =
      ∫ x, inner ℂ (f n x) (g x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hf n).coeFn_toLp] with x hx
    rw [hx]
  have hright : inner ℂ (hη.toLp η) g = ∫ x, inner ℂ (η x) (g x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hη.coeFn_toLp] with x hx
    rw [hx]
  simpa only [hleft, hright] using hi

/-- A weak coordinate derivative identity extends from compact smooth tests to all
Schwartz spin-amplitude tests on the carriers. -/
theorem HasWeakDerivative.schwartz_test {N q : ℕ} {a : Fin N × Fin 3} {u g : State N q}
    (h : HasWeakDerivative a u g) (η : 𝓢(Configuration N, SpinAmplitudes N q)) :
    (∫ x, inner ℂ (η x) (g x)) =
      -(∫ x, inner ℂ (fderiv ℝ η x (coordinateVector a)) (u x)) := by
  obtain ⟨f, hf, h₀, h₁⟩ := exists_compact_smooth_schwartz_test_approximation η
  have hfLp (n : ℕ) : MemLp (f n) 2 volume :=
    (hf n).2.continuous.memLp_of_hasCompactSupport (hf n).1
  have hdfLp (n : ℕ) : MemLp
      (fun x => fderiv ℝ (f n) x (coordinateVector a)) 2 volume :=
    (((hf n).2.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hf n).1.fderiv_apply ℝ (coordinateVector a))
  have hηdLp : MemLp (fun x => fderiv ℝ η x (coordinateVector a)) 2 volume :=
    ((SchwartzMap.evalCLM ℝ (Configuration N) (SpinAmplitudes N q) (coordinateVector a))
      (SchwartzMap.fderivCLM ℝ (Configuration N) (SpinAmplitudes N q) η)).memLp 2 volume
  have ht₀ := tendsto_integral_inner_of_eLpNorm hfLp (η.memLp 2 volume) g h₀
  have ht₁ := (tendsto_integral_inner_of_eLpNorm hdfLp hηdLp u
    (h₁ (coordinateVector a))).neg
  have hident (n : ℕ) : (∫ x, inner ℂ (f n x) (g x)) =
      -(∫ x, inner ℂ (fderiv ℝ (f n) x (coordinateVector a)) (u x)) :=
    h (f n) (hf n).1 (hf n).2
  exact tendsto_nhds_unique ht₀ (by simpa only [hident] using ht₁)

end LiebThirring.Sobolev

end
