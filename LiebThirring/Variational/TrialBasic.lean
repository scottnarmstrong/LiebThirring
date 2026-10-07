/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.FormDomain
public import LiebThirring.Theorems.KineticEnergySchwartz
public import LiebThirring.Kinetic.Permutation
import LiebThirring.Fourier.Schwartz

/-! # From nonzero antisymmetric Schwartz functions to normalized trials -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring

/-- Every directional derivative of a Schwartz function has finite squared integral. -/
theorem schwartz_lintegral_fderiv_lt_top
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (f : 𝓢(V, H)) (m : V) :
    (∫⁻ x : V, (‖fderiv ℝ (fun y => f y) x m‖₊ : ℝ≥0∞) ^ 2) < ⊤ := by
  let g : 𝓢(V, H) := LineDeriv.lineDerivOp m f
  have hg : (∫⁻ x : V, (‖g x‖₊ : ℝ≥0∞) ^ 2) < ⊤ := by
    rw [Fourier.lintegral_norm_sq_eq_ofReal_integral]
    exact ENNReal.ofReal_lt_top
  simpa only [g, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hg

/-- Schwartz states have finite kinetic energy. -/
theorem kineticEnergy_schwartz_lt_top {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) :
    kineticEnergy (f.toLp 2 (volume : Measure (Configuration N))) < ⊤ := by
  classical
  rw [kineticEnergy_schwartz]
  apply ENNReal.sum_lt_top.mpr
  intro i _
  apply ENNReal.sum_lt_top.mpr
  intro a _
  exact schwartz_lintegral_fderiv_lt_top f (PiLp.single 2 (i, a) (1 : ℝ))

/-- Pointwise fermionic covariance descends to the L² representative. -/
theorem antisymmetric_toLp_of_pointwise {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (hf : ∀ (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q),
      f (permutePositions σ x) (permuteSpins σ s) =
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * f x s) :
    antisymmetric (f.toLp 2 (volume : Measure (Configuration N))) := by
  intro σ
  filter_upwards [f.coeFn_toLp 2 (volume : Measure (Configuration N)),
    (measurePreserving_permutePositions σ).quasiMeasurePreserving.ae
      (f.coeFn_toLp 2 (volume : Measure (Configuration N)))] with x hx hσ
  intro s
  rw [hx, hσ]
  exact hf σ x s

/-- A nonzero Schwartz function represents a nonzero L² state. -/
theorem schwartz_toLp_ne_zero {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (hf : f ≠ 0) :
    f.toLp 2 (volume : Measure (Configuration N)) ≠ 0 := by
  intro h
  apply hf
  apply DFunLike.ext
  have heq : (fun x => f x) =ᵐ[volume] fun _ => (0 : SpinAmplitudes N q) := by
    filter_upwards [f.coeFn_toLp 2 (volume : Measure (Configuration N)),
      Lp.coeFn_zero (SpinAmplitudes N q) 2 (volume : Measure (Configuration N))] with x hx hz
    rw [h] at hx
    exact hx.symm.trans hz
  intro x
  exact congrFun (Measure.eq_of_ae_eq heq f.continuous continuous_const) x

/-- Scaling a nonzero Schwartz function by its inverse L² norm normalizes it. -/
theorem norm_schwartz_toLp_normalize {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (hf : f ≠ 0) :
    ‖((‖f.toLp 2 (volume : Measure (Configuration N))‖⁻¹ • f).toLp 2
      (volume : Measure (Configuration N)))‖ = 1 := by
  have hnorm : ‖f.toLp 2 (volume : Measure (Configuration N))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (schwartz_toLp_ne_zero f hf)
  change ‖(SchwartzMap.toLpCLM ℝ (SpinAmplitudes N q) 2
    (volume : Measure (Configuration N))) (‖f.toLp 2 (volume : Measure (Configuration N))‖⁻¹ • f)‖ = 1
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ hnorm

/-- Normalization within Schwartz space preserves covariance and finite kinetic energy. -/
theorem exists_normalized_formDomain_of_schwartz {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (hf : f ≠ 0)
    (hanti : ∀ (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q),
      f (permutePositions σ x) (permuteSpins σ s) =
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * f x s) :
    ∃ ψ : FormDomain N q, ‖(ψ : State N q)‖ = 1 := by
  let c : ℝ := ‖f.toLp 2 (volume : Measure (Configuration N))‖⁻¹
  let g := c • f
  have hganti : ∀ (σ : Equiv.Perm (Fin N)) (x : Configuration N) (s : SpinLabels N q),
      g (permutePositions σ x) (permuteSpins σ s) =
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * g x s := by
    intro σ x s
    change (c : ℂ) * f (permutePositions σ x) (permuteSpins σ s) =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ((c : ℂ) * f x s)
    rw [hanti]
    ring
  refine ⟨⟨g.toLp 2 (volume : Measure (Configuration N)),
    antisymmetric_toLp_of_pointwise g hganti, kineticEnergy_schwartz_lt_top g⟩, ?_⟩
  exact norm_schwartz_toLp_normalize f hf

end LiebThirring

end
