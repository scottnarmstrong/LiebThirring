/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.RealEnergy
import LiebThirring.Kinetic.Permutation

/-! # Scalar homogeneity on the fermionic form domain -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- The squared-norm expectation of any nonnegative weight is homogeneous. -/
theorem trial_lintegral_weight_smul {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [NormedSpace ℂ H] {μ : Measure α}
    (p : α → ℝ≥0∞) (c : ℂ) (u : Lp H 2 μ) :
    (∫⁻ x, p x * (‖(c • u) x‖₊ : ℝ≥0∞) ^ 2 ∂μ) =
      (‖c‖₊ : ℝ≥0∞) ^ 2 * ∫⁻ x, p x * (‖u x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  calc
    _ = ∫⁻ x, (‖c‖₊ : ℝ≥0∞) ^ 2 * (p x * (‖u x‖₊ : ℝ≥0∞) ^ 2) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_smul c u] with x hx
      rw [hx]
      simp only [Pi.smul_apply, nnnorm_smul, ENNReal.coe_mul, mul_pow]
      ring
    _ = _ := lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)

/-- Fourier kinetic energy is homogeneous under complex scalars. -/
theorem trial_kineticEnergy_smul {N q : ℕ} (c : ℂ) (u : State N q) :
    kineticEnergy (c • u) = (‖c‖₊ : ℝ≥0∞) ^ 2 * kineticEnergy u := by
  unfold kineticEnergy
  rw [map_smul]
  exact trial_lintegral_weight_smul
    (fun ξ : Configuration N => ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2)
    c (Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) u)

/-- Complex scalar multiples preserve fermionic antisymmetry. -/
theorem trial_antisymmetric_smul {N q : ℕ} (c : ℂ) (u : State N q)
    (hu : antisymmetric u) : antisymmetric (c • u) := by
  intro σ
  filter_upwards [hu σ, Lp.coeFn_smul c u,
    (measurePreserving_permutePositions σ).quasiMeasurePreserving.ae (Lp.coeFn_smul c u)]
    with x hx hs hσ
  intro s
  rw [hs, hσ]
  change c * u (permutePositions σ x) (permuteSpins σ s) =
    (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * (c * u x s)
  rw [hx]
  ring

/-- Scalar multiplication on the form-domain subtype. -/
@[expose] noncomputable def trialFormDomainSmul {N q : ℕ}
    (c : ℂ) (u : FormDomain N q) : FormDomain N q :=
  ⟨c • u.val, trial_antisymmetric_smul c u.val u.property.1, by
    rw [trial_kineticEnergy_smul]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) u.property.2⟩

/-- The real energy scales by squared scalar norm, on the whole unnormalized domain. -/
theorem realEnergy_trialFormDomainSmul {N q M : ℕ}
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (c : ℂ) (u : FormDomain N q) :
    realEnergy z R hR (trialFormDomainSmul c u) = ‖c‖ ^ 2 * realEnergy z R hR u := by
  unfold realEnergy
  change (kineticEnergy (c • u.val)).toReal +
      (∫⁻ x : Configuration N, electronRepulsion x * (‖(c • u.val) x‖₊ : ℝ≥0∞) ^ 2).toReal +
      (nuclearRepulsion z R).toReal * ‖c • u.val‖ ^ 2 -
      (∫⁻ x : Configuration N, attraction z R x * (‖(c • u.val) x‖₊ : ℝ≥0∞) ^ 2).toReal = _
  rw [trial_kineticEnergy_smul, trial_lintegral_weight_smul, trial_lintegral_weight_smul]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm,
    norm_smul, mul_pow]
  ring

end LiebThirring

end
