/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Kinetic.DensityBasic

/-! # density from an actual amplitude representative

A representative equality in configuration space yields equality of all
integrated one-particle marginals almost everywhere. The replacement
amplitude needs no additional measurability hypothesis.
direct proof product-measure transport.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring

/-- An a.e. amplitude representative gives the density a.e. -/
theorem density_eq_marginals_of_ae_eq {N q : ℕ} (ψ : State N q)
    (f : Configuration N → SpinAmplitudes N q) (hψ : ψ =ᵐ[volume] f) :
    density ψ =ᵐ[volume] fun x : Position =>
      ∑ i : Fin N, ∫⁻ y : OtherConfiguration i,
        (‖f (insertParticle i x y)‖₊ : ℝ≥0∞) ^ 2 := by
  have hi (i : Fin N) : ∀ᵐ x : Position,
      (∫⁻ y : OtherConfiguration i, (‖ψ (insertParticle i x y)‖₊ : ℝ≥0∞) ^ 2) =
        ∫⁻ y : OtherConfiguration i, (‖f (insertParticle i x y)‖₊ : ℝ≥0∞) ^ 2 := by
    have h := (measurePreserving_insertParticle i).quasiMeasurePreserving.ae hψ
    rw [Measure.volume_eq_prod] at h
    filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
    exact lintegral_congr_ae (hx.mono fun y hy => by dsimp only; rw [hy])
  filter_upwards [Filter.eventually_all.mpr hi] with x hx
  exact Finset.sum_congr rfl (fun i _ => hx i)

end LiebThirring
end
