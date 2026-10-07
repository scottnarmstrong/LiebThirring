/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoForm.SmoothCore
import LiebThirring.Kinetic.Permutation

/-! # Pointwise statistics of smooth joint states

The statistics are almost-everywhere statements about L² classes.
Continuity and full support of Lebesgue volume upgrade these statements on
Schwartz representatives, as needed for the explicit cluster shuffle construction.

-/

public section
open MeasureTheory WithLp
open scoped SchwartzMap
namespace LiebThirring

/-- Electronic statistics hold everywhere on a smooth representative. -/
theorem quantum_antisymmetric_schwartz_iff {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    quantum_antisymmetric (f.toLp 2 volume) ↔
      ∀ (σ : Equiv.Perm (Fin N)) (X : QuantumConfiguration N M) (s : SpinLabels N q),
        f (toLp 2 (permutePositions σ X.fst, X.snd)) (permuteSpins σ s) =
          (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * f X s := by
  refine ⟨?_, quantum_antisymmetric_toLp_of_pointwise f⟩
  intro hf σ X s
  let P := LinearIsometryEquiv.withLpProdCongr 2 (permutationLinearIsometryEquiv σ)
    (LinearIsometryEquiv.refl ℝ (Configuration M))
  have ha : (fun X => f (P X) (permuteSpins σ s)) =ᵐ[volume]
      (fun X => (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * f X s) := by
    filter_upwards [hf σ, f.coeFn_toLp 2 volume,
      (measurePreserving_quantum_electron_permutation σ).quasiMeasurePreserving.ae
        (f.coeFn_toLp 2 volume)] with Y hY h0 hP
    change f (toLp 2 (permutePositions σ Y.fst, Y.snd)) (permuteSpins σ s) = _
    rw [← hP, ← h0]
    exact hY s
  have he := Measure.eq_of_ae_eq ha
    ((PiLp.continuous_apply 2 (fun _ : SpinLabels N q => ℂ) (permuteSpins σ s)).comp (f.continuous.comp P.continuous))
    (continuous_const.mul ((PiLp.continuous_apply 2 (fun _ : SpinLabels N q => ℂ) s).comp f.continuous))
  exact congrFun he X

/-- Nuclear statistics hold everywhere on a smooth representative. -/
theorem nuclear_symmetric_schwartz_iff {N M q : ℕ}
    (f : 𝓢(QuantumConfiguration N M, SpinAmplitudes N q)) :
    nuclear_symmetric (f.toLp 2 volume) ↔
      ∀ (τ : Equiv.Perm (Fin M)) (X : QuantumConfiguration N M) (s : SpinLabels N q),
        f (toLp 2 (X.fst, permutePositions τ X.snd)) s = f X s := by
  refine ⟨?_, nuclear_symmetric_toLp_of_pointwise f⟩
  intro hf τ X s
  let P := LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.refl ℝ (Configuration N)) (permutationLinearIsometryEquiv τ)
  have ha : (fun X => f (P X) s) =ᵐ[volume] (fun X => f X s) := by
    filter_upwards [hf τ, f.coeFn_toLp 2 volume,
      (measurePreserving_quantum_nuclear_permutation τ).quasiMeasurePreserving.ae
        (f.coeFn_toLp 2 volume)] with Y hY h0 hP
    change f (toLp 2 (Y.fst, permutePositions τ Y.snd)) s = _
    rw [← hP, ← h0]
    exact hY s
  have he := Measure.eq_of_ae_eq ha
    ((PiLp.continuous_apply 2 (fun _ : SpinLabels N q => ℂ) s).comp (f.continuous.comp P.continuous))
    ((PiLp.continuous_apply 2 (fun _ : SpinLabels N q => ℂ) s).comp f.continuous)
  exact congrFun he X

end LiebThirring
end
