/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.TFQuantum.SlaterTensorState
public import LiebThirring.TFQuantum.SlaterNorm
/-! # Fourier transformation of general Slater states

The actual Slater State is the normalized finite signed sum of actual ordered
L² products. Fourier transformation acts independently on every orbital in
these products and therefore on the determinant. There is no orthonormality,
normalization, finite kinetic energy, or representative agreement premise.
direct proof determinant expansion and the
proved all-L² particle tensor Fourier transport.
-/

public section
open MeasureTheory WithLp
open scoped FourierTransform
namespace LiebThirring

theorem slaterState_eq_sum_orbitalProductState {N q : ℕ}
    (u : Fin N → State 1 q) :
    slaterState u = ((Real.sqrt N.factorial : ℂ)⁻¹) •
      ∑ σ : Equiv.Perm (Fin N),
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) •
          orbitalProductState (fun j => u (σ j)) := by
  classical
  let terms := fun σ : Equiv.Perm (Fin N) =>
    (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) • orbitalProductState (fun j => u (σ j))
  have ht : ∀ᵐ X : Configuration N, ∀ σ : Equiv.Perm (Fin N),
      terms σ X = (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) •
        orbitalProductAmplitude (fun j => u (σ j)) X := by
    apply ae_all_iff.mpr
    intro σ
    filter_upwards [Lp.coeFn_smul (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)
      (orbitalProductState (fun j => u (σ j))),
      coeFn_orbitalProductState (fun j => u (σ j))] with X hs hp
    rw [hs]
    simp only [Pi.smul_apply]
    rw [hp]
  apply Lp.ext
  filter_upwards [coeFn_slaterState u,
    Lp.coeFn_smul ((Real.sqrt N.factorial : ℂ)⁻¹) (∑ σ, terms σ),
    Lp.coeFn_fun_finsetSum Finset.univ terms, ht] with X hX hs hsum htX
  change slaterState u X = ((((Real.sqrt N.factorial : ℂ)⁻¹) • ∑ σ, terms σ) X)
  rw [hX, hs]
  simp only [Pi.smul_apply]
  rw [hsum]
  ext s
  simp only [slaterAmplitude, PiLp.toLp_apply, PiLp.smul_apply, WithLp.ofLp_sum,
    Finset.sum_apply, Complex.ofReal_inv]
  rw [slaterDeterminant_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [htX]
  rfl

theorem fourier_slaterState {N q : ℕ} (u : Fin N → State 1 q) :
    𝓕 (slaterState u) = slaterState (fun j => 𝓕 (u j)) := by
  rw [slaterState_eq_sum_orbitalProductState, slaterState_eq_sum_orbitalProductState]
  simp only [FourierTransform.fourier_smul, FourierTransform.fourier_sum,
    fourier_orbitalProductState]

end LiebThirring
end
