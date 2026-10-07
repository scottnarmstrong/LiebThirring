/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SlicesSubsetWeak
public import LiebThirring.Variational.SlicesSubsetAntisymmetric
public import LiebThirring.Variational.FormAlgebra

/-! # Form-domain representatives of particle-block slices -/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal Classical

namespace LiebThirring.Variational

/-- A total form-domain-valued version of the one-particle residual slice. -/
noncomputable def residualParticleFormSlice {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q) (x : Position)
    (s : Fin q) : FormDomain k q :=
  if h : antisymmetric (residualParticleSlice i e u x s) ∧
      kineticEnergy (residualParticleSlice i e u x s) < ⊤ then
    ⟨residualParticleSlice i e u x s, h⟩
  else 0

theorem residualParticleFormSlice_ae {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q)
    (hanti : antisymmetric u) (hkin : kineticEnergy u < ⊤) :
    ∀ᵐ x : Position, ∀ s : Fin q,
      ((residualParticleFormSlice i e u x s : FormDomain k q) : State k q) =
        residualParticleSlice i e u x s := by
  filter_upwards [residualParticleSlice_antisymmetric_ae i e u hanti,
    residualParticleSlice_kineticEnergy_lt_top_ae i e u hkin] with x ha hk
  intro s
  simp [residualParticleFormSlice, ha s, hk s]

end LiebThirring.Variational
end
