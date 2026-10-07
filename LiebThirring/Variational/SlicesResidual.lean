/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SlicesReindex

/-!
# Literal residual-state slices

The selected position and spin are fixed first by the existing currying isometry. An explicit
ordering equivalence then transports the remaining particles to a literal state carrier.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace LiebThirring.Variational

/-- The residual state at selected position `x` and spin `s`, with explicitly ordered particles. -/
noncomputable def residualParticleSlice {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q) (x : Position) (s : Fin q) :
    State k q :=
  residualStateReindex i e (oneParticleCurrying i u x s)

/-- Fixed-spin residual slicing as a bounded outer-L² operator. -/
noncomputable def residualSliceFieldCLM {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (s : Fin q) :
    State N q →L[ℂ] Lp (State k q) 2 (volume : Measure Position) :=
  ((residualStateReindex i e).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
      2 (volume : Measure Position)).comp
    (((PiLp.proj (𝕜 := ℂ) 2
      (fun _ : Fin q => RestState i q) s).compLpL 2
        (volume : Measure Position)).comp
      (oneParticleCurrying i).toContinuousLinearMap)

/-- The bounded residual slice field evaluates to the literal residual slice almost everywhere. -/
theorem residualSliceFieldCLM_ae {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (s : Fin q) (u : State N q) :
    ∀ᵐ x : Position, residualSliceFieldCLM i e s u x = residualParticleSlice i e u x s := by
  filter_upwards [((residualStateReindex i e).toContinuousLinearEquiv.toContinuousLinearMap).coeFn_compLp
      (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q => RestState i q) s).compLpL 2
        (volume : Measure Position)) (oneParticleCurrying i u)),
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q => RestState i q) s).coeFn_compLp
      (oneParticleCurrying i u)] with x hr hp
  exact hr.trans (congrArg (residualStateReindex i e) hp)

/-- The residual-state slice has the expected inserted-state representative. -/
theorem residualParticleSlice_ae {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (u : State N q) :
    ∀ᵐ x : Position, ∀ s : Fin q, ∀ᵐ y : Configuration k, ∀ t : SpinLabels k q,
      residualParticleSlice i e u x s y t =
        u (insertParticle i x (Sobolev.configurationReindexMeasurableEquiv e y))
          (insertSpin i s (fun j => t (e.symm j))) := by
  filter_upwards [oneParticleCurrying_ae i u] with x hx
  intro s
  have hc := (Sobolev.measurePreserving_configurationReindex e).quasiMeasurePreserving.ae (hx s)
  filter_upwards [residualStateReindex_ae i e (oneParticleCurrying i u x s), hc]
    with y hr hc
  intro t
  exact (hr t).trans (hc (fun j => t (e.symm j)))

end LiebThirring.Variational

end
