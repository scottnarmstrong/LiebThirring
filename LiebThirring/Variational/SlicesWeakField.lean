/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.SlicesResidual
public import LiebThirring.Variational.SlicesSmooth
public import LiebThirring.Variational.SlicesWeak

/-! # Outer L² fields of residual weak graphs -/

@[expose] public section

open MeasureTheory WithLp
open scoped ENNReal
open Filter Topology

namespace LiebThirring.Variational

/-- Pack a state and its selected residual derivatives into one outer L² graph field. -/
noncomputable def residualGraphField {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (s : Fin q) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) :
    Lp (Sobolev.FormGraphAmbient k q) 2 (volume : Measure Position) :=
  (finiteLpPiLpEquiv (volume : Measure Position)
    (fun _ : Option (Fin k × Fin 3) => State k q)).symm
      (toLp 2 fun t => match t with
        | none => residualSliceFieldCLM i e s u
        | some a => residualSliceFieldCLM i e s (g ((e a.1).val, a.2)))

/-- Zeroth component of the packed residual graph field. -/
theorem residualGraphField_none {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (s : Fin q) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) :
    (finiteLpPiLpEquiv (volume : Measure Position)
      (fun _ : Option (Fin k × Fin 3) => State k q) (residualGraphField i e s u g)) none =
      residualSliceFieldCLM i e s u := by
  rw [residualGraphField, LinearIsometryEquiv.apply_symm_apply]

/-- Derivative components of the packed residual graph field. -/
theorem residualGraphField_some {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (s : Fin q) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) (a : Fin k × Fin 3) :
    (finiteLpPiLpEquiv (volume : Measure Position)
      (fun _ : Option (Fin k × Fin 3) => State k q) (residualGraphField i e s u g)) (some a) =
      residualSliceFieldCLM i e s (g ((e a.1).val, a.2)) := by
  rw [residualGraphField, LinearIsometryEquiv.apply_symm_apply]

/-- Componentwise L² convergence gives convergence of the packed residual graph fields. -/
theorem residualGraphField_tendsto {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (s : Fin q)
    (u : ℕ → State N q) (u0 : State N q)
    (g : ℕ → (Fin N × Fin 3) → State N q)
    (g0 : (Fin N × Fin 3) → State N q)
    (hu : Tendsto u atTop (𝓝 u0))
    (hg : ∀ a, Tendsto (fun n => g n a) atTop (𝓝 (g0 a))) :
    Tendsto (fun n => residualGraphField i e s (u n) (g n)) atTop
      (𝓝 (residualGraphField i e s u0 g0)) := by
  unfold residualGraphField
  apply ((finiteLpPiLpEquiv (volume : Measure Position)
    (fun _ : Option (Fin k × Fin 3) => State k q)).symm.continuous.tendsto _).comp
  apply (PiLp.continuous_toLp 2
    (fun _ : Option (Fin k × Fin 3) =>
      Lp (State k q) 2 (volume : Measure Position)) |>.tendsto _).comp
  apply tendsto_pi_nhds.mpr
  intro t
  cases t with
  | none => exact ((residualSliceFieldCLM i e s).continuous.tendsto u0).comp hu
  | some a => exact ((residualSliceFieldCLM i e s).continuous.tendsto
      (g0 ((e a.1).val, a.2))).comp (hg ((e a.1).val, a.2))

/-- On one common full-measure set, every packed slot is its literal residual slice. -/
theorem residualGraphField_ae_slots {N k q : ℕ} (i : Fin N)
    (e : Fin k ≃ {j : Fin N // j ≠ i}) (s : Fin q) (u : State N q)
    (g : (Fin N × Fin 3) → State N q) :
    ∀ᵐ x : Position, ∀ t : Option (Fin k × Fin 3),
      residualGraphField i e s u g x t = match t with
        | none => residualParticleSlice i e u x s
        | some a => residualParticleSlice i e (g ((e a.1).val, a.2)) x s := by
  rw [ae_all_iff]
  intro t
  cases t with
  | none =>
      filter_upwards [finiteLpPiLpEquiv_apply_ae (volume : Measure Position)
          (fun _ : Option (Fin k × Fin 3) => State k q)
          (residualGraphField i e s u g) none,
        residualSliceFieldCLM_ae i e s u] with x ht hs
      rw [residualGraphField_none] at ht
      exact ht.symm.trans hs
  | some a =>
      filter_upwards [finiteLpPiLpEquiv_apply_ae (volume : Measure Position)
          (fun _ : Option (Fin k × Fin 3) => State k q)
          (residualGraphField i e s u g) (some a),
        residualSliceFieldCLM_ae i e s (g ((e a.1).val, a.2))] with x ht hs
      rw [residualGraphField_some] at ht
      exact ht.symm.trans hs

end LiebThirring.Variational

end
