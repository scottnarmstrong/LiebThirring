/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.LocalWeakGraph
public import LiebThirring.Sobolev.FormGraph

/-!
# Configuration-space local weak Sobolev graphs

Each physical coordinate derivative has a local L² slot. The Neumann form
domain is the full local weak-H¹ graph: no boundary derivative condition is
imposed. Its derivative energy is the sum of the physical L² gradient norms.
-/

@[expose] public section

open MeasureTheory
open LiebThirring.Sobolev

namespace LiebThirring.TFCubes

/-- Spin-valued L² on a measurable configuration-space region. -/
noncomputable abbrev ConfigurationRegionState (N q : ℕ) (Ω : Set (Configuration N)) :=
  RegionState (Configuration N) (SpinAmplitudes N q) Ω

/-- A local state and one local L² slot for every physical derivative. -/
noncomputable abbrev LocalFormGraphAmbient (N q : ℕ) (Ω : Set (Configuration N)) :=
  PiLp 2 (fun _ : Option (Fin N × Fin 3) => ConfigurationRegionState N q Ω)

/-- The complete physical local weak-gradient graph. -/
noncomputable def localFormGraph (N q : ℕ) (Ω : Set (Configuration N)) :
    Submodule ℂ (LocalFormGraphAmbient N q Ω) where
  carrier := {v | ∀ a, HasWeakDerivativeOn Ω (coordinateVector a) (v none) (v (some a))}
  zero_mem' := by
    intro a
    exact HasWeakDerivativeOn.zero Ω (coordinateVector a)
  add_mem' := by
    intro v w hv hw a
    exact (hv a).add (hw a)
  smul_mem' := by
    intro c v hv a
    exact (hv a).smul c

/-- The physical local gradient energy, with kinetic normalization `-Δ`. -/
noncomputable def localGradientEnergy {N q : ℕ} {Ω : Set (Configuration N)}
    (v : LocalFormGraphAmbient N q Ω) : ℝ :=
  ∑ a : Fin N × Fin 3, ‖v (some a)‖ ^ 2

/-- Each local derivative norm is its literal restricted physical integral. -/
theorem norm_sq_configurationRegionState {N q : ℕ} {Ω : Set (Configuration N)}
    (u : ConfigurationRegionState N q Ω) :
    ‖u‖ ^ 2 = ∫ x in Ω, ‖u x‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) u u)]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (u x)).symm

/-- On an open region the local graph state uniquely determines all derivative slots. -/
theorem localFormGraph_ext_state {N q : ℕ} {Ω : Set (Configuration N)} (hΩ : IsOpen Ω)
    {v w : localFormGraph N q Ω}
    (hstate : (v : LocalFormGraphAmbient N q Ω) none =
      (w : LocalFormGraphAmbient N q Ω) none) : v = w := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  cases i with
  | none => exact hstate
  | some a =>
    have hv := v.property a
    rw [hstate] at hv
    exact hv.unique (w.property a) hΩ

end LiebThirring.TFCubes

end
