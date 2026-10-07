/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.RemoteState

/-! # remote orbital families

Direct proof construction; source
context Lieb–Simon (1977) III.5, (74)--(78), pp. 72--73.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal SchwartzMap
namespace LiebThirring.TFUpper

@[expose] noncomputable def remoteOrbitalState {q : ℕ} (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (t : Fin q) (a : Position)
    (L : ℝ) (hL : 0 < L) (i : ℕ) : State 1 q :=
  spatialSpinSchwartzState (remoteSpinOrbital h hh t a L hL i)

theorem norm_remoteOrbitalState {q : ℕ} (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (hn : (∫ x, ‖h x‖ ^ 2) = 1)
    (t : Fin q) (a : Position) (L : ℝ) (hL : 0 < L) (i : ℕ) :
    ‖remoteOrbitalState h hh t a L hL i‖ = 1 := by
  rw [remoteOrbitalState, norm_spatialSpinSchwartzState,
    norm_toLp_remoteSpinOrbital h hh hn t a L hL i]

theorem orthonormal_remoteOrbitalState {q r : ℕ} (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (hn : (∫ x, ‖h x‖ ^ 2) = 1)
    (t : Fin q) (a : Position) (L : ℝ) (hL : 0 < L) :
    Orthonormal ℂ (fun i : Fin r => remoteOrbitalState h hh t a L hL i) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  split_ifs with hij
  · subst j
    rw [inner_self_eq_norm_sq_to_K, norm_remoteOrbitalState h hh hn t a L hL]
    norm_num
  · rw [remoteOrbitalState, remoteOrbitalState, inner_spatialSpinSchwartzState,
      SchwartzMap.inner_toL2_toL2_eq _ _ (volume : Measure Position)]
    exact integral_inner_remoteSpinOrbital_eq_zero h hh t a L hL
      (fun heq => hij (Fin.ext heq))

theorem orbitalValue_remoteOrbitalState_ae {q : ℕ} (h : 𝓢(Position, ℂ))
    (hh : ∀ x, 1 < ‖x‖ → h x = 0) (t s : Fin q) (a : Position)
    (L : ℝ) (hL : 0 < L) (i : ℕ) :
    ∀ᵐ x : Position ∂volume,
      orbitalValue (remoteOrbitalState h hh t a L hL i) x s =
        remoteSpinOrbital h hh t a L hL i x s :=
  orbitalValue_spatialSpinSchwartzState_ae _ s

end LiebThirring.TFUpper
end
