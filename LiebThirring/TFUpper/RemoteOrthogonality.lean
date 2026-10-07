/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.RemoteFamily

/-! # Orthogonality of main and remote orbital families

Direct proof construction; source
context Lieb–Simon (1977) III.5, (74)--(78), pp. 72--73.
-/

public section
open MeasureTheory Set
open scoped ENNReal NNReal SchwartzMap ComplexConjugate
namespace LiebThirring.TFUpper

theorem inner_remoteOrbitalState_eq_zero_of_main_support {q : ℕ}
    (u : State 1 q) {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (hu : ∀ s : Fin q, ∀ᵐ x : Position ∂volume,
      R < ‖x‖ → orbitalValue u x s = 0)
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (t : Fin q) (i : ℕ) :
    inner ℂ u (remoteOrbitalState h hh t (remoteStart R L) L hL i) = 0 := by
  rw [orbital_inner_eq_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_all_iff.mpr hu,
    ae_all_iff.mpr (fun s => orbitalValue_remoteOrbitalState_ae h hh t s _ L hL i)] with
      x hux hvx
  change (∑ s : Fin q, starRingEnd ℂ (orbitalValue u x s) *
    orbitalValue (remoteOrbitalState h hh t (remoteStart R L) L hL i) x s) = 0
  apply Finset.sum_eq_zero
  intro s _
  rw [hvx s]
  by_cases hx : x ∈ tsupport
      (fun y => remoteSpinOrbital h hh t (remoteStart R L) L hL i y)
  · have hxb := tsupport_remoteSpinOrbital_subset h hh t (remoteStart R L) L hL i hx
    rw [hux s (norm_gt_of_mem_remote_closedBall hR hL i hxb)]
    simp
  · rw [image_eq_zero_of_notMem_tsupport hx]
    simp

theorem inner_main_remoteOrbitalState_eq_zero {n q : ℕ}
    (u : Fin n → State 1 q) {R L : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (hu : ∀ j s, ∀ᵐ x : Position ∂volume,
      R < ‖x‖ → orbitalValue (u j) x s = 0)
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (t : Fin q) (j : Fin n) (i : ℕ) :
    inner ℂ (u j) (remoteOrbitalState h hh t (remoteStart R L) L hL i) = 0 :=
  inner_remoteOrbitalState_eq_zero_of_main_support (u j) hR hL (hu j) h hh t i

end LiebThirring.TFUpper
end
