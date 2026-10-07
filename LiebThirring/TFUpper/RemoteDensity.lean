/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.RemoteOrbitals
public import LiebThirring.TFFunctional.TrialDensities

/-! # Densities of finite remote-orbital families

This module packages the actual density of the concrete remote Schwartz orbitals
used in the particle-number correction and proves its mass and scaling laws.
-/

public section

open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace LiebThirring.TFUpper

/-- The literal spatial density of the concrete remote orbital family. -/
@[expose] noncomputable def remoteOrbitalDensityFn {q r : ℕ}
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (t : Fin q) (a : Position) (L : ℝ) (hL : 0 < L) (x : Position) : ℝ :=
  ∑ i : Fin r, ‖remoteSpinOrbital h hh t a L hL i x‖ ^ 2

theorem continuous_remoteOrbitalDensityFn {q r : ℕ}
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (t : Fin q) (a : Position) (L : ℝ) (hL : 0 < L) :
    Continuous (remoteOrbitalDensityFn h hh t a L hL (r := r)) := by
  unfold remoteOrbitalDensityFn
  fun_prop

theorem hasCompactSupport_remoteOrbitalDensityTerm {q : ℕ}
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (t : Fin q) (a : Position) (L : ℝ) (hL : 0 < L) (i : ℕ) :
    HasCompactSupport (fun x => ‖remoteSpinOrbital h hh t a L hL i x‖ ^ 2) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (remoteOrbitalCenter a L i) L)
  intro x hx
  have hx' : remoteSpinOrbital h hh t a L hL i x ≠ 0 := by
    intro hz
    exact hx (by simp [hz])
  exact (tsupport_remoteSpinOrbital_subset h hh t a L hL i) (subset_tsupport _ hx')

theorem hasCompactSupport_remoteOrbitalDensityFn {q r : ℕ}
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (t : Fin q) (a : Position) (L : ℝ) (hL : 0 < L) :
    HasCompactSupport (remoteOrbitalDensityFn h hh t a L hL (r := r)) := by
  let f : Fin r → Position → ℝ :=
    fun i x => ‖remoteSpinOrbital h hh t a L hL i x‖ ^ 2
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin r)), HasCompactSupport (f i) := by
    intro i _
    exact hasCompactSupport_remoteOrbitalDensityTerm h hh t a L hL i
  rw [show remoteOrbitalDensityFn h hh t a L hL (r := r) = ∑ i : Fin r, f i by
    funext x
    unfold remoteOrbitalDensityFn
    simp only [Finset.sum_apply, f]]
  exact HasCompactSupport.finset_sum hf

/-- The actual density bundled in the Thomas--Fermi carrier. -/
@[expose] noncomputable def remoteOrbitalDensity {q r : ℕ}
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (t : Fin q) (a : Position) (L : ℝ) (hL : 0 < L) : TFDensity :=
  TFFunctional.tfDensityOfFunction (remoteOrbitalDensityFn h hh t a L hL (r := r))
    ((continuous_remoteOrbitalDensityFn h hh t a L hL (r := r)).memLp_of_hasCompactSupport
      (hasCompactSupport_remoteOrbitalDensityFn h hh t a L hL (r := r)))
    (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (memLp_one_iff_integrable.mp
      ((continuous_remoteOrbitalDensityFn h hh t a L hL (r := r)).memLp_of_hasCompactSupport
        (hasCompactSupport_remoteOrbitalDensityFn h hh t a L hL (r := r))))

theorem remoteOrbitalDensity_coe_ae {q r : ℕ}
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (t : Fin q) (a : Position) (L : ℝ) (hL : 0 < L) :
    (remoteOrbitalDensity h hh t a L hL (r := r)).val =ᵐ[volume]
      remoteOrbitalDensityFn h hh t a L hL (r := r) :=
  TFFunctional.tfDensityOfFunction_coeFn _ _ _ _

/-- The remote density has exactly one unit of mass per orbital. -/
theorem tfMass_remoteOrbitalDensity {q r : ℕ}
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (hn : (∫ x, ‖h x‖ ^ 2) = 1) (t : Fin q) (a : Position)
    (L : ℝ) (hL : 0 < L) :
    tfMass (remoteOrbitalDensity h hh t a L hL (r := r)) = r := by
  unfold tfMass
  rw [integral_congr_ae (remoteOrbitalDensity_coe_ae h hh t a L hL)]
  unfold remoteOrbitalDensityFn
  rw [integral_finsetSum _]
  · have hone (i : Fin r) :
        (∫ x, ‖remoteSpinOrbital h hh t a L hL i x‖ ^ 2) = 1 := by
      simp only [remoteSpinOrbital, norm_escapeSpinOrbital]
      change (∫ x, ‖escapeOrbital (fun y => h y) L (remoteOrbitalCenter a L i) x‖ ^ 2) = 1
      rw [integral_norm_sq_escapeOrbital (fun y => h y) L hL, hn]
    simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  · intro i _
    exact memLp_one_iff_integrable.mp
      (((remoteSpinOrbital h hh t a L hL i).continuous.norm.pow 2).memLp_of_hasCompactSupport
        (hasCompactSupport_remoteOrbitalDensityTerm h hh t a L hL i))

end LiebThirring.TFUpper

end
