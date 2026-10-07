/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.RemoteFamily
public import LiebThirring.TFUpper.RemoteDensity
public import LiebThirring.TFUpper.SlaterBound

/-! # The remote density on the state carrier

This bridge identifies the packaged TF density with the density of the
one-particle states. A uniform potential bound controls both
the main--remote and remote self interaction. Source: particle-number correction, direct proof.
-/

public section
open MeasureTheory
open scoped ENNReal NNReal SchwartzMap
namespace LiebThirring.TFUpper

theorem remoteOrbitalDensity_eq_slaterOrbitalDensity_ae {q r : ℕ}
    (h : 𝓢(Position, ℂ)) (hh : ∀ x, 1 < ‖x‖ → h x = 0)
    (t : Fin q) (a : Position) (L : ℝ) (hL : 0 < L) :
    ∀ᵐ x : Position,
      (remoteOrbitalDensity h hh t a L hL (r := r)).val x =
        slaterOrbitalDensity (fun i : Fin r => remoteOrbitalState h hh t a L hL i) x := by
  have hv : ∀ᵐ x : Position, ∀ i : Fin r,
      remoteOrbitalState h hh t a L hL i (oneParticleConfiguration x) =
        oneParticleSpinIsometry q (remoteSpinOrbital h hh t a L hL i x) := by
    apply ae_all_iff.mpr
    intro i
    have hi := oneParticleConfigurationEquiv.measurePreserving.quasiMeasurePreserving.ae
      (spatialSpinSchwartzState_ae (remoteSpinOrbital h hh t a L hL i))
    have heval (x : Position) : oneParticleConfigurationEquiv x = oneParticleConfiguration x := rfl
    simpa only [remoteOrbitalState, heval,
      particlePosition_oneParticleConfiguration] using hi
  filter_upwards [remoteOrbitalDensity_coe_ae h hh t a L hL (r := r), hv] with x hx hvx
  rw [hx, slaterOrbitalDensity_eq_sum_norm_sq]
  unfold remoteOrbitalDensityFn
  apply Finset.sum_congr rfl
  intro i _
  rw [hvx i, LinearIsometryEquiv.norm_map]

theorem added_coulomb_cost_le_of_potential_le (d e : TFDensity) (p : ℝ)
    (hp : 0 ≤ p)
    (hpotential : ∀ x, coulombPotential (tfDensityMeasure e) x ≤ ENNReal.ofReal p) :
    2 * tfCoulombEnergy d e + tfCoulombEnergy e e ≤
      p * (tfMass d + tfMass e / 2) := by
  have hcross := TFFunctional.tfCoulombEnergy_le_of_potential_le d e p hp hpotential
  have hself := TFFunctional.tfCoulombEnergy_le_of_potential_le e e p hp hpotential
  nlinarith only [hcross, hself]

end LiebThirring.TFUpper
end
