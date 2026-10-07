/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.Append
public import LiebThirring.TFUpper.StateDensity
public import LiebThirring.TFUpper.SpatialKinetic
public import LiebThirring.TFUpper.ScaleSelection
public import LiebThirring.TFUpper.PotentialSelection
import LiebThirring.TFUpper.RemoteOrthogonality

/-! # Exact particle-number correction by actual remote orbitals

Given a compactly supported finite orthonormal main family, append exactly
the missing number of normalized compact Schwartz orbitals. Their disjoint
balls lie beyond the main support. Dilation makes the kinetic sum
and the uniform Coulomb potential small simultaneously, and the added
nuclear attraction has favorable sign. The Slater construction determinant construction is
supplied by the proved Slater API. No particle-number monotonicity is assumed.

Direct proof; see the explicit construction and
estimates in `RemoteOrbitals`, `RemoteState`, and `RemoteDensityBounds`.
-/

public section
open MeasureTheory Filter
open scoped ENNReal NNReal SchwartzMap Topology
namespace LiebThirring.TFUpper

/-- A genuine exact-`N` Slater trial with arbitrarily small added cost.
The main support and density are literal properties of `u`. -/
theorem exists_exact_particle_trial
    (q : {q : ℕ // 1 ≤ q}) {n M : ℕ} (α : ℝ≥0)
    (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (u : Fin n → State 1 q.val) (hu : Orthonormal ℂ u)
    (hf : ∀ i, kineticEnergy (u i) < ⊤)
    (S : ℝ) (hS : 0 ≤ S)
    (hs : ∀ i, ∀ᵐ x : Position, S < ‖x‖ → orbitalValue (u i) x = 0)
    (d : TFDensity) (hd : ∀ᵐ x : Position, d.val x = slaterOrbitalDensity u x)
    (N : ℕ) (hle : n ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : ElectronicTrial N q.val,
      dilatedElectronicEnergy α z R ψ.val ≤ orbitalUpperEnergy α z R u + ε := by
  classical
  let r := N - n
  suffices hex : ∃ ψ : ElectronicTrial (n + r) q.val,
      dilatedElectronicEnergy α z R ψ.val ≤ orbitalUpperEnergy α z R u + ε by
    have hnr : n + r = N := by dsimp only [r]; omega
    exact Eq.mp (congrArg (fun k => ∃ ψ : ElectronicTrial k q.val,
      dilatedElectronicEnergy α z R ψ.val ≤ orbitalUpperEnergy α z R u + ε) hnr) hex
  obtain ⟨h, _, hh, hn⟩ := exists_normalized_compact_schwartz_orbital
  let t : Fin q.val := ⟨0, show 0 < q.val from q.property⟩
  let A : ℝ := (α : ℝ) ^ (-(5 : ℝ) / 3)
  let B : ℝ := (α : ℝ) ^ (-(2 : ℝ)) * (tfMass d + (r : ℝ) / 2)
  let p : ℝ := ε / (2 * (A + B + 1))
  have hA : 0 ≤ A := Real.rpow_nonneg α.property _
  have hB : 0 ≤ B := mul_nonneg (Real.rpow_nonneg α.property _)
    (add_nonneg (TFFunctional.tfMass_nonneg d)
      (div_nonneg (Nat.cast_nonneg r) (by norm_num)))
  have hp : 0 < p := div_pos hε (by linarith only [hA, hB])
  have hkin := eventually_remoteSpinOrbital_kinetic_lt (r := r) h hh t p hp
  have hpot := eventually_remoteOrbitalDensity_potential_le (r := r) h hh hn t p hp
  obtain ⟨L, hLone, hLkin, hLpot⟩ :=
    ((eventually_ge_atTop (1 : ℝ)).and (hkin.and hpot)).exists
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  let a := remoteStart S L
  let v : Fin r → State 1 q.val := fun i => remoteOrbitalState h hh t a L hL i
  let e : TFDensity := remoteOrbitalDensity h hh t a L hL (r := r)
  have he : ∀ᵐ x : Position, e.val x = slaterOrbitalDensity v x :=
    remoteOrbitalDensity_eq_slaterOrbitalDensity_ae h hh t a L hL
  have hv : Orthonormal ℂ v := orthonormal_remoteOrbitalState h hh hn t a L hL
  have hcross : ∀ i j, inner ℂ (u i) (v j) = 0 := by
    intro i j
    apply inner_main_remoteOrbitalState_eq_zero u hS hL _ h hh t i j
    intro k s
    filter_upwards [hs k] with x hx hxs
    exact congrArg (fun f : Fin q.val → ℂ => f s) (hx hxs)
  have hvf : ∀ i, kineticEnergy (v i) < ⊤ := fun i =>
    kineticEnergy_spatialSpinSchwartzState_lt_top (remoteSpinOrbital h hh t a L hL i)
  have huf : ∀ i, kineticEnergy (Fin.addCases u v i) < ⊤ := by
    intro i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simpa only [Fin.addCases_left] using hf k
    · simpa only [Fin.addCases_right] using hvf k
  have hK : (∑ i, (kineticEnergy (v i)).toReal) < p := by
    change (∑ i : Fin r, (kineticEnergy
      (spatialSpinSchwartzState (remoteSpinOrbital h hh t a L hL i))).toReal) < p
    simp_rw [kineticEnergy_spatialSpinSchwartzState_toReal]
    exact hLkin hL a
  clear_value v
  have huv : Orthonormal ℂ (Fin.addCases u v) :=
    orthonormal_addCases u v hu hv hcross
  have happ := orbitalUpperEnergy_append_le α z R u v d e hd he
  have hC := added_coulomb_cost_le_of_potential_le d e p hp.le (hLpot hL a)
  have hemass : tfMass e = (r : ℝ) := tfMass_remoteOrbitalDensity h hh hn t a L hL
  rw [hemass] at hC
  have hcost : A * (∑ i, (kineticEnergy (v i)).toReal) +
      (α : ℝ) ^ (-(2 : ℝ)) * (2 * tfCoulombEnergy d e + tfCoulombEnergy e e) < ε := by
    have hsmall := weighted_small_cost_le A B ε (∑ i, (kineticEnergy (v i)).toReal)
      p hA hB hε hK.le le_rfl
    have hmul := mul_le_mul_of_nonneg_left hC (Real.rpow_nonneg α.property (-(2 : ℝ)))
    apply lt_of_le_of_lt _ hsmall
    apply add_le_add_right
    dsimp only [B]
    rw [mul_comm p _, ← mul_assoc] at hmul
    exact hmul
  let w : Fin (n + r) → State 1 q.val := Fin.addCases u v
  have hw : Orthonormal ℂ w := huv
  have hwf : ∀ i, kineticEnergy (w i) < ⊤ := huf
  have hwd : ∀ᵐ x : Position, (TFFunctional.tfDensityAdd d e).val x =
      slaterOrbitalDensity w x := tfDensity_add_represents_append u v d e hd he
  have hwupper : orbitalUpperEnergy α z R w ≤
      orbitalUpperEnergy α z R u + (α : ℝ) ^ (-(5 : ℝ) / 3) *
        ∑ i, (kineticEnergy (v i)).toReal +
        (α : ℝ) ^ (-(2 : ℝ)) * (2 * tfCoulombEnergy d e + tfCoulombEnergy e e) := happ
  clear_value w
  obtain ⟨ψ, hψ⟩ := @exists_dilated_slater_trial_le (n + r) q.val M α z R w
    (TFFunctional.tfDensityAdd d e) hwd hw hwf
  refine ⟨ψ, hψ.trans (hwupper.trans ?_)⟩
  dsimp only [A] at hcost
  simpa only [add_assoc] using add_le_add_right hcost.le (orbitalUpperEnergy α z R u)

end LiebThirring.TFUpper
end
