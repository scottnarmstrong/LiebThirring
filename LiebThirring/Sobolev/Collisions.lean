/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Kinetic.DensityBasic

/-!
# Collision null sets on the configuration carrier

Fixed-pole and electron-electron collisions have zero volume,
including products with spectator coordinates and finite counting spin measures.
The insertion equivalence is the existing measure-preserving particle insertion.
-/

public section

open MeasureTheory WithLp

namespace LiebThirring.Sobolev

/-- The position of a spectator is independent of the inserted particle. -/
theorem particlePosition_insertParticle_other {N : ℕ} (i j : Fin N) (hji : j ≠ i)
    (x : Position) (y : OtherConfiguration i) :
    particlePosition (insertParticle i x y) j = toLp 2 (fun a => y (⟨j, hji⟩, a)) := by
  ext a
  simp only [particlePosition, insertParticle, PiLp.toLp_apply, dite_eq_right hji]

/-- A selected electron equals a fixed pole on a null set. -/
theorem volume_particlePosition_eq {N : ℕ} (i : Fin N) (c : Position) :
    volume {x : Configuration N | particlePosition x i = c} = 0 := by
  have hs : MeasurableSet {x : Configuration N | particlePosition x i = c} :=
    measurableSet_eq_fun (measurable_particlePosition i) measurable_const
  rw [← (measurePreserving_insertParticle i).measure_preimage hs.nullMeasurableSet]
  change (volume.prod volume) {z : Position × OtherConfiguration i |
    particlePosition (insertParticle i z.1 z.2) i = c} = 0
  have hsp : MeasurableSet {z : Position × OtherConfiguration i |
      particlePosition (insertParticle i z.1 z.2) i = c} :=
    (measurePreserving_insertParticle i).measurable hs
  rw [Measure.prod_apply_symm hsp]
  simp only [particlePosition_insertParticle, Set.preimage_ofPred_eq, Set.ofPred_eq_eq_singleton,
    measure_singleton, lintegral_zero]

/-- Distinct electrons coincide on a null set, without any state assumptions. -/
theorem volume_particlePosition_eq_particlePosition {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    volume {x : Configuration N | particlePosition x i = particlePosition x j} = 0 := by
  have hs := measurableSet_eq_fun (measurable_particlePosition i)
    (measurable_particlePosition j)
  rw [← (measurePreserving_insertParticle i).measure_preimage hs.nullMeasurableSet]
  change (volume.prod volume) {z : Position × OtherConfiguration i |
    particlePosition (insertParticle i z.1 z.2) i =
      particlePosition (insertParticle i z.1 z.2) j} = 0
  have hsp : MeasurableSet {z : Position × OtherConfiguration i |
      particlePosition (insertParticle i z.1 z.2) i =
        particlePosition (insertParticle i z.1 z.2) j} :=
    (measurePreserving_insertParticle i).measurable hs
  rw [Measure.prod_apply_symm hsp]
  simp only [particlePosition_insertParticle,
    particlePosition_insertParticle_other i j (Ne.symm hij), Set.preimage_ofPred_eq, Set.ofPred_eq_eq_singleton,
    measure_singleton, lintegral_zero]

/-- Almost every configuration avoids a fixed pole in any chosen coordinate. -/
theorem ae_particlePosition_ne {N : ℕ} (i : Fin N) (c : Position) :
    ∀ᵐ x : Configuration N, particlePosition x i ≠ c := by
  simpa only [ae_iff, not_not] using volume_particlePosition_eq i c

/-- Almost every configuration has distinct selected electron positions. -/
theorem ae_particlePosition_ne_particlePosition {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    ∀ᵐ x : Configuration N, particlePosition x i ≠ particlePosition x j := by
  simpa only [ae_iff, not_not] using volume_particlePosition_eq_particlePosition i j hij

/-- All finitely many electron-nucleus and electron-electron collisions are avoided a.e. -/
theorem ae_collision_free {N M : ℕ} (R : Fin M → Position) :
    ∀ᵐ x : Configuration N,
      (∀ i k, particlePosition x i ≠ R k) ∧
      (∀ i j, i ≠ j → particlePosition x i ≠ particlePosition x j) := by
  have hn : ∀ᵐ x : Configuration N, ∀ i k, particlePosition x i ≠ R k := by
    simp only [ae_all_iff]
    exact fun i k => ae_particlePosition_ne i (R k)
  have he : ∀ᵐ x : Configuration N,
      ∀ i j, i ≠ j → particlePosition x i ≠ particlePosition x j := by
    simp only [ae_all_iff]
    exact fun i j hij => ae_particlePosition_ne_particlePosition i j hij
  exact hn.and he

end LiebThirring.Sobolev

end
