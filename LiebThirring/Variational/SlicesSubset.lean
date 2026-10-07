/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.Regrouping
public import LiebThirring.Kinetic.CurryingDensity

/-!
# Arbitrary particle-block L² slicing with finite-spin regrouping

Particle slicing uses an explicit ordering `e: Fin k ≃ S`. The complementary spins remain
an independent finite sum. The construction is a linear isometric equivalence
on the literal configuration and state carriers, including `k = 0`.
-/

public section
open MeasureTheory WithLp
open scoped ENNReal NNReal Classical

namespace LiebThirring.Variational

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

/-- Spatial coordinates of the complementary particle block. -/
abbrev SubsetSpectatorConfiguration {N : ℕ} (S : Set (Fin N)) :=
  EuclideanSpace ℝ ((Sᶜ : Set (Fin N)) × Fin 3)

/-- Spins of the complementary particle block. -/
abbrev SubsetSpectatorSpins {N : ℕ} (S : Set (Fin N)) (q : ℕ) :=
  (Sᶜ : Set (Fin N)) → Fin q

/-- Insert the ordered selected block and its complementary block. -/
@[expose] noncomputable def subsetOrderedInsertion {N k : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) :
    (SubsetSpectatorConfiguration S × Configuration k) ≃ᵐ Configuration N := by
  classical
  exact (MeasurableEquiv.prodComm (α := SubsetSpectatorConfiguration S)
    (β := Configuration k)).trans
      (((Sobolev.configurationReindexMeasurableEquiv e).prodCongr
        (MeasurableEquiv.refl _)).trans (Sobolev.subsetInsertionMeasurableEquiv S))

/-- The particle block split has unit Jacobian. -/
theorem measurePreserving_subsetOrderedInsertion {N k : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) : MeasurePreserving (subsetOrderedInsertion S e) volume volume := by
  classical
  exact Measure.measurePreserving_swap.trans
    (((Sobolev.measurePreserving_configurationReindex e).prod (MeasurePreserving.id _)).trans
      (Sobolev.measurePreserving_subsetInsertion S))

/-- Insert a selected-spin assignment and the complementary spin assignment. -/
@[expose] noncomputable def subsetOrderedSpinEquiv {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) :
    (SubsetSpectatorSpins S q × SpinLabels k q) ≃ SpinLabels N q := by
  classical
  exact (Equiv.prodComm _ _).trans
    (((Equiv.piCongrLeft (fun _ : S => Fin q) e).prodCongr (Equiv.refl _)).trans
      (Sobolev.subsetSpinEquiv S))

/-- Regroup all spin amplitudes, retaining one summand for each complementary spin. -/
@[expose] noncomputable def subsetSpinCurrying {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) : SpinAmplitudes N q ≃ₗᵢ[ℂ]
      PiLp 2 (fun _ : SubsetSpectatorSpins S q => SpinAmplitudes k q) := by
  classical
  exact (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (subsetOrderedSpinEquiv S e).symm).trans
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (Equiv.sigmaEquivProd (SubsetSpectatorSpins S q) (SpinLabels k q)).symm).trans
      (LinearIsometryEquiv.piLpCurry ℂ 2
        (fun (_ : SubsetSpectatorSpins S q) (_ : SpinLabels k q) => ℂ)))

/-- The full block-currying isometry, using Lebesgue measure and finite counting-spin normalization. -/
@[expose] noncomputable def subsetParticleField {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) : State N q ≃ₗᵢ[ℂ]
      Lp (PiLp 2 (fun _ : SubsetSpectatorSpins S q => State k q)) 2
        (volume : Measure (SubsetSpectatorConfiguration S)) := by
  classical
  let A := l2PullbackEquiv (E := SpinAmplitudes N q)
    (subsetOrderedInsertion S e) (measurePreserving_subsetOrderedInsertion S e)
  let B := l2TargetEquiv (volume : Measure (SubsetSpectatorConfiguration S × Configuration k))
    (subsetSpinCurrying (q := q) S e)
  let C := l2CurryLinearIsometryEquiv (μ := (volume : Measure (SubsetSpectatorConfiguration S)))
    (ν := (volume : Measure (Configuration k)))
    (E := PiLp 2 (fun _ : SubsetSpectatorSpins S q => SpinAmplitudes k q))
  let D := l2TargetEquiv (volume : Measure (SubsetSpectatorConfiguration S))
    (finiteLpPiLpEquiv (volume : Measure (Configuration k))
      (fun _ : SubsetSpectatorSpins S q => SpinAmplitudes k q))
  exact ((A.trans B).trans C).trans D

/-- An ordered selected-block state with the complementary positions and spins fixed. -/
@[expose] noncomputable def subsetParticleSlice {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (u : State N q) (y : SubsetSpectatorConfiguration S)
    (α : SubsetSpectatorSpins S q) : State k q := subsetParticleField S e u y α

/-- Block slices agree with the inserted state on one full-measure outer set. -/
theorem subsetParticleSlice_ae {N k q : ℕ} (S : Set (Fin N))
    (e : Fin k ≃ S) (u : State N q) :
    ∀ᵐ y : SubsetSpectatorConfiguration S, ∀ α : SubsetSpectatorSpins S q,
      ∀ᵐ x : Configuration k, ∀ s : SpinLabels k q,
        subsetParticleSlice S e u y α x s =
          u (subsetOrderedInsertion S e (y, x)) (subsetOrderedSpinEquiv S e (α, s)) := by
  classical
  let A := l2PullbackEquiv (E := SpinAmplitudes N q)
    (subsetOrderedInsertion S e) (measurePreserving_subsetOrderedInsertion S e)
  let B := l2TargetEquiv (volume : Measure (SubsetSpectatorConfiguration S × Configuration k))
    (subsetSpinCurrying (q := q) S e)
  let h := B (A u)
  let D := l2TargetEquiv (volume : Measure (SubsetSpectatorConfiguration S))
    (finiteLpPiLpEquiv (volume : Measure (Configuration k))
      (fun _ : SubsetSpectatorSpins S q => SpinAmplitudes k q))
  have hA := Measure.ae_ae_of_ae_prod (l2PullbackEquiv_ae
    (subsetOrderedInsertion S e) (measurePreserving_subsetOrderedInsertion S e) u)
  have hB := Measure.ae_ae_of_ae_prod (l2TargetEquiv_ae
    (volume : Measure (SubsetSpectatorConfiguration S × Configuration k))
    (subsetSpinCurrying (q := q) S e) (A u))
  change ∀ᵐ y : SubsetSpectatorConfiguration S, ∀ α : SubsetSpectatorSpins S q,
    ∀ᵐ x : Configuration k, ∀ s : SpinLabels k q,
      D (l2Curry h) y α x s = _
  filter_upwards [l2TargetEquiv_ae (volume : Measure (SubsetSpectatorConfiguration S))
    (finiteLpPiLpEquiv (volume : Measure (Configuration k))
      (fun _ : SubsetSpectatorSpins S q => SpinAmplitudes k q)) (l2Curry h),
      l2Curry_ae h, hA, hB] with y hy hc ha hb
  intro α
  rw [hy]
  filter_upwards [finiteLpPiLpEquiv_apply_ae (volume : Measure (Configuration k))
    (fun _ : SubsetSpectatorSpins S q => SpinAmplitudes k q) (l2Curry h y) α,
    hc, ha, hb] with x hx hcx hax hbx
  intro s
  rw [hx, hcx, hbx, hax]
  rfl

end LiebThirring.Variational
end
