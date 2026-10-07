/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import LiebThirring.TFQuantum.SlaterTensorReindex
public import LiebThirring.Variational.SpectatorReindex
/-! # Appending a spatial-spin orbital to an arbitrary L² state

The tensor append operation uses genuine one-particle insertion and an explicit
ordering of the spectator configuration. It commutes with full Fourier
transformation and has the actual product amplitude almost everywhere.
direct proof particle-coordinate tensor algebra.
-/

public section
open MeasureTheory WithLp
open scoped FourierTransform
namespace LiebThirring

@[expose] noncomputable def orbitalTensorAppend {N q : ℕ}
    (f : State 1 q) (v : State N q) : State (N+1) q :=
  oneParticleInsertion (Fin.last N) (orbitalSpatialStateEquiv q f)
    ((Variational.residualStateReindex (Fin.last N)
      (finSuccAboveEquiv (Fin.last N))).symm v)

theorem fourier_orbitalTensorAppend {N q : ℕ} (f : State 1 q) (v : State N q) :
    𝓕 (orbitalTensorAppend f v) = orbitalTensorAppend (𝓕 f) (𝓕 v) := by
  simp only [orbitalTensorAppend, fourier_oneParticleInsertion,
    fourier_orbitalSpatialStateEquiv, fourier_residualStateReindex_symm]

theorem particleTensorFunction_apply {N q : ℕ} (i : Fin N)
    (f : Position → EuclideanSpace ℂ (Fin q))
    (v : OtherConfiguration i → EuclideanSpace ℂ (OtherSpinLabels i q))
    (X : Configuration N) (s : SpinLabels N q) :
    particleTensorFunction i f v X s =
      f (((insertionMeasurableEquiv i).symm X).1) (s i) *
        v (((insertionMeasurableEquiv i).symm X).2) (fun j => s j.val) := by
  have hx : insertParticle i (((insertionMeasurableEquiv i).symm X).1)
      (((insertionMeasurableEquiv i).symm X).2) = X := by
    rw [← insertionMeasurableEquiv_apply, MeasurableEquiv.apply_symm_apply]
  have hs : insertSpin i (s i) (fun j => s j.val) = s :=
    (spinInsertionEquiv i).apply_symm_apply s
  have h := particleTensorFunction_insert i f v
    (((insertionMeasurableEquiv i).symm X).1)
    (((insertionMeasurableEquiv i).symm X).2) (s i) (fun j => s j.val)
  rw [hx, hs] at h
  exact h

theorem orbitalTensorAppend_apply_ae {N q : ℕ} (f : State 1 q) (v : State N q) :
    ∀ᵐ X : Configuration (N+1), ∀ s : SpinLabels (N+1) q,
      orbitalTensorAppend f v X s =
        orbitalValue f (particlePosition X (Fin.last N)) (s (Fin.last N)) *
          v (Variational.residualProjection (Fin.last N)
            (finSuccAboveEquiv (Fin.last N)) X) (fun j => s j.castSucc) := by
  let i := Fin.last N
  let e := finSuccAboveEquiv i
  have hm := (MeasurePreserving.symm (insertionMeasurableEquiv i)
    (measurePreserving_insertion i)).quasiMeasurePreserving
  rw [Measure.volume_eq_prod] at hm
  have hf := (Measure.quasiMeasurePreserving_fst.comp hm).ae
    (orbitalSpatialStateEquiv_ae f)
  have hv := (Measure.quasiMeasurePreserving_snd.comp hm).ae
    (residualStateReindex_symm_ae i e v)
  filter_upwards [oneParticleInsertion_coe_ae i (orbitalSpatialStateEquiv q f)
    ((Variational.residualStateReindex i e).symm v), hf, hv] with X hX hfX hvX
  intro s
  change oneParticleInsertion i (orbitalSpatialStateEquiv q f)
    ((Variational.residualStateReindex i e).symm v) X s = _
  simp only [Function.comp_apply] at hfX hvX
  rw [hX, particleTensorFunction_apply, hfX, hvX]
  rw [Variational.insertionMeasurableEquiv_symm_fst]
  simp only [e, i, finSuccAboveEquiv_apply, Fin.succAbove_last,
    Variational.residualProjection]

end LiebThirring
end
