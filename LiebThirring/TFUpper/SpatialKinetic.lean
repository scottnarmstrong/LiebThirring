/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.RemoteState
public import LiebThirring.Theorems.KineticEnergySchwartz

/-! # one-particle kinetic energy of spatial-spin Schwartz orbitals

The configuration and spin reindexings preserve the actual Schwartz function,
not just its L² norm. The Fourier kinetic energy then equals the
classical gradient energy. Proof: particle-number correction, using quantum form domain's existing
Schwartz kinetic identity.
-/

public section
open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap
namespace LiebThirring.TFUpper

/-- The spatial-spin Schwartz function on the literal carrier. -/
@[expose] noncomputable def spatialSpinSchwartzLift {q : ℕ}
    (g : 𝓢(Position, EuclideanSpace ℂ (Fin q))) :
    𝓢(Configuration 1, SpinAmplitudes 1 q) :=
  ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    oneParticleConfigurationEquiv.symm.toContinuousLinearEquiv) g).postcompCLM
      (oneParticleSpinIsometry q).toContinuousLinearMap

theorem spatialSpinSchwartzState_eq_lift_toLp {q : ℕ}
    (g : 𝓢(Position, EuclideanSpace ℂ (Fin q))) :
    spatialSpinSchwartzState g = (spatialSpinSchwartzLift g).toLp 2
      (volume : Measure (Configuration 1)) := by
  let U := oneParticleSpinIsometry q
  let e := oneParticleConfigurationEquiv
  let f := g.toLp 2 (volume : Measure Position)
  apply Lp.ext
  have hcomp := Lp.coeFn_compMeasurePreserving (spatialSpinLpIsometry q f)
    e.symm.measurePreserving
  have hf := U.isometry.lipschitzWith.coeFn_compLp (map_zero U) f
  filter_upwards [hcomp, e.symm.measurePreserving.quasiMeasurePreserving.ae hf,
    e.symm.measurePreserving.quasiMeasurePreserving.ae (g.coeFn_toLp 2 volume),
    (spatialSpinSchwartzLift g).coeFn_toLp 2 volume] with X hx hU hg hLift
  rw [hLift]
  exact hx.trans (hU.trans (congrArg U hg))

theorem fderiv_spatialSpinSchwartzLift {q : ℕ}
    (g : 𝓢(Position, EuclideanSpace ℂ (Fin q))) (X v : Configuration 1) :
    fderiv ℝ (fun Y => spatialSpinSchwartzLift g Y) X v =
      oneParticleSpinIsometry q
        (fderiv ℝ (fun y => g y) (particlePosition X 0) (particlePosition v 0)) := by
  let e := oneParticleConfigurationEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let U := (oneParticleSpinIsometry q).toContinuousLinearMap.restrictScalars ℝ
  have hg := ((g.smooth ⊤).differentiable (by simp)).differentiableAt.hasFDerivAt
    (x := e X)
  have h := U.hasFDerivAt.comp X (hg.comp X e.hasFDerivAt)
  change fderiv ℝ (fun Y => U (g (e Y))) X v = _
  exact congrArg (fun f : Configuration 1 →L[ℝ] SpinAmplitudes 1 q => f v) h.fderiv

theorem particlePosition_single_one (a : Fin 3) :
    particlePosition (PiLp.single 2 ((0 : Fin 1), a) (1 : ℝ)) 0 =
      PiLp.single 2 a (1 : ℝ) := by
  ext b
  simp only [particlePosition, PiLp.toLp_apply, PiLp.single_apply,
    Prod.mk.injEq, true_and]

theorem integral_fderiv_spatialSpinSchwartzLift {q : ℕ}
    (g : 𝓢(Position, EuclideanSpace ℂ (Fin q))) (a : Fin 3) :
    (∫ X : Configuration 1, ‖fderiv ℝ (fun Y => spatialSpinSchwartzLift g Y) X
      (PiLp.single 2 ((0 : Fin 1), a) (1 : ℝ))‖ ^ 2) =
      ∫ x : Position, ‖fderiv ℝ (fun y => g y) x (PiLp.single 2 a (1 : ℝ))‖ ^ 2 := by
  simp only [fderiv_spatialSpinSchwartzLift, particlePosition_single_one,
    LinearIsometryEquiv.norm_map]
  exact oneParticleConfigurationEquiv.symm.measurePreserving.integral_comp
    oneParticleConfigurationEquiv.symm.toMeasurableEquiv.measurableEmbedding
      (fun x : Position => ‖fderiv ℝ (fun y => g y) x (PiLp.single 2 a (1 : ℝ))‖ ^ 2)

theorem kineticEnergy_spatialSpinSchwartzState {q : ℕ}
    (g : 𝓢(Position, EuclideanSpace ℂ (Fin q))) :
    kineticEnergy (spatialSpinSchwartzState g) = ENNReal.ofReal
      (∑ a : Fin 3, ∫ x : Position,
        ‖fderiv ℝ (fun y => g y) x (PiLp.single 2 a (1 : ℝ))‖ ^ 2) := by
  rw [spatialSpinSchwartzState_eq_lift_toLp, kineticEnergy_schwartz, Fin.sum_univ_one]
  have hdir (a : Fin 3) :
      (∫⁻ X : Configuration 1,
        (‖fderiv ℝ (fun Y => spatialSpinSchwartzLift g Y) X
          (PiLp.single 2 ((0 : Fin 1), a) (1 : ℝ))‖₊ : ℝ≥0∞) ^ 2) =
        ENNReal.ofReal (∫ x : Position,
          ‖fderiv ℝ (fun y => g y) x (PiLp.single 2 a (1 : ℝ))‖ ^ 2) := by
    have h := Fourier.lintegral_norm_sq_eq_ofReal_integral
      (LineDeriv.lineDerivOp (show Configuration 1 from PiLp.single 2 ((0 : Fin 1), a) (1 : ℝ))
        (spatialSpinSchwartzLift g))
    simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv] at h
    rw [integral_fderiv_spatialSpinSchwartzLift] at h
    exact h
  simp only [hdir]
  exact (ENNReal.ofReal_sum_of_nonneg fun a _ => integral_nonneg fun _ => sq_nonneg _).symm

theorem kineticEnergy_spatialSpinSchwartzState_lt_top {q : ℕ}
    (g : 𝓢(Position, EuclideanSpace ℂ (Fin q))) :
    kineticEnergy (spatialSpinSchwartzState g) < ⊤ := by
  rw [kineticEnergy_spatialSpinSchwartzState]
  exact ENNReal.ofReal_lt_top

theorem kineticEnergy_spatialSpinSchwartzState_toReal {q : ℕ}
    (g : 𝓢(Position, EuclideanSpace ℂ (Fin q))) :
    (kineticEnergy (spatialSpinSchwartzState g)).toReal =
      ∑ a : Fin 3, ∫ x : Position,
        ‖fderiv ℝ (fun y => g y) x (PiLp.single 2 a (1 : ℝ))‖ ^ 2 := by
  rw [kineticEnergy_spatialSpinSchwartzState, ENNReal.toReal_ofReal
    (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)]

end LiebThirring.TFUpper
end
