/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.DirichletKineticConvergence
public import LiebThirring.TFUpper.DirichletKineticState
public import LiebThirring.TFUpper.SpatialKinetic
public import LiebThirring.TFCubes.DirichletClosure

/-!
# Closed weak-gradient graph for a Dirichlet cube orbital

Compact sine-product Schwartz functions converge simultaneously with each
coordinate derivative. Closedness of the weak-derivative graph then
places the literal zero-extended cube mode in the global Sobolev graph.
explicit zero-extension construction.
-/

public section

open MeasureTheory Filter WithLp LineDeriv
open scoped Topology SchwartzMap
open LiebThirring.Sobolev

namespace LiebThirring.TFUpper

theorem spatialSpinSchwartzLift_lineDeriv {q : ℕ}
    (g : 𝓢(Position, EuclideanSpace ℂ (Fin q))) (a : Fin 3) :
    spatialSpinSchwartzLift (lineDerivOp (positionCoordinateVector a) g) =
      lineDerivOp (Sobolev.coordinateVector ((0 : Fin 1), a))
        (spatialSpinSchwartzLift g) := by
  ext X
  have hv : particlePosition (Sobolev.coordinateVector ((0 : Fin 1), a)) 0 =
      positionCoordinateVector a := by
    rw [Sobolev.coordinateVector, EuclideanSpace.basisFun_apply,
      positionCoordinateVector]
    exact particlePosition_single_one a
  have heval (g' : 𝓢(Position, EuclideanSpace ℂ (Fin q))) (Y : Configuration 1) :
      spatialSpinSchwartzLift g' Y = oneParticleSpinIsometry q (g' (particlePosition Y 0)) := rfl
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    fderiv_spatialSpinSchwartzLift, hv,
    heval]

theorem hasWeakDerivative_spatialSpinSchwartzState {q : ℕ}
    (g : 𝓢(Position, EuclideanSpace ℂ (Fin q))) (a : Fin 3) :
    HasWeakDerivative ((0 : Fin 1), a) (spatialSpinSchwartzState g)
      (spatialSpinSchwartzState (lineDerivOp (positionCoordinateVector a) g)) := by
  rw [spatialSpinSchwartzState_eq_lift_toLp,
    spatialSpinSchwartzState_eq_lift_toLp,
    spatialSpinSchwartzLift_lineDeriv]
  rw [← TFCubes.schwartzCoordinateDerivativeL2_eq]
  exact hasWeakDerivative_schwartzCoordinateDerivativeL2 _ _

theorem dirichletCubeApproxDerivative_toLp_eq {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (a : Fin 3) (k : ℕ) :
    (lineDerivOp (positionCoordinateVector a)
      (dirichletCubeApproxSchwartz ℓ b p k)).toLp 2 volume =
      (memLp_dirichletCubeApproxDerivativeValue_global ℓ b p a k).toLp
        (dirichletCubeApproxDerivativeValue ℓ b p a k) := by
  apply Lp.ext
  filter_upwards [(lineDerivOp (positionCoordinateVector a)
      (dirichletCubeApproxSchwartz ℓ b p k)).coeFn_toLp 2 volume,
    (memLp_dirichletCubeApproxDerivativeValue_global ℓ b p a k).coeFn_toLp]
      with x hx hy
  rw [hx, hy]
  rfl

theorem hasWeakDerivative_dirichletCubeOrbital {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (a : Fin 3) :
    HasWeakDerivative ((0 : Fin 1), a) (dirichletCubeOrbital ℓ b p)
      (spatialSpinToState q (dirichletCubeDerivativeSpatialL2 ℓ b p a)) := by
  apply HasWeakDerivative.closed_of_tendsto
    (uSeq := fun k => spatialSpinSchwartzState (dirichletCubeApproxSchwartz ℓ b p k))
    (gSeq := fun k => spatialSpinSchwartzState
      (lineDerivOp (positionCoordinateVector a) (dirichletCubeApproxSchwartz ℓ b p k)))
  · exact fun k => hasWeakDerivative_spatialSpinSchwartzState _ a
  · change Tendsto
      (fun k => spatialSpinToState q
        ((dirichletCubeApproxSchwartz ℓ b p k).toLp 2 volume)) atTop
      (𝓝 (spatialSpinToState q (dirichletCubeSpatialL2 ℓ b p)))
    exact (spatialSpinToState q).continuous.tendsto _ |>.comp
      (tendsto_dirichletCubeApproxSchwartz_toLp ℓ b p)
  · change Tendsto
      (fun k => spatialSpinToState q
        ((lineDerivOp (positionCoordinateVector a)
          (dirichletCubeApproxSchwartz ℓ b p k)).toLp 2 volume)) atTop
      (𝓝 (spatialSpinToState q (dirichletCubeDerivativeSpatialL2 ℓ b p a)))
    simp_rw [dirichletCubeApproxDerivative_toLp_eq]
    exact (spatialSpinToState q).continuous.tendsto _ |>.comp
      (tendsto_dirichletCubeApproxDerivativeSpatialL2 ℓ b p a)

end LiebThirring.TFUpper

end
