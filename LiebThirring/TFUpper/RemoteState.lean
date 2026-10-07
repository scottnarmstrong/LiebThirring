/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.RemoteOrbitals
public import LiebThirring.TFQuantum.SlaterProduct

/-! # Transport of remote orbitals to one-particle states

Direct proof construction; source
context Lieb–Simon (1977) III.5, (74)--(78), pp. 72--73.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal SchwartzMap

namespace LiebThirring.TFUpper

/-- The literal equivalence between one spin label and a one-particle spin configuration. -/
@[expose] def oneParticleSpinEquiv (q : ℕ) : Fin q ≃ SpinLabels 1 q where
  toFun := oneParticleSpinLabel
  invFun := fun s => s 0
  left_inv := fun _ => rfl
  right_inv := fun s => by
    funext i
    exact congrArg s (Subsingleton.elim 0 i)

/-- Reindex a spatial spin vector as a one-particle spin amplitude. -/
@[expose] noncomputable def oneParticleSpinIsometry (q : ℕ) :
    EuclideanSpace ℂ (Fin q) ≃ₗᵢ[ℂ] SpinAmplitudes 1 q :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (oneParticleSpinEquiv q)

/-- Pointwise spin reindexing acts isometrically on spatial L2. -/
@[expose] noncomputable def spatialSpinLpIsometry (q : ℕ) :
    Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position) →ₗᵢ[ℂ]
      Lp (SpinAmplitudes 1 q) 2 (volume : Measure Position) where
  toFun f := (oneParticleSpinIsometry q).isometry.lipschitzWith.compLp
    (map_zero (oneParticleSpinIsometry q)) f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(oneParticleSpinIsometry q).isometry.lipschitzWith.coeFn_compLp
        (map_zero (oneParticleSpinIsometry q)) (f + g),
      (oneParticleSpinIsometry q).isometry.lipschitzWith.coeFn_compLp
        (map_zero (oneParticleSpinIsometry q)) f,
      (oneParticleSpinIsometry q).isometry.lipschitzWith.coeFn_compLp
        (map_zero (oneParticleSpinIsometry q)) g,
      Lp.coeFn_add f g,
      Lp.coeFn_add
        ((oneParticleSpinIsometry q).isometry.lipschitzWith.compLp
          (map_zero (oneParticleSpinIsometry q)) f)
        ((oneParticleSpinIsometry q).isometry.lipschitzWith.compLp
          (map_zero (oneParticleSpinIsometry q)) g)] with x hfg hf hg hadd hout
    simp only [Function.comp_apply] at hfg hf hg
    rw [hfg, hadd, hout]
    simp only [Pi.add_apply]
    rw [hf, hg, map_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(oneParticleSpinIsometry q).isometry.lipschitzWith.coeFn_compLp
        (map_zero (oneParticleSpinIsometry q)) (c • f),
      (oneParticleSpinIsometry q).isometry.lipschitzWith.coeFn_compLp
        (map_zero (oneParticleSpinIsometry q)) f,
      Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((oneParticleSpinIsometry q).isometry.lipschitzWith.compLp
        (map_zero (oneParticleSpinIsometry q)) f)] with
        x hcf hf hin hout
    simp only [Function.comp_apply] at hcf hf
    rw [hcf, hin]
    simp only [RingHom.id_apply]
    rw [hout]
    simp only [Pi.smul_apply]
    rw [map_smul, hf]
  norm_map' f := by
    let U := oneParticleSpinIsometry q
    let g := U.isometry.lipschitzWith.compLp (map_zero U) f
    have hleft : ‖g‖ ≤ ‖f‖ := by
      have hb := U.isometry.lipschitzWith.norm_compLp_le (map_zero U) f
      dsimp only [g]
      convert hb using 1
      norm_num
    have hinv : U.symm.isometry.lipschitzWith.compLp (map_zero U.symm) g = f := by
      apply Lp.ext
      filter_upwards [U.symm.isometry.lipschitzWith.coeFn_compLp (map_zero U.symm) g,
        U.isometry.lipschitzWith.coeFn_compLp (map_zero U) f] with x hx hfx
      simp only [Function.comp_apply] at hx hfx
      rw [hx, hfx]
      exact U.symm_apply_apply (f x)
    have hright : ‖f‖ ≤ ‖g‖ := by
      rw [← hinv]
      have hb := U.symm.isometry.lipschitzWith.norm_compLp_le (map_zero U.symm) g
      convert hb using 1
      norm_num
    exact le_antisymm hleft hright

/-- Transport spatial L2 to the one-particle configuration carrier. -/
@[expose] noncomputable def spatialSpinToState (q : ℕ) :
    Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position) →ₗᵢ[ℂ] State 1 q :=
  (Lp.compMeasurePreservingₗᵢ ℂ oneParticleConfigurationEquiv.symm
      oneParticleConfigurationEquiv.symm.measurePreserving).comp
    (spatialSpinLpIsometry q)

/-- A spatial-spin Schwartz orbital as a one-particle state. -/
@[expose] noncomputable def spatialSpinSchwartzState {q : ℕ}
    (g : 𝓢(Position, EuclideanSpace ℂ (Fin q))) : State 1 q :=
  spatialSpinToState q (g.toLp 2 (volume : Measure Position))

@[simp] theorem norm_spatialSpinSchwartzState {q : ℕ}
    (g : 𝓢(Position, EuclideanSpace ℂ (Fin q))) :
    ‖spatialSpinSchwartzState g‖ = ‖g.toLp 2 (volume : Measure Position)‖ :=
  (spatialSpinToState q).norm_map _

/-- The state transport preserves inner products. -/
theorem inner_spatialSpinSchwartzState {q : ℕ}
    (g h : 𝓢(Position, EuclideanSpace ℂ (Fin q))) :
    inner ℂ (spatialSpinSchwartzState g) (spatialSpinSchwartzState h) =
      inner ℂ (g.toLp 2 (volume : Measure Position))
        (h.toLp 2 (volume : Measure Position)) :=
  (spatialSpinToState q).inner_map_map _ _

/-- An almost-everywhere representative of the transported state. -/
theorem spatialSpinSchwartzState_ae {q : ℕ}
    (g : 𝓢(Position, EuclideanSpace ℂ (Fin q))) :
    ∀ᵐ X : Configuration 1 ∂volume,
      spatialSpinSchwartzState g X =
        oneParticleSpinIsometry q (g (particlePosition X 0)) := by
  let f := g.toLp 2 (volume : Measure Position)
  let h := spatialSpinLpIsometry q f
  have houter := Lp.coeFn_compMeasurePreserving h
    oneParticleConfigurationEquiv.symm.measurePreserving
  have hspin := (oneParticleSpinIsometry q).isometry.lipschitzWith.coeFn_compLp
    (map_zero (oneParticleSpinIsometry q)) f
  have hg := g.coeFn_toLp 2 (volume : Measure Position)
  have hspin' := oneParticleConfigurationEquiv.symm.measurePreserving.quasiMeasurePreserving.ae
    (hspin.and hg)
  filter_upwards [houter, hspin'] with X hX hs
  change (Lp.compMeasurePreserving oneParticleConfigurationEquiv.symm
    oneParticleConfigurationEquiv.symm.measurePreserving h) X = _
  rw [hX]
  simp only [Function.comp_apply] at hs ⊢
  rw [show h (oneParticleConfigurationEquiv.symm X) =
      oneParticleSpinIsometry q (f (oneParticleConfigurationEquiv.symm X)) from hs.1,
    show f (oneParticleConfigurationEquiv.symm X) = g (oneParticleConfigurationEquiv.symm X)
      from hs.2]
  congr 2

/-- The orbital value agrees almost everywhere with the original spatial-spin orbital. -/
theorem orbitalValue_spatialSpinSchwartzState_ae {q : ℕ}
    (g : 𝓢(Position, EuclideanSpace ℂ (Fin q))) (t : Fin q) :
    ∀ᵐ x : Position ∂volume, orbitalValue (spatialSpinSchwartzState g) x t = g x t := by
  have h := oneParticleConfigurationEquiv.measurePreserving.quasiMeasurePreserving.ae
    (spatialSpinSchwartzState_ae g)
  filter_upwards [h] with x hx
  have hv := congrArg (fun v : SpinAmplitudes 1 q => v (oneParticleSpinLabel t)) hx
  have heval : oneParticleConfigurationEquiv x = oneParticleConfiguration x := rfl
  have hspin_eval (v : EuclideanSpace ℂ (Fin q)) :
      oneParticleSpinIsometry q v (oneParticleSpinLabel t) = v t := rfl
  simpa only [orbitalValue, heval, particlePosition_oneParticleConfiguration,
    hspin_eval] using hv

end LiebThirring.TFUpper

end
