/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.WeightedIntegration

/-!
# Removing a point from integration by parts

In three dimensions, almost every coordinate line avoids the origin.
Fubini therefore gives integration by parts for coefficients smooth away
from the origin, provided the three products are integrable. In particular,
no boundary measure at the origin is introduced.
-/

public section
open MeasureTheory WithLp
open scoped Topology
namespace LiebThirring

/-- Split one coordinate from Euclidean three-space, with the scalar last. -/
@[expose] noncomputable def weightedCoordinateEquiv (i : Fin 3) :
    Position ≃ᵐ ((Fin 2 → ℝ) × ℝ) :=
  ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i)).trans
    MeasurableEquiv.prodComm

theorem measurePreserving_weightedCoordinateEquiv (i : Fin 3) :
    MeasurePreserving (weightedCoordinateEquiv i) volume volume :=
  ((PiLp.volume_preserving_ofLp (Fin 3)).trans
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) i)).trans Measure.measurePreserving_swap

/-- Insert the scalar coordinate along a fixed coordinate line. -/
@[expose] noncomputable def weightedCoordinateLine (i : Fin 3) (y : Fin 2 → ℝ) (t : ℝ) :
    Position := toLp 2 (i.insertNth t y)

theorem weightedCoordinateLine_affine (i : Fin 3) (y : Fin 2 → ℝ) (t : ℝ) :
    weightedCoordinateLine i y t = weightedCoordinateLine i y 0 +
      t • EuclideanSpace.basisFun (Fin 3) ℝ i := by
  apply PiLp.ext
  intro j
  by_cases hj : j = i
  · subst j
    simp [weightedCoordinateLine, EuclideanSpace.basisFun_apply]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [weightedCoordinateLine, EuclideanSpace.basisFun_apply, i.succAbove_ne k]

theorem hasDerivAt_weightedCoordinateLine (i : Fin 3) (y : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (weightedCoordinateLine i y) (EuclideanSpace.basisFun (Fin 3) ℝ i) t := by
  have hh := (hasDerivAt_const t (weightedCoordinateLine i y 0)).add
      ((hasDerivAt_id t).smul_const (EuclideanSpace.basisFun (Fin 3) ℝ i))
  simp only [zero_add, one_smul] at hh
  convert hh using 1
  funext s
  exact weightedCoordinateLine_affine i y s

theorem weightedCoordinateLine_ne_zero (i : Fin 3) {y : Fin 2 → ℝ} (hy : y ≠ 0) (t : ℝ) :
    weightedCoordinateLine i y t ≠ 0 := by
  intro h
  apply hy
  funext j
  have hh := congrArg (fun x : Position => x (i.succAbove j)) h
  simpa only [weightedCoordinateLine, ofLp_toLp, Fin.insertNth_apply_succAbove,
    PiLp.zero_apply, Pi.zero_apply] using hh

/-- Integration by parts across an isolated point, proved by a.e. coordinate
lines. Its integrability hypotheses make this a generic analytic helper. -/
theorem integral_punctured_mul_fderiv_of_integrable {a g : Position → ℝ}
    (ha : ∀ x : Position, x ≠ 0 → DifferentiableAt ℝ a x)
    (hg : Differentiable ℝ g) (i : Fin 3)
    (hi₁ : Integrable (fun x => fderiv ℝ a x (EuclideanSpace.basisFun (Fin 3) ℝ i) * g x))
    (hi₂ : Integrable (fun x => a x * fderiv ℝ g x (EuclideanSpace.basisFun (Fin 3) ℝ i)))
    (hi₀ : Integrable (fun x => a x * g x)) :
    (∫ x, a x * fderiv ℝ g x (EuclideanSpace.basisFun (Fin 3) ℝ i)) =
      -∫ x, fderiv ℝ a x (EuclideanSpace.basisFun (Fin 3) ℝ i) * g x := by
  let e := (weightedCoordinateEquiv i).symm
  have he : MeasurePreserving e volume volume :=
    (measurePreserving_weightedCoordinateEquiv i).symm
  have h₁ := (he.integrable_comp_emb e.measurableEmbedding).mpr hi₁
  have h₂ := (he.integrable_comp_emb e.measurableEmbedding).mpr hi₂
  have h₀ := (he.integrable_comp_emb e.measurableEmbedding).mpr hi₀
  rw [← he.integral_comp' (fun x => a x * fderiv ℝ g x (EuclideanSpace.basisFun (Fin 3) ℝ i)),
    ← he.integral_comp' (fun x => fderiv ℝ a x (EuclideanSpace.basisFun (Fin 3) ℝ i) * g x)]
  simp only [Function.comp_def] at h₁ h₂ h₀
  change (∫ x, a (e x) * fderiv ℝ g (e x) (EuclideanSpace.basisFun (Fin 3) ℝ i)
    ∂(volume.prod volume)) = -∫ x, fderiv ℝ a (e x) (EuclideanSpace.basisFun (Fin 3) ℝ i) *
    g (e x) ∂(volume.prod volume)
  rw [integral_prod _ h₂, integral_prod _ h₁, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [h₁.prod_right_ae, h₂.prod_right_ae, h₀.prod_right_ae,
    show ∀ᵐ y : Fin 2 → ℝ, y ≠ 0 by rw [ae_iff]; simp] with y hy₁ hy₂ hy₀ hy
  apply integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.mul ℝ ℝ)
  · intro t _
    exact ((ha (weightedCoordinateLine i y t) (weightedCoordinateLine_ne_zero i hy t)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_weightedCoordinateLine i y t))
  · intro t _
    exact ((hg (weightedCoordinateLine i y t)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_weightedCoordinateLine i y t))
  · exact hy₂
  · exact hy₁
  · exact hy₀

end LiebThirring
end
