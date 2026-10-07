/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.WeakMultiplier
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import LiebThirring.Sobolev.RealLipschitzIntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Rademacher

/-!
# Coordinate splitting for Lipschitz integration by parts

This module isolates one real coordinate of configuration space as the first factor of a
measure-preserving product decomposition.  It is the Fubini coordinate system used by the scalar
Lipschitz integration-by-parts argument.
-/

public section

open MeasureTheory WithLp
open scoped ContDiff NNReal

namespace LiebThirring.Sobolev

/-- All configuration coordinates except `a`. -/
abbrev CoordinateComplement {N : ℕ} (a : Fin N × Fin 3) :=
  EuclideanSpace ℝ {j : Fin N × Fin 3 // j ≠ a}

/-- Split an index into the selected singleton coordinate and its complement. -/
@[expose] def coordinateIndexEquiv {N : ℕ} (a : Fin N × Fin 3) :
    (Fin N × Fin 3) ≃ (Unit ⊕ {j : Fin N × Fin 3 // j ≠ a}) where
  toFun j := if h : j = a then Sum.inl () else Sum.inr ⟨j, h⟩
  invFun := Sum.elim (fun _ => a) Subtype.val
  left_inv j := by
    dsimp
    split <;> simp_all
  right_inv j := by
    cases j with
    | inl u => cases u; simp
    | inr j => simp [j.property]

/-- Insert one selected coordinate into its complementary configuration. -/
@[expose] noncomputable def insertCoordinate {N : ℕ} (a : Fin N × Fin 3)
    (t : EuclideanSpace ℝ Unit) (y : CoordinateComplement a) : Configuration N :=
  toLp 2 fun j => if h : j = a then t () else y ⟨j, h⟩

/-- The measurable product equivalence associated with `insertCoordinate`. -/
@[expose] noncomputable def coordinateInsertionMeasurableEquiv {N : ℕ} (a : Fin N × Fin 3) :
    (EuclideanSpace ℝ Unit × CoordinateComplement a) ≃ᵐ Configuration N :=
  ((MeasurableEquiv.toLp 2 (Unit → ℝ)).symm.prodCongr
    (MeasurableEquiv.toLp 2 ({j : Fin N × Fin 3 // j ≠ a} → ℝ)).symm).trans
  ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Unit ⊕ {j : Fin N × Fin 3 // j ≠ a} => ℝ)).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin N × Fin 3 => ℝ)
      (coordinateIndexEquiv a).symm).trans (MeasurableEquiv.toLp 2 _)))

theorem coordinateInsertionMeasurableEquiv_apply {N : ℕ} (a : Fin N × Fin 3)
    (z : EuclideanSpace ℝ Unit × CoordinateComplement a) :
    coordinateInsertionMeasurableEquiv a z = insertCoordinate a z.1 z.2 := by
  ext j
  simp [coordinateInsertionMeasurableEquiv, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
    Equiv.sumPiEquivProdPi, coordinateIndexEquiv, insertCoordinate]
  split <;> rfl

/-- Splitting off one configuration coordinate preserves Lebesgue volume. -/
theorem measurePreserving_coordinateInsertion {N : ℕ} (a : Fin N × Fin 3) :
    MeasurePreserving (coordinateInsertionMeasurableEquiv a) volume volume := by
  exact ((PiLp.volume_preserving_ofLp Unit).prod
    (PiLp.volume_preserving_ofLp {j : Fin N × Fin 3 // j ≠ a})).trans
    ((volume_measurePreserving_sumPiEquivProdPi_symm _).trans
      ((volume_measurePreserving_piCongrLeft _ (coordinateIndexEquiv a).symm).trans
        (PiLp.volume_preserving_toLp (Fin N × Fin 3))))

/-- Identify the one-dimensional Euclidean singleton space with `ℝ`. -/
@[expose] noncomputable def realUnitMeasurableEquiv : ℝ ≃ᵐ EuclideanSpace ℝ Unit :=
  (MeasurableEquiv.piUnique (fun _ : Unit => ℝ)).symm.trans (MeasurableEquiv.toLp 2 _)

theorem realUnitMeasurableEquiv_apply (t : ℝ) :
    realUnitMeasurableEquiv t = t • EuclideanSpace.basisFun Unit ℝ () := by
  ext u
  cases u
  simp [realUnitMeasurableEquiv]

theorem measurePreserving_realUnit :
    MeasurePreserving realUnitMeasurableEquiv volume volume :=
  (volume_preserving_piUnique (fun _ : Unit => ℝ)).symm.trans
    (PiLp.volume_preserving_toLp Unit)

/-- Split configuration space into the selected real coordinate and its complement. -/
@[expose] noncomputable def realCoordinateInsertionMeasurableEquiv {N : ℕ}
    (a : Fin N × Fin 3) : (ℝ × CoordinateComplement a) ≃ᵐ Configuration N :=
  (realUnitMeasurableEquiv.prodCongr (MeasurableEquiv.refl _)).trans
    (coordinateInsertionMeasurableEquiv a)

theorem realCoordinateInsertionMeasurableEquiv_apply {N : ℕ} (a : Fin N × Fin 3)
    (z : ℝ × CoordinateComplement a) :
    realCoordinateInsertionMeasurableEquiv a z =
      insertCoordinate a (z.1 • EuclideanSpace.basisFun Unit ℝ ()) z.2 := by
  change coordinateInsertionMeasurableEquiv a (realUnitMeasurableEquiv z.1, z.2) = _
  rw [coordinateInsertionMeasurableEquiv_apply, realUnitMeasurableEquiv_apply]

theorem measurePreserving_realCoordinateInsertion {N : ℕ} (a : Fin N × Fin 3) :
    MeasurePreserving (realCoordinateInsertionMeasurableEquiv a) volume volume :=
  ((measurePreserving_realUnit.prod (MeasurePreserving.id volume))).trans
    (measurePreserving_coordinateInsertion a)

theorem insertCoordinate_add_selected {N : ℕ} (a : Fin N × Fin 3)
    (t : EuclideanSpace ℝ Unit) (y : CoordinateComplement a) (s : ℝ) :
    insertCoordinate a (t + s • EuclideanSpace.basisFun Unit ℝ ()) y =
      insertCoordinate a t y + s • coordinateVector a := by
  ext j
  by_cases h : j = a
  · subst j
    simp [insertCoordinate, coordinateVector]
  · simp [insertCoordinate, coordinateVector, h]

theorem realCoordinateInsertion_add {N : ℕ} (a : Fin N × Fin 3)
    (t s : ℝ) (y : CoordinateComplement a) :
    realCoordinateInsertionMeasurableEquiv a (t + s, y) =
      realCoordinateInsertionMeasurableEquiv a (t, y) + s • coordinateVector a := by
  rw [realCoordinateInsertionMeasurableEquiv_apply,
    realCoordinateInsertionMeasurableEquiv_apply]
  convert insertCoordinate_add_selected a
    (t • EuclideanSpace.basisFun Unit ℝ ()) y s using 1
  ext u
  cases u
  simp [add_smul]

theorem hasDerivAt_realCoordinateInsertion {N : ℕ} (a : Fin N × Fin 3)
    (y : CoordinateComplement a) (t : ℝ) :
    HasDerivAt (fun r => realCoordinateInsertionMeasurableEquiv a (r, y))
      (coordinateVector a) t := by
  have h := (hasDerivAt_const (x := t) (c :=
    realCoordinateInsertionMeasurableEquiv a (0, y))).add
      ((hasDerivAt_id t).smul_const (coordinateVector a))
  convert h using 1
  · funext r
    change realCoordinateInsertionMeasurableEquiv a (r, y) =
      realCoordinateInsertionMeasurableEquiv a (0, y) + r • coordinateVector a
    simpa using realCoordinateInsertion_add a 0 r y
  · simp

theorem contDiff_realCoordinateInsertion {N : ℕ} (a : Fin N × Fin 3)
    (y : CoordinateComplement a) :
    ContDiff ℝ ∞ (fun t : ℝ => realCoordinateInsertionMeasurableEquiv a (t, y)) := by
  have heq : (fun t : ℝ => realCoordinateInsertionMeasurableEquiv a (t, y)) =
      fun t => realCoordinateInsertionMeasurableEquiv a (0, y) + t • coordinateVector a := by
    funext t
    simpa using realCoordinateInsertion_add a 0 t y
  rw [heq]
  fun_prop

theorem hasDerivAt_coordinateSlice {N : ℕ} (a : Fin N × Fin 3)
    (b : Configuration N → ℝ) (y : CoordinateComplement a) (t : ℝ)
    (hb : DifferentiableAt ℝ b (realCoordinateInsertionMeasurableEquiv a (t, y))) :
    HasDerivAt (fun r => b (realCoordinateInsertionMeasurableEquiv a (r, y)))
      (fderiv ℝ b (realCoordinateInsertionMeasurableEquiv a (t, y)) (coordinateVector a)) t := by
  change HasDerivAt (b ∘ fun r => realCoordinateInsertionMeasurableEquiv a (r, y)) _ t
  exact hb.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_realCoordinateInsertion a y t)

theorem lipschitzWith_one_realCoordinateInsertion {N : ℕ} (a : Fin N × Fin 3)
    (y : CoordinateComplement a) :
    LipschitzWith 1 (fun t : ℝ => realCoordinateInsertionMeasurableEquiv a (t, y)) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  have hs := realCoordinateInsertion_add a t (s - t) y
  have hts : t + (s - t) = s := by ring
  rw [hts] at hs
  rw [hs, dist_eq_norm, add_sub_cancel_left, norm_smul]
  simp [coordinateVector, Real.dist_eq]

theorem isometry_realCoordinateInsertion {N : ℕ} (a : Fin N × Fin 3)
    (y : CoordinateComplement a) :
    Isometry (fun t : ℝ => realCoordinateInsertionMeasurableEquiv a (t, y)) := by
  refine Isometry.of_dist_eq fun s t => ?_
  have hs := realCoordinateInsertion_add a t (s - t) y
  have hts : t + (s - t) = s := by ring
  rw [hts] at hs
  rw [hs, dist_eq_norm, add_sub_cancel_left, norm_smul]
  simp [coordinateVector, Real.dist_eq]

theorem hasCompactSupport_coordinateSlice {N : ℕ} (a : Fin N × Fin 3)
    (φ : Configuration N → ℝ) (hφc : HasCompactSupport φ) (y : CoordinateComplement a) :
    HasCompactSupport (fun t : ℝ => φ (realCoordinateInsertionMeasurableEquiv a (t, y))) := by
  let f : ℝ → Configuration N := fun t => realCoordinateInsertionMeasurableEquiv a (t, y)
  apply HasCompactSupport.intro
    ((isometry_realCoordinateInsertion a y).isClosedEmbedding.isCompact_preimage hφc)
  intro t ht
  exact image_eq_zero_of_notMem_tsupport ht

theorem LipschitzWith.coordinateSlice {N : ℕ} {b : Configuration N → ℝ} {C : ℝ≥0}
    (hb : LipschitzWith C b) (a : Fin N × Fin 3) (y : CoordinateComplement a) :
    LipschitzWith C (fun t : ℝ => b (realCoordinateInsertionMeasurableEquiv a (t, y))) := by
  change LipschitzWith C (b ∘ fun t : ℝ => realCoordinateInsertionMeasurableEquiv a (t, y))
  simpa only [mul_one] using hb.comp (lipschitzWith_one_realCoordinateInsertion a y)

/-- On almost every coordinate line and almost every point of that line, the derivative of a
Lipschitz scalar slice is its ambient directional Fréchet derivative. -/
theorem ae_ae_hasDerivAt_coordinateSlice {N : ℕ} (a : Fin N × Fin 3)
    (b : Configuration N → ℝ) (C : ℝ≥0) (hb : LipschitzWith C b) :
    ∀ᵐ y : CoordinateComplement a, ∀ᵐ t : ℝ,
      HasDerivAt (fun r => b (realCoordinateInsertionMeasurableEquiv a (r, y)))
        (fderiv ℝ b (realCoordinateInsertionMeasurableEquiv a (t, y))
          (coordinateVector a)) t := by
  have hprod : ∀ᵐ z : ℝ × CoordinateComplement a,
      DifferentiableAt ℝ b (realCoordinateInsertionMeasurableEquiv a z) :=
    (measurePreserving_realCoordinateInsertion a).quasiMeasurePreserving.ae
      hb.ae_differentiableAt
  have hmeas : MeasurableSet {z : ℝ × CoordinateComplement a |
      DifferentiableAt ℝ b (realCoordinateInsertionMeasurableEquiv a z)} :=
    (measurableSet_of_differentiableAt ℝ b).preimage
      (realCoordinateInsertionMeasurableEquiv a).measurable
  have ht_y := Measure.ae_ae_of_ae_prod hprod
  have hy_t := (Measure.ae_ae_comm hmeas).mp ht_y
  filter_upwards [hy_t] with y hy
  filter_upwards [hy] with t ht
  exact hasDerivAt_coordinateSlice a b y t ht

/-- Scalar integration by parts for a Lipschitz function on configuration space. -/
theorem integral_mul_coordinateDerivative_eq_neg_of_lipschitz {N : ℕ}
    (a : Fin N × Fin 3) (b φ : Configuration N → ℝ) (C : ℝ≥0)
    (hb : LipschitzWith C b) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, b x * fderiv ℝ φ x (coordinateVector a)) =
      -(∫ x, lipschitzDirectionalDerivative b a x * φ x) := by
  let e := realCoordinateInsertionMeasurableEquiv a
  let db : Configuration N → ℝ := lipschitzDirectionalDerivative b a
  let dφ : Configuration N → ℝ := fun x => fderiv ℝ φ x (coordinateVector a)
  have hdφc : Continuous dφ :=
    (hφ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hdφsupp : HasCompactSupport dφ := hφc.fderiv_apply ℝ (coordinateVector a)
  have hleft : Integrable (fun x => b x * dφ x) :=
    (hb.continuous.mul hdφc).integrable_of_hasCompactSupport hdφsupp.mul_left
  have hφint : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hright_meas : AEStronglyMeasurable (fun x => db x * φ x) :=
    (lipschitzDirectionalDerivative_measurable b a).aestronglyMeasurable.mul
      hφ.continuous.aestronglyMeasurable
  have hright : Integrable (fun x => db x * φ x) := by
    apply Integrable.mono' (hφint.norm.const_mul (C : ℝ)) hright_meas
    filter_upwards with x
    calc
      ‖db x * φ x‖ = ‖db x‖ * ‖φ x‖ := norm_mul _ _
      _ ≤ (C : ℝ) * ‖φ x‖ := by
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_right
            (norm_lipschitzDirectionalDerivative_le b C hb a x) (norm_nonneg (φ x))
  rw [← (measurePreserving_realCoordinateInsertion a).integral_comp
      (realCoordinateInsertionMeasurableEquiv a).measurableEmbedding,
    ← (measurePreserving_realCoordinateInsertion a).integral_comp
      (realCoordinateInsertionMeasurableEquiv a).measurableEmbedding]
  change (∫ z : ℝ × CoordinateComplement a, b (e z) * dφ (e z)) =
    -(∫ z : ℝ × CoordinateComplement a, db (e z) * φ (e z))
  have hleft_prod : Integrable (fun z : ℝ × CoordinateComplement a =>
      b (e z) * dφ (e z)) :=
    ((measurePreserving_realCoordinateInsertion a).integrable_comp_emb
      (realCoordinateInsertionMeasurableEquiv a).measurableEmbedding).2 hleft
  have hright_prod : Integrable (fun z : ℝ × CoordinateComplement a =>
      db (e z) * φ (e z)) :=
    ((measurePreserving_realCoordinateInsertion a).integrable_comp_emb
      (realCoordinateInsertionMeasurableEquiv a).measurableEmbedding).2 hright
  rw [Measure.volume_eq_prod] at hleft_prod hright_prod ⊢
  rw [integral_prod_symm _ hleft_prod, integral_prod_symm _ hright_prod]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_ae_hasDerivAt_coordinateSlice a b C hb] with y hby
  have hφslice : ContDiff ℝ ∞
      (fun t : ℝ => φ (realCoordinateInsertionMeasurableEquiv a (t, y))) :=
    hφ.comp (contDiff_realCoordinateInsertion a y)
  have hslice := integral_mul_deriv_eq_neg_deriv_mul_of_lipschitz
    (LipschitzWith.coordinateSlice hb a y) hφslice
      (hasCompactSupport_coordinateSlice a φ hφc y)
  have hleftslice : (∫ t : ℝ, b (e (t, y)) * dφ (e (t, y))) =
      ∫ t : ℝ, b (e (t, y)) *
        deriv (fun r => φ (realCoordinateInsertionMeasurableEquiv a (r, y))) t := by
    apply integral_congr_ae
    filter_upwards with t
    rw [(hasDerivAt_coordinateSlice a φ y t
      ((hφ.differentiable (by simp)) _)).deriv]
  have hrightslice : (∫ t : ℝ, db (e (t, y)) * φ (e (t, y))) =
      ∫ t : ℝ, deriv (fun r => b (realCoordinateInsertionMeasurableEquiv a (r, y))) t *
        φ (e (t, y)) := by
    apply integral_congr_ae
    filter_upwards [hby] with t ht
    rw [ht.deriv]
    rfl
  calc
    (∫ t : ℝ, b (e (t, y)) * dφ (e (t, y))) = _ := hleftslice
    _ = -(∫ t : ℝ, deriv (fun r => b (realCoordinateInsertionMeasurableEquiv a (r, y))) t *
        φ (e (t, y))) := by simpa [e] using hslice
    _ = -(∫ t : ℝ, db (e (t, y)) * φ (e (t, y))) := congrArg Neg.neg hrightslice.symm

end LiebThirring.Sobolev

end
