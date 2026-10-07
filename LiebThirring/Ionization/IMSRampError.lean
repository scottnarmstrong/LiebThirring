/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.IMSCutoff
public import LiebThirring.Variational.SpectatorMultiplier

/-! # Sharp derivative error for the explicit IMS subset partition -/

public section

open MeasureTheory
open scoped NNReal

namespace LiebThirring
open Sobolev

/-- The sector product with the factor at particle `i` replaced by its selected
coordinate derivative. -/
@[expose] noncomputable def imsSectorCoordinateWeight {N : ℕ}
    (χ η : Position → ℝ) (S : Finset (Fin N)) (i : Fin N) (dχ dη : ℝ)
    (x : Configuration N) : ℝ :=
  (∏ j ∈ S, if j = i then dχ else χ (particlePosition x j)) *
    ∏ j ∈ Finset.univ \ S, if j = i then dη else η (particlePosition x j)

/-- Squaring and summing the coordinate-replaced subset products removes every
unselected particle factor. -/
theorem sum_imsSectorCoordinateWeight_sq {N : ℕ} (χ η : Position → ℝ)
    (hpart : ∀ y, χ y ^ 2 + η y ^ 2 = 1) (i : Fin N) (dχ dη : ℝ)
    (x : Configuration N) :
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
      imsSectorCoordinateWeight χ η S i dχ dη x ^ 2) = dχ ^ 2 + dη ^ 2 := by
  simp only [imsSectorCoordinateWeight, mul_pow, ← Finset.prod_pow]
  rw [← Finset.prod_add]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton i _ (by simp)]
  have hprod : (∏ j ∈ Finset.univ \ {i},
      ((if j = i then dχ else χ (particlePosition x j)) ^ 2 +
        (if j = i then dη else η (particlePosition x j)) ^ 2)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    have hji : j ≠ i := by
      exact fun h => (Finset.mem_sdiff.mp hj).2 (by simp [h])
    simp [hji, hpart]
  rw [hprod, mul_one]
  simp

/-- At a common differentiability point, the actual selected coordinate derivative of
a sector is the coordinate-replaced sector product. -/
theorem lipschitzDirectionalDerivative_imsSectorWeight {N : ℕ}
    (χ η : Position → ℝ) (S : Finset (Fin N)) (i : Fin N) (a : Fin 3)
    (x : Configuration N)
    (hxχ : ∀ j, DifferentiableAt ℝ (fun X : Configuration N => χ (particlePosition X j)) x)
    (hxη : ∀ j, DifferentiableAt ℝ (fun X : Configuration N => η (particlePosition X j)) x) :
    lipschitzDirectionalDerivative (imsSectorWeight χ η S) (i, a) x =
      imsSectorCoordinateWeight χ η S i
        (lipschitzDirectionalDerivative (fun X => χ (particlePosition X i)) (i, a) x)
        (lipschitzDirectionalDerivative (fun X => η (particlePosition X i)) (i, a) x) x := by
  let f : Fin N → Configuration N → ℝ := fun j X => χ (particlePosition X j)
  let g : Fin N → Configuration N → ℝ := fun j X => η (particlePosition X j)
  have hf : HasFDerivAt (fun X => ∏ j ∈ S, f j X)
      (∑ j ∈ S, (∏ k ∈ S.erase j, f k x) • fderiv ℝ (f j) x) x :=
    HasFDerivAt.finsetProd fun j _ => (hxχ j).hasFDerivAt
  have hg : HasFDerivAt (fun X => ∏ j ∈ Finset.univ \ S, g j X)
      (∑ j ∈ Finset.univ \ S,
        (∏ k ∈ (Finset.univ \ S).erase j, g k x) • fderiv ℝ (g j) x) x :=
    HasFDerivAt.finsetProd fun j _ => (hxη j).hasFDerivAt
  have hp := hf.mul hg
  unfold lipschitzDirectionalDerivative
  change (fderiv ℝ ((fun X => ∏ j ∈ S, f j X) *
      (fun X => ∏ j ∈ Finset.univ \ S, g j X)) x) (coordinateVector (i, a)) = _
  rw [hp.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [show (∑ j ∈ Finset.univ \ S,
      (∏ k ∈ (Finset.univ \ S).erase j, g k x) • fderiv ℝ (g j) x) (coordinateVector (i, a)) =
      ∑ j ∈ Finset.univ \ S, (∏ k ∈ (Finset.univ \ S).erase j, g k x) *
        fderiv ℝ (g j) x (coordinateVector (i, a)) by
          rw [show (∑ j ∈ Finset.univ \ S,
            (∏ k ∈ (Finset.univ \ S).erase j, g k x) • fderiv ℝ (g j) x) =
              (Finset.univ \ S).sum (fun j =>
                (∏ k ∈ (Finset.univ \ S).erase j, g k x) • fderiv ℝ (g j) x) from rfl,
            sum_apply]
          simp]
  rw [show (∑ j ∈ S, (∏ k ∈ S.erase j, f k x) • fderiv ℝ (f j) x)
      (coordinateVector (i, a)) =
      ∑ j ∈ S, (∏ k ∈ S.erase j, f k x) *
        fderiv ℝ (f j) x (coordinateVector (i, a)) by
          rw [show (∑ j ∈ S, (∏ k ∈ S.erase j, f k x) • fderiv ℝ (f j) x) =
              S.sum (fun j => (∏ k ∈ S.erase j, f k x) • fderiv ℝ (f j) x) from rfl,
            sum_apply]
          simp]
  have hfzero (j : Fin N) (hji : j ≠ i) :
      fderiv ℝ (f j) x (coordinateVector (i, a)) = 0 := by
    change lipschitzDirectionalDerivative
      (fun X : Configuration N => χ (particlePosition X j)) (i, a) x = 0
    exact lipschitzDirectionalDerivative_selected_other j i hji.symm a χ x
  have hgzero (j : Fin N) (hji : j ≠ i) :
      fderiv ℝ (g j) x (coordinateVector (i, a)) = 0 := by
    change lipschitzDirectionalDerivative
      (fun X : Configuration N => η (particlePosition X j)) (i, a) x = 0
    exact lipschitzDirectionalDerivative_selected_other j i hji.symm a η x
  by_cases hi : i ∈ S
  · have hnot : i ∉ Finset.univ \ S := by simp [hi]
    have hgsum : (∑ j ∈ Finset.univ \ S,
        (∏ k ∈ (Finset.univ \ S).erase j, g k x) *
          fderiv ℝ (g j) x (coordinateVector (i, a))) = 0 :=
      Finset.sum_eq_zero (fun j hj => by
      have hji : j ≠ i := fun h => hnot (h ▸ hj)
      rw [hgzero j hji, mul_zero])
    have hfsum : (∑ j ∈ S, (∏ k ∈ S.erase j, f k x) *
        fderiv ℝ (f j) x (coordinateVector (i, a))) =
        (∏ k ∈ S.erase i, f k x) * fderiv ℝ (f i) x (coordinateVector (i, a)) :=
      Finset.sum_eq_single i
      (fun j _ hji => by rw [hfzero j hji, mul_zero])
      (fun h => (h hi).elim)
    rw [hgsum, hfsum]
    simp only [mul_zero, zero_add, imsSectorCoordinateWeight]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton i _ (fun h => (h hi).elim)]
    have hinrest : (∏ j ∈ S \ {i},
        if j = i then
          fderiv ℝ (fun X => χ (particlePosition X i)) x (coordinateVector (i, a))
        else χ (particlePosition x j)) = ∏ j ∈ S.erase i, f j x := by
      rw [Finset.erase_eq]
      apply Finset.prod_congr
      · rfl
      · intro j hj
        have hji : j ≠ i := by
          exact fun h => (Finset.mem_sdiff.mp hj).2 (by simp [h])
        simp [hji, f]
    have hout : (∏ j ∈ Finset.univ \ S,
        if j = i then
          fderiv ℝ (fun X => η (particlePosition X i)) x (coordinateVector (i, a))
        else η (particlePosition x j)) = ∏ j ∈ Finset.univ \ S, g j x := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := fun h => hnot (h ▸ hj)
      simp [hji, g]
    rw [hinrest, hout]
    simp only [f]
    simp
    ring
  · have himem : i ∈ Finset.univ \ S := by simp [hi]
    have hfsum : (∑ j ∈ S, (∏ k ∈ S.erase j, f k x) *
        fderiv ℝ (f j) x (coordinateVector (i, a))) = 0 :=
      Finset.sum_eq_zero (fun j hj => by
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      rw [hfzero j hji, mul_zero])
    have hgsum : (∑ j ∈ Finset.univ \ S,
        (∏ k ∈ (Finset.univ \ S).erase j, g k x) *
          fderiv ℝ (g j) x (coordinateVector (i, a))) =
        (∏ k ∈ (Finset.univ \ S).erase i, g k x) *
          fderiv ℝ (g i) x (coordinateVector (i, a)) :=
      Finset.sum_eq_single i
      (fun j _ hji => by rw [hgzero j hji, mul_zero])
      (fun h => (h himem).elim)
    rw [hfsum, hgsum]
    simp only [mul_zero, add_zero, imsSectorCoordinateWeight]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton i _ (fun h => (h himem).elim)]
    have houtrest : (∏ j ∈ (Finset.univ \ S) \ {i},
        if j = i then
          fderiv ℝ (fun X => η (particlePosition X i)) x (coordinateVector (i, a))
        else η (particlePosition x j)) =
        ∏ j ∈ (Finset.univ \ S).erase i, g j x := by
      rw [Finset.erase_eq]
      apply Finset.prod_congr
      · rfl
      · intro j hj
        have hji : j ≠ i := by
          exact fun h => (Finset.mem_sdiff.mp hj).2 (by simp [h])
        simp [hji, g]
    have hin : (∏ j ∈ S,
        if j = i then
          fderiv ℝ (fun X => χ (particlePosition X i)) x (coordinateVector (i, a))
        else χ (particlePosition x j)) = ∏ j ∈ S, f j x := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      simp [hji, f]
    rw [hin, houtrest]
    simp only [g]
    simp
    exact Or.inl (mul_comm _ _)

/-- Three selected coordinate values of a scalar functional are bounded by its operator norm. -/
theorem sum_selected_coordinate_apply_sq_le_norm_sq {N : ℕ}
    (L : Configuration N →L[ℝ] ℝ) (i : Fin N) :
    (∑ a : Fin 3, L (coordinateVector (i, a)) ^ 2) ≤ ‖L‖ ^ 2 := by
  let v : Configuration N := ContinuousLinearMap.adjoint L 1
  have hc (c : Fin N × Fin 3) : v c = L (coordinateVector c) := by
    have h := ContinuousLinearMap.adjoint_inner_left L (coordinateVector c) 1
    simpa [v, coordinateVector, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left, real_inner_comm] using h
  calc
    _ = ∑ a : Fin 3, v (i, a) ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hc]
    _ ≤ ∑ c : Fin N × Fin 3, v c ^ 2 := by
      rw [Fintype.sum_prod_type]
      exact Finset.single_le_sum
        (fun j _ => Finset.sum_nonneg (fun a _ => sq_nonneg (v (j, a))))
        (Finset.mem_univ i)
    _ = ‖v‖ ^ 2 := EuclideanSpace.real_norm_sq_eq v |>.symm
    _ ≤ ‖L‖ ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc
        ‖v‖ ≤ ‖ContinuousLinearMap.adjoint L‖ * ‖(1 : ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ = ‖L‖ := by simp

/-- The selected three-coordinate derivative of a `C`-Lipschitz scalar function has
squared norm at most `C²` at every differentiability point. -/
theorem sum_selected_lipschitzDirectionalDerivative_sq_le {N : ℕ}
    (φ : Configuration N → ℝ) (C : ℝ≥0) (hφ : LipschitzWith C φ)
    (i : Fin N) (x : Configuration N) :
    (∑ a : Fin 3, lipschitzDirectionalDerivative φ (i, a) x ^ 2) ≤ (C : ℝ) ^ 2 := by
  calc
    _ ≤ ‖fderiv ℝ φ x‖ ^ 2 := sum_selected_coordinate_apply_sq_le_norm_sq _ i
    _ ≤ (C : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _)
      (norm_fderiv_le_of_lipschitz ℝ hφ) 2

/-- For each particle, the explicit sine/cosine pair has total squared three-coordinate
derivative at most `π²/(4R²)`. -/
theorem ae_sum_imsChi_imsEta_selected_derivative_sq_le {N : ℕ} {R : ℝ} (hR : 0 < R)
    (i : Fin N) :
    ∀ᵐ x ∂(volume : Measure (Configuration N)),
      (∑ a : Fin 3, (
        lipschitzDirectionalDerivative
            (fun X => imsChi R (particlePosition X i)) (i, a) x ^ 2 +
          lipschitzDirectionalDerivative
            (fun X => imsEta R (particlePosition X i)) (i, a) x ^ 2)) ≤
        Real.pi ^ 2 / (4 * R ^ 2) := by
  let φ := fun X : Configuration N => imsAngle (‖particlePosition X i‖ / R)
  let C : ℝ≥0 := NNReal.mk (Real.pi / (2 * R)) (by positivity)
  have hφ : LipschitzWith C φ :=
    lipschitzWith_selected_multiplier i _ C (lipschitzWith_imsRadialAngle hR)
  have htrig := ae_sq_lipschitzDirectionalDerivative_cos_add_sin φ C hφ
  filter_upwards [htrig] with x hx
  calc
    _ = ∑ a : Fin 3, lipschitzDirectionalDerivative φ (i, a) x ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      simpa [imsChi, imsEta, φ] using hx (i, a)
    _ ≤ (C : ℝ) ^ 2 := sum_selected_lipschitzDirectionalDerivative_sq_le φ C hφ i x
    _ = Real.pi ^ 2 / (4 * R ^ 2) := by
      change (Real.pi / (2 * R)) ^ 2 = _
      field_simp
      ring

/-- The literal subset partition has the exact sharp many-particle IMS error bound,
with no spatial-dimension or sector-cardinality factor. -/
theorem ae_sum_imsSectorWeight_derivative_sq_le {N : ℕ} {R : ℝ} (hR : 0 < R) :
    ∀ᵐ x ∂(volume : Measure (Configuration N)),
      (∑ ia : Fin N × Fin 3,
        ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
          lipschitzDirectionalDerivative (imsSectorWeight (imsChi R) (imsEta R) S) ia x ^ 2) ≤
        N * Real.pi ^ 2 / (4 * R ^ 2) := by
  let C : ℝ≥0 := NNReal.mk (Real.pi / (2 * R)) (by positivity)
  have hχ (j : Fin N) : LipschitzWith C
      (fun X : Configuration N => imsChi R (particlePosition X j)) :=
    lipschitzWith_selected_multiplier j _ C (lipschitzWith_imsChi hR)
  have hη (j : Fin N) : LipschitzWith C
      (fun X : Configuration N => imsEta R (particlePosition X j)) :=
    lipschitzWith_selected_multiplier j _ C (lipschitzWith_imsEta hR)
  have hdχ : ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ j,
      DifferentiableAt ℝ (fun X : Configuration N => imsChi R (particlePosition X j)) x :=
    ae_all_iff.mpr fun j => (hχ j).ae_differentiableAt_configuration
  have hdη : ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ j,
      DifferentiableAt ℝ (fun X : Configuration N => imsEta R (particlePosition X j)) x :=
    ae_all_iff.mpr fun j => (hη j).ae_differentiableAt_configuration
  have hp : ∀ᵐ x ∂(volume : Measure (Configuration N)), ∀ i,
      (∑ a : Fin 3, (
        lipschitzDirectionalDerivative
            (fun X => imsChi R (particlePosition X i)) (i, a) x ^ 2 +
          lipschitzDirectionalDerivative
            (fun X => imsEta R (particlePosition X i)) (i, a) x ^ 2)) ≤
        Real.pi ^ 2 / (4 * R ^ 2) :=
    ae_all_iff.mpr (ae_sum_imsChi_imsEta_selected_derivative_sq_le hR)
  filter_upwards [hdχ, hdη, hp] with x hxχ hxη hxpair
  rw [Fintype.sum_prod_type]
  simp_rw [show ∀ i a, (∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
      lipschitzDirectionalDerivative (imsSectorWeight (imsChi R) (imsEta R) S) (i, a) x ^ 2) =
      lipschitzDirectionalDerivative (fun X => imsChi R (particlePosition X i)) (i, a) x ^ 2 +
        lipschitzDirectionalDerivative (fun X => imsEta R (particlePosition X i)) (i, a) x ^ 2 by
    intro i a
    simp_rw [lipschitzDirectionalDerivative_imsSectorWeight
      (imsChi R) (imsEta R) _ i a x hxχ hxη]
    exact sum_imsSectorCoordinateWeight_sq _ _ (imsChi_sq_add_imsEta_sq R)
      i _ _ x]
  calc
    _ ≤ ∑ _i : Fin N, Real.pi ^ 2 / (4 * R ^ 2) :=
      Finset.sum_le_sum fun i _ => hxpair i
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The literal sharp IMS error density for the radial subset partition. -/
@[expose] noncomputable def imsRampErrorDensity {N q : ℕ} (R : ℝ) (u : State N q)
    (x : Configuration N) : ℝ :=
  (∑ ia : Fin N × Fin 3,
    ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
      lipschitzDirectionalDerivative (imsSectorWeight (imsChi R) (imsEta R) S) ia x ^ 2) *
    ‖u x‖ ^ 2

/-- The explicit radial IMS error density is integrable. -/
theorem integrable_imsRampErrorDensity {N q : ℕ} {R : ℝ} (hR : 0 < R)
    (u : State N q) : Integrable (imsRampErrorDensity R u) := by
  let K : ℝ := N * Real.pi ^ 2 / (4 * R ^ 2)
  have hmeas : AEStronglyMeasurable (imsRampErrorDensity R u)
      (volume : Measure (Configuration N)) := by
    apply AEStronglyMeasurable.mul
    · exact (Finset.measurable_sum Finset.univ (fun ia _ =>
        Finset.measurable_sum Finset.univ.powerset (fun S _ =>
          (lipschitzDirectionalDerivative_measurable
            (imsSectorWeight (imsChi R) (imsEta R) S) ia).pow_const 2))).aestronglyMeasurable
    · exact ((Lp.stronglyMeasurable u).norm.aestronglyMeasurable.pow 2).congr
        (Filter.Eventually.of_forall fun _ => rfl)
  apply Integrable.mono' ((integrable_state_norm_sq u).const_mul K) hmeas
  filter_upwards [ae_sum_imsSectorWeight_derivative_sq_le hR] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)
  · exact mul_nonneg (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)

/-- The integrated literal radial IMS correction is bounded by exactly
`Nπ²/(4R²)` times the unnormalized mass. -/
theorem integral_imsRampErrorDensity_le {N q : ℕ} {R : ℝ} (hR : 0 < R)
    (u : State N q) :
    ∫ x : Configuration N, imsRampErrorDensity R u x ≤
      (N * Real.pi ^ 2 / (4 * R ^ 2)) * ‖u‖ ^ 2 := by
  calc
    _ ≤ ∫ x : Configuration N,
        (N * Real.pi ^ 2 / (4 * R ^ 2)) * ‖u x‖ ^ 2 :=
      integral_mono_ae (integrable_imsRampErrorDensity hR u)
        ((integrable_state_norm_sq u).const_mul _)
        ((ae_sum_imsSectorWeight_derivative_sq_le hR).mono fun x hx =>
          mul_le_mul_of_nonneg_right hx (sq_nonneg _))
    _ = _ := by rw [integral_const_mul, integral_state_norm_sq]

end LiebThirring

end
