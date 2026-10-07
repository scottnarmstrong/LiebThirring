/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Ionization.WeightedComplex
public import LiebThirring.Variational.SlicesSmooth
public import LiebThirring.Variational.SpectatorMultiplier

/-! # Selected-particle weighted positivity on the compact smooth core

Argument weighted positivity is applied on selected-particle slices, with the other positions
held fixed. The Hilbert target retains all spin amplitudes.
-/

@[expose] public section
open MeasureTheory WithLp LineDeriv
open scoped SchwartzMap ContDiff FourierTransform
namespace LiebThirring
open Sobolev Variational

/-- Isometric insertion of the selected position with all spectators zero. -/
noncomputable def selectedPositionEmbedding {N : ℕ} (i : Fin N) :
    Position →ₗᵢ[ℝ] Configuration N :=
  (configurationInsertionLinearIsometryEquiv i).toLinearIsometry.comp
    (show Position →ₗᵢ[ℝ] WithLp 2 (Position × OtherConfiguration i) from
    { toFun := fun x => toLp 2 (x, (0 : OtherConfiguration i))
      map_add' := by intros; apply WithLp.ofLp_injective; simp
      map_smul' := by intros; apply WithLp.ofLp_injective; simp
      norm_map' := fun x => WithLp.norm_toLp_fst 2 Position (OtherConfiguration i) x })

@[simp] theorem selectedPositionEmbedding_apply {N : ℕ} (i : Fin N) (x : Position) :
    selectedPositionEmbedding i x = insertParticle i x 0 := by
  change configurationInsertionLinearIsometryEquiv i (toLp 2 (x, 0)) = _
  exact configurationInsertionLinearIsometryEquiv_apply i _

theorem selectedPositionEmbedding_basis {N : ℕ} (i : Fin N) (a : Fin 3) :
    selectedPositionEmbedding i (EuclideanSpace.basisFun (Fin 3) ℝ a) =
      coordinateVector (i, a) := by
  rw [selectedPositionEmbedding_apply]
  ext jb
  simp only [insertParticle, PiLp.toLp_apply, coordinateVector,
    EuclideanSpace.basisFun_apply]
  split
  · rename_i h
    simp [h, Prod.ext_iff]
  · rename_i h
    simp [h, Prod.ext_iff]

/-- Affine insertion of a selected position with fixed spectators. -/
noncomputable def selectedPositionInsertion {N : ℕ} (i : Fin N)
    (y : OtherConfiguration i) (x : Position) : Configuration N :=
  selectedPositionEmbedding i x + insertParticle i 0 y

@[simp] theorem selectedPositionInsertion_eq {N : ℕ} (i : Fin N)
    (y : OtherConfiguration i) (x : Position) :
    selectedPositionInsertion i y x = insertParticle i x y := by
  rw [selectedPositionInsertion, selectedPositionEmbedding_apply]
  ext jb
  simp only [PiLp.add_apply, insertParticle, PiLp.toLp_apply]
  split <;> simp

theorem selectedPositionInsertion_antilipschitz {N : ℕ} (i : Fin N)
    (y : OtherConfiguration i) : AntilipschitzWith 1 (selectedPositionInsertion i y) := by
  rw [antilipschitzWith_iff_le_mul_dist]
  intro a b
  simp only [selectedPositionInsertion, dist_eq_norm, add_sub_add_right_eq_sub]
  rw [← map_sub, LinearIsometry.norm_map]
  simp

theorem selectedPositionInsertion_contDiff {N : ℕ} (i : Fin N)
    (y : OtherConfiguration i) : ContDiff ℝ ⊤ (selectedPositionInsertion i y) :=
  (selectedPositionEmbedding i).toContinuousLinearMap.contDiff.add contDiff_const

theorem fderiv_selectedPosition_slice {N q : ℕ} (i : Fin N) (y : OtherConfiguration i)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (x : Position) (a : Fin 3) :
    fderiv ℝ (fun z => f (insertParticle i z y)) x
      (EuclideanSpace.basisFun (Fin 3) ℝ a) =
      fderiv ℝ f (insertParticle i x y) (coordinateVector (i, a)) := by
  have hi : HasFDerivAt (selectedPositionInsertion i y)
      (selectedPositionEmbedding i).toContinuousLinearMap x :=
    ((selectedPositionEmbedding i).toContinuousLinearMap.hasFDerivAt).add_const
      (insertParticle i 0 y)
  have hd := f.differentiableAt (x := insertParticle i x y)
  rw [← selectedPositionInsertion_eq] at hd
  have hc := hd.hasFDerivAt.comp x hi
  have he : (fun z => f (selectedPositionInsertion i y z)) =
      fun z => f (insertParticle i z y) := by simp
  change HasFDerivAt (fun z => f (selectedPositionInsertion i y z)) _ x at hc
  rw [he] at hc
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, selectedPositionInsertion_eq]
  change fderiv ℝ f (insertParticle i x y)
    (selectedPositionEmbedding i (EuclideanSpace.basisFun (Fin 3) ℝ a)) = _
  rw [selectedPositionEmbedding_basis]

/-- Selected-particle projection as a continuous linear map. -/
noncomputable def selectedPositionProjection {N : ℕ} (i : Fin N) :
    Configuration N →L[ℝ] Position :=
  (WithLp.fstL 2 ℝ Position (OtherConfiguration i)).comp
    (configurationInsertionLinearIsometryEquiv i).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem selectedPositionProjection_apply {N : ℕ} (i : Fin N)
    (X : Configuration N) : selectedPositionProjection i X = particlePosition X i := by
  obtain ⟨z, rfl⟩ := (configurationInsertionLinearIsometryEquiv i).surjective X
  change ((configurationInsertionLinearIsometryEquiv i).symm
    (configurationInsertionLinearIsometryEquiv i z)).fst = _
  rw [LinearIsometryEquiv.symm_apply_apply,
    configurationInsertionLinearIsometryEquiv_apply, particlePosition_insertParticle]
  rfl

@[simp] theorem selectedPositionProjection_coordinateVector {N : ℕ} (i : Fin N)
    (a : Fin 3) : selectedPositionProjection i (coordinateVector (i, a)) =
      EuclideanSpace.basisFun (Fin 3) ℝ a := by
  rw [← selectedPositionEmbedding_basis, selectedPositionEmbedding_apply,
    selectedPositionProjection_apply, particlePosition_insertParticle]

theorem fderiv_selected_ionizationWeight {N : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (i : Fin N) (X : Configuration N) (hX : particlePosition X i ≠ 0) (a : Fin 3) :
    lipschitzDirectionalDerivative (fun Y => ionizationWeight ε ‖particlePosition Y i‖)
      (i, a) X = fderiv ℝ (fun x : Position => ionizationWeight ε ‖x‖)
        (particlePosition X i) (EuclideanSpace.basisFun (Fin 3) ℝ a) := by
  have hw : DifferentiableAt ℝ (fun x : Position => ionizationWeight ε ‖x‖)
      (particlePosition X i) := by
    apply DifferentiableAt.comp _
      ((hasDerivAt_ionizationWeight (by positivity)).differentiableAt)
      (hasFDerivAt_position_norm hX).differentiableAt
  rw [← selectedPositionProjection_apply] at hw
  have hh := hw.hasFDerivAt.comp X (selectedPositionProjection i).hasFDerivAt
  have he : (fun Y => ionizationWeight ε ‖selectedPositionProjection i Y‖) =
      (fun Y => ionizationWeight ε ‖particlePosition Y i‖) := by funext Y; simp
  change HasFDerivAt (fun Y => ionizationWeight ε ‖selectedPositionProjection i Y‖) _ X at hh
  rw [he] at hh
  unfold lipschitzDirectionalDerivative
  rw [hh.fderiv, ContinuousLinearMap.comp_apply,
    selectedPositionProjection_coordinateVector, selectedPositionProjection_apply]

theorem hasCompactSupport_selectedPosition_slice {N q : ℕ} (i : Fin N)
    (y : OtherConfiguration i) {f : 𝓢(Configuration N, SpinAmplitudes N q)}
    (hfc : HasCompactSupport f) : HasCompactSupport (fun x => f (insertParticle i x y)) := by
  have hc := hfc.comp_isClosedEmbedding
    ((selectedPositionInsertion_antilipschitz i y).isClosedEmbedding
      ((selectedPositionEmbedding i).toContinuousLinearMap.uniformContinuous.add
        uniformContinuous_const))
  simpa only [Function.comp_def, selectedPositionInsertion_eq] using hc

/-- Pointwise representative of a selected weighted kinetic cross term. -/
theorem schwartzCoordinateDerivativeL2_eq_toLp {N q : ℕ}
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (a : Fin N × Fin 3) :
    schwartzCoordinateDerivativeL2 f a = (lineDerivOp (coordinateVector a) f).toLp 2 volume := by
  apply (hasWeakDerivative_schwartzCoordinateDerivativeL2 f a).unique
  rw [hasWeakDerivative_iff_fourier_eq_symbol]
  have hderiv : 𝓕 ((lineDerivOp (coordinateVector a) f).toLp 2 volume) =
      (𝓕 (lineDerivOp (coordinateVector a) f)).toLp 2 volume :=
    SchwartzMap.toLp_fourier_eq _
  have hstate : 𝓕 (f.toLp 2 volume) = (𝓕 f).toLp 2 volume := SchwartzMap.toLp_fourier_eq f
  filter_upwards [(𝓕 (lineDerivOp (coordinateVector a) f)).coeFn_toLp 2 volume,
    (𝓕 f).coeFn_toLp 2 volume] with ξ hd hu
  rw [hderiv, hstate, hd, hu, fourier_lineDeriv_coordinate]

/-- Pointwise representative of a selected weighted kinetic cross term. -/
noncomputable def selectedSmoothIonizationCross {N q : ℕ} (ε : ℝ) (i : Fin N)
    (f : 𝓢(Configuration N, SpinAmplitudes N q)) (a : Fin 3)
    (X : Configuration N) : ℂ :=
  inner ℂ
    ((ionizationWeight ε ‖particlePosition X i‖ : ℂ) •
      fderiv ℝ f X (coordinateVector (i, a)) +
    (lipschitzDirectionalDerivative
      (fun Y => ionizationWeight ε ‖particlePosition Y i‖) (i, a) X : ℂ) • f X)
    (fderiv ℝ f X (coordinateVector (i, a)))

theorem selectedSmoothIonizationCross_ae_eq {N q : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (i : Fin N) (f : 𝓢(Configuration N, SpinAmplitudes N q)) (a : Fin 3)
    (B : ℝ) (hB : ∀ x : Position, ‖ionizationWeight ε ‖x‖‖ ≤ B) :
    (fun X => inner ℂ
      ((lipschitzProductDerivative (fun Y => ionizationWeight ε ‖particlePosition Y i‖)
        B (fun _Y => hB _) 1
        (lipschitzWith_selected_multiplier i _ 1 (lipschitzWith_ionizationWeight hε))
        (i, a) (f.toLp 2 volume) (schwartzCoordinateDerivativeL2 f (i, a))) X)
      ((schwartzCoordinateDerivativeL2 f (i, a)) X)) =ᵐ[volume]
      selectedSmoothIonizationCross ε i f a := by
  filter_upwards [lipschitzProductDerivative_coeFn
      (fun Y => ionizationWeight ε ‖particlePosition Y i‖) B (fun _Y => hB _) 1
      (lipschitzWith_selected_multiplier i _ 1 (lipschitzWith_ionizationWeight hε))
      (i, a) (f.toLp 2 volume) (schwartzCoordinateDerivativeL2 f (i, a)),
    f.coeFn_toLp 2 volume,
    (lineDerivOp (coordinateVector (i, a)) f).coeFn_toLp 2 volume] with X hG hf hg
  have hg' : (schwartzCoordinateDerivativeL2 f (i, a)) X =
      fderiv ℝ f X (coordinateVector (i, a)) := by
    simpa only [schwartzCoordinateDerivativeL2_eq_toLp,
      SchwartzMap.lineDerivOp_apply_eq_fderiv] using hg
  rw [hG, hf, hg']
  rfl

theorem integrable_selectedSmoothIonizationCross {N q : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (i : Fin N) (f : 𝓢(Configuration N, SpinAmplitudes N q)) (a : Fin 3)
    (B : ℝ) (hB : ∀ x : Position, ‖ionizationWeight ε ‖x‖‖ ≤ B) :
    Integrable (selectedSmoothIonizationCross ε i f a) := by
  exact (L2.integrable_inner (𝕜 := ℂ)
    (lipschitzProductDerivative (fun Y => ionizationWeight ε ‖particlePosition Y i‖)
      B (fun _Y => hB _) 1
      (lipschitzWith_selected_multiplier i _ 1 (lipschitzWith_ionizationWeight hε))
      (i, a) (f.toLp 2 volume) (schwartzCoordinateDerivativeL2 f (i, a)))
    (schwartzCoordinateDerivativeL2 f (i, a))).congr
      (selectedSmoothIonizationCross_ae_eq hε i f a B hB)

theorem selectedSmoothIonizationCross_slice_ae {N q : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (i : Fin N) (f : 𝓢(Configuration N, SpinAmplitudes N q)) (a : Fin 3)
    (y : OtherConfiguration i) :
    (fun x => selectedSmoothIonizationCross ε i f a (insertParticle i x y)) =ᵐ[volume]
    (fun x => inner ℂ
      (fderiv ℝ (fun z => ionizationWeight ε ‖z‖ • f (insertParticle i z y)) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a))
      (fderiv ℝ (fun z => f (insertParticle i z y)) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a))) := by
  filter_upwards [show ∀ᵐ x : Position, x ≠ 0 by rw [ae_iff]; simp] with x hx
  have hdf : Differentiable ℝ (fun z => f (insertParticle i z y)) := by
    have hd := f.differentiable.comp
      ((selectedPositionInsertion_contDiff i y).differentiable (by simp))
    simpa only [Function.comp_def, selectedPositionInsertion_eq] using hd
  rw [fderiv_ionizationWeight_smul hε hdf hx,
    fderiv_selectedPosition_slice]
  unfold selectedSmoothIonizationCross
  rw [particlePosition_insertParticle,
    fderiv_selected_ionizationWeight hε i _ (by simpa using hx),
    particlePosition_insertParticle, fderiv_ionizationWeight hε hx]
  congr 1

/-- Selected-particle weighted positivity on the compact Schwartz core. -/
theorem integral_selectedSmoothIonizationCross_nonneg {N q : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε) (i : Fin N) (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (hfc : HasCompactSupport f) (B : ℝ)
    (hB : ∀ x : Position, ‖ionizationWeight ε ‖x‖‖ ≤ B) :
    0 ≤ (∑ a : Fin 3, ∫ X, selectedSmoothIonizationCross ε i f a X).re := by
  have hint (a : Fin 3) := integrable_selectedSmoothIonizationCross hε i f a B hB
  have hsum : Integrable (fun X => ∑ a : Fin 3, selectedSmoothIonizationCross ε i f a X) :=
    integrable_finsetSum Finset.univ (fun a _ => hint a)
  rw [← integral_finsetSum Finset.univ (fun a _ => hint a)]
  have hre : (∫ X, ∑ a : Fin 3, selectedSmoothIonizationCross ε i f a X).re =
      ∫ X, (∑ a : Fin 3, selectedSmoothIonizationCross ε i f a X).re :=
    (integral_re hsum).symm
  rw [hre]
  rw [← (measurePreserving_insertion i).integral_comp'
    (fun X => (∑ a : Fin 3, selectedSmoothIonizationCross ε i f a X).re)]
  have hp := (measurePreserving_insertion i).integrable_comp_of_integrable hsum.re
  change Integrable (fun z : Position × OtherConfiguration i =>
    (∑ a : Fin 3, selectedSmoothIonizationCross ε i f a
      (insertionMeasurableEquiv i z)).re) (volume.prod volume) at hp
  change 0 ≤ ∫ z : Position × OtherConfiguration i,
    (∑ a : Fin 3, selectedSmoothIonizationCross ε i f a
      (insertionMeasurableEquiv i z)).re ∂volume.prod volume
  rw [integral_prod_symm _ hp]
  apply integral_nonneg
  intro y
  simp only [insertionMeasurableEquiv_apply]
  have hd : ContDiff ℝ 2 (fun x => f (insertParticle i x y)) := by
    have hh := ((f.smooth ⊤).of_le (show (2 : ℕ∞ω) ≤ ∞ by norm_num)).comp
      ((selectedPositionInsertion_contDiff i y).of_le (by simp))
    simpa only [Function.comp_def, selectedPositionInsertion_eq] using hh
  have hc := hasCompactSupport_selectedPosition_slice i y hfc
  have hslice (a : Fin 3) : Integrable
      (fun x => selectedSmoothIonizationCross ε i f a (insertParticle i x y)) :=
    (integrable_ionization_complex_cross hε hd hc a).congr
      (selectedSmoothIonizationCross_slice_ae hε i f a y).symm
  have hre' : (∫ x, ∑ a : Fin 3,
      selectedSmoothIonizationCross ε i f a (insertParticle i x y)).re =
      ∫ x, (∑ a : Fin 3, selectedSmoothIonizationCross ε i f a
        (insertParticle i x y)).re :=
    (integral_re (integrable_finsetSum Finset.univ (fun a _ => hslice a))).symm
  rw [← hre', integral_finsetSum Finset.univ (fun a _ => hslice a)]
  have he (a : Fin 3) := integral_congr_ae
    (selectedSmoothIonizationCross_slice_ae hε i f a y)
  simp_rw [he]
  exact integral_ionization_complex_cross_nonneg hε hd hc

/-- Bundled L² form of selected-particle weighted positivity, for graph limits. -/
theorem re_sum_inner_selected_ionization_productDerivative_nonneg {N q : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε) (i : Fin N) (f : 𝓢(Configuration N, SpinAmplitudes N q))
    (hfc : HasCompactSupport f) (B : ℝ)
    (hB : ∀ x : Position, ‖ionizationWeight ε ‖x‖‖ ≤ B) :
    0 ≤ (∑ a : Fin 3, inner ℂ
      (lipschitzProductDerivative (fun Y => ionizationWeight ε ‖particlePosition Y i‖)
        B (fun _Y => hB _) 1
        (lipschitzWith_selected_multiplier i _ 1 (lipschitzWith_ionizationWeight hε))
        (i, a) (f.toLp 2 volume) (schwartzCoordinateDerivativeL2 f (i, a)))
      (schwartzCoordinateDerivativeL2 f (i, a))).re := by
  have he (a : Fin 3) : inner ℂ
      (lipschitzProductDerivative (fun Y => ionizationWeight ε ‖particlePosition Y i‖)
        B (fun _Y => hB _) 1
        (lipschitzWith_selected_multiplier i _ 1 (lipschitzWith_ionizationWeight hε))
        (i, a) (f.toLp 2 volume) (schwartzCoordinateDerivativeL2 f (i, a)))
      (schwartzCoordinateDerivativeL2 f (i, a)) =
      ∫ X, selectedSmoothIonizationCross ε i f a X := by
    rw [L2.inner_def]
    exact integral_congr_ae (selectedSmoothIonizationCross_ae_eq hε i f a B hB)
  simp_rw [he]
  exact integral_selectedSmoothIonizationCross_nonneg hε i f hfc B hB

end LiebThirring
end
