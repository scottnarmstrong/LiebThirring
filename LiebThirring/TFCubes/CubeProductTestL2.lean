/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeProductTests
public import LiebThirring.TFCubes.CubeCoordinates
public import LiebThirring.TFCubes.IntervalDominatedConvergence
public import LiebThirring.TFCubes.IntervalCutoffEstimates
public import LiebThirring.TFCubes.IntervalModeDerivatives

/-! # L2 convergence of compact cube product tests -/

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

namespace LiebThirring.TFCubes

private theorem neumannIntervalCoefficient_nonneg_test
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (m : ℕ) :
    0 ≤ neumannIntervalCoefficient ℓ m := by
  unfold neumannIntervalCoefficient
  split_ifs <;> positivity

private theorem abs_neumannIntervalMode_le_test
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (m : ℕ) (x : ℝ) :
    |neumannIntervalMode ℓ m x| ≤ neumannIntervalCoefficient ℓ m := by
  rw [neumannIntervalMode, abs_mul,
    abs_of_nonneg (neumannIntervalCoefficient_nonneg_test ℓ m)]
  exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
    (neumannIntervalCoefficient_nonneg_test ℓ m)).trans_eq (mul_one _)

private theorem norm_compactNeumannFactor_le
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (m j : ℕ) (x : ℝ) :
    ‖compactNeumannFactor ℓ m j x‖ ≤ neumannIntervalCoefficient ℓ m := by
  rw [compactNeumannFactor, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (intervalInteriorCutoff_nonneg ℓ j x)]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul (intervalInteriorCutoff_le_one ℓ j x)
    (abs_neumannIntervalMode_le_test ℓ m x) (abs_nonneg _)
    zero_le_one).trans_eq (one_mul _)

noncomputable def cubeTestFactorBound (ℓ : {ℓ : ℝ // 0 < ℓ})
    (k : Fin 3 → ℕ) : ℝ :=
  Real.sqrt (2 / ℓ.val) + ∑ i : Fin 3, neumannIntervalCoefficient ℓ (k i)

private theorem cubeTestFactorBound_nonneg (ℓ : {ℓ : ℝ // 0 < ℓ})
    (k : Fin 3 → ℕ) : 0 ≤ cubeTestFactorBound ℓ k := by
  exact add_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun i _ =>
    neumannIntervalCoefficient_nonneg_test ℓ (k i))

private theorem compact_test_factor_le_bound (ℓ : {ℓ : ℝ // 0 < ℓ})
    (k : Fin 3 → ℕ) (a : Fin 3) (n : ℕ+) (j : ℕ) (i : Fin 3) (x : ℝ) :
    ‖if i = a then compactDirichletMode ℓ n j x
        else compactNeumannFactor ℓ (k i) j x‖ ≤ cubeTestFactorBound ℓ k := by
  by_cases hia : i = a
  · simp only [hia, ↓reduceIte, compactDirichletMode, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (intervalInteriorCutoff_nonneg ℓ j x)]
    refine (mul_le_mul (intervalInteriorCutoff_le_one ℓ j x)
      (abs_dirichletIntervalMode_le ℓ n x) (abs_nonneg _) zero_le_one).trans ?_
    simp only [one_mul, cubeTestFactorBound]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun r _ =>
      neumannIntervalCoefficient_nonneg_test ℓ (k r))
  · simp only [ite_eq_right hia]
    exact (norm_compactNeumannFactor_le ℓ (k i) j x).trans <|
      (Finset.single_le_sum
        (fun r _ => neumannIntervalCoefficient_nonneg_test ℓ (k r))
        (Finset.mem_univ i)).trans (le_add_of_nonneg_left (Real.sqrt_nonneg _))

private theorem norm_neumannCubeProductTest_le
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) (j : ℕ) (x : Position) :
    ‖neumannCubeProductTest ℓ b k a n j x‖ ≤
      ∏ _i : Fin 3, cubeTestFactorBound ℓ k := by
  rw [neumannCubeProductTest, translatedProductTest, norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => by
    simpa only [ite_apply] using compact_test_factor_le_bound ℓ k a n j i (x i - b i)

theorem norm_neumannCubeMixedTestLimit_le
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) (x : Position) :
    ‖neumannCubeMixedTestLimit ℓ b k a n x‖ ≤
      ∏ _i : Fin 3, cubeTestFactorBound ℓ k := by
  unfold neumannCubeMixedTestLimit
  rw [norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  by_cases hia : i = a
  · simp only [hia, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_dirichletIntervalMode_le ℓ n _).trans <|
      le_add_of_nonneg_right (Finset.sum_nonneg fun r _ =>
        neumannIntervalCoefficient_nonneg_test ℓ (k r))
  · simp only [ite_eq_right hia, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_neumannIntervalMode_le_test ℓ (k i) _).trans <|
      (Finset.single_le_sum
        (fun r _ => neumannIntervalCoefficient_nonneg_test ℓ (k r))
        (Finset.mem_univ i)).trans (le_add_of_nonneg_left (Real.sqrt_nonneg _))

theorem contDiff_neumannCubeMixedTestLimit
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) :
    ContDiff ℝ ∞ (neumannCubeMixedTestLimit ℓ b k a n) := by
  rw [show neumannCubeMixedTestLimit ℓ b k a n = translatedProductTest b
      (fun i => if i = a then fun x => (dirichletIntervalMode ℓ n x : ℂ)
        else fun x => (neumannIntervalMode ℓ (k i) x : ℂ)) by
      funext x
      simp only [neumannCubeMixedTestLimit, translatedProductTest, ite_apply]]
  apply contDiff_translatedProductTest
  intro i
  by_cases hia : i = a
  · simp only [hia, ↓reduceIte]
    apply Complex.ofRealCLM.contDiff.comp
    exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))
  · simp only [ite_eq_right hia]
    apply Complex.ofRealCLM.contDiff.comp
    exact contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))

theorem neumannCubeMixedTestLimit_memLp
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) :
    MemLp (neumannCubeMixedTestLimit ℓ b k a n) 2
      (volume.restrict (cubeInterior b ℓ)) :=
  MemLp.of_bound (contDiff_neumannCubeMixedTestLimit ℓ b k a n).continuous.aestronglyMeasurable
    (∏ _i : Fin 3, cubeTestFactorBound ℓ k)
    (Eventually.of_forall (norm_neumannCubeMixedTestLimit_le ℓ b k a n))

noncomputable def neumannCubeMixedTestLimitL2
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) : RegionState Position ℂ (cubeInterior b ℓ) :=
  (neumannCubeMixedTestLimit_memLp ℓ b k a n).toLp
    (neumannCubeMixedTestLimit ℓ b k a n)

theorem tendsto_localL2_neumannCubeProductTest
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) :
    Tendsto (fun j => localTestFunctionL2 (cubeInterior b ℓ)
      (neumannCubeProductTest ℓ b k a n j)
      (hasCompactSupport_neumannCubeProductTest ℓ b k a n j)
      (contDiff_neumannCubeProductTest ℓ b k a n j)) atTop
      (𝓝 (neumannCubeMixedTestLimitL2 ℓ b k a n)) := by
  let hg := neumannCubeMixedTestLimit_memLp ℓ b k a n
  have hf (j : ℕ) : MemLp (neumannCubeProductTest ℓ b k a n j) 2
      (volume.restrict (cubeInterior b ℓ)) :=
    ((contDiff_neumannCubeProductTest ℓ b k a n j).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_neumannCubeProductTest ℓ b k a n j)).restrict _
  have hlim : ∀ᵐ x ∂volume.restrict (cubeInterior b ℓ),
      Tendsto (fun j => neumannCubeProductTest ℓ b k a n j x) atTop
        (𝓝 (neumannCubeMixedTestLimit ℓ b k a n x)) := by
    filter_upwards [ae_restrict_mem (measurableSet_cubeInterior b ℓ)] with x hx
    exact tendsto_neumannCubeProductTest ℓ b k a n hx
  have ht := tendsto_complexL2_of_bounded_ae_tendsto hf hg
    (∏ _i : Fin 3, cubeTestFactorBound ℓ k)
    (fun j => Eventually.of_forall (norm_neumannCubeProductTest_le ℓ b k a n j))
    (Eventually.of_forall (norm_neumannCubeMixedTestLimit_le ℓ b k a n)) hlim
  simpa only [localTestFunctionL2, neumannCubeMixedTestLimitL2] using ht

theorem contDiff_neumannCubeMixedDerivativeLimit
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) :
    ContDiff ℝ ∞ (neumannCubeMixedDerivativeLimit ℓ b k a n) := by
  unfold neumannCubeMixedDerivativeLimit
  apply ContDiff.mul
  · apply contDiff_prod
    intro i hi
    apply Complex.ofRealCLM.contDiff.comp
    exact contDiff_const.mul (Real.contDiff_cos.comp
      (contDiff_const.mul ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).contDiff.sub
        contDiff_const)))
  · have hscalar : ContDiff ℝ ∞
        (fun t : ℝ => (dirichletIntervalMode ℓ n t : ℂ)) := by
      apply Complex.ofRealCLM.contDiff.comp
      exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))
    have hderiv : ContDiff ℝ ∞
        (fun t : ℝ => fderiv ℝ (fun y => (dirichletIntervalMode ℓ n y : ℂ)) t 1) :=
      (hscalar.fderiv_right (n := ∞) (by simp)).clm_apply contDiff_const
    exact hderiv.comp
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) a).contDiff.sub contDiff_const)

private noncomputable def cubeTestDerivativeBound (ℓ : {ℓ : ℝ // 0 < ℓ})
    (k : Fin 3 → ℕ) (a : Fin 3) (n : ℕ+) (M : ℝ) : ℝ :=
  (∏ _i ∈ Finset.univ.erase a, cubeTestFactorBound ℓ k) *
    (Real.sqrt (2 / ℓ.val) * intervalFrequency ℓ n +
      4 * M * (Real.sqrt (2 / ℓ.val) * intervalFrequency ℓ n))

private theorem norm_neumannCubeMixedDerivativeLimit_le
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) (M : ℝ) (hM : 0 ≤ M) (x : Position) :
    ‖neumannCubeMixedDerivativeLimit ℓ b k a n x‖ ≤
      cubeTestDerivativeBound ℓ k a n M := by
  unfold neumannCubeMixedDerivativeLimit cubeTestDerivativeBound
  rw [norm_mul, norm_prod]
  apply mul_le_mul
  · apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro i hi
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_neumannIntervalMode_le_test ℓ (k i) _).trans <|
      (Finset.single_le_sum
        (fun r _ => neumannIntervalCoefficient_nonneg_test ℓ (k r))
        (Finset.mem_univ i)).trans (le_add_of_nonneg_left (Real.sqrt_nonneg _))
  · rw [fderiv_dirichletIntervalMode_ofReal, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (intervalFrequency_nonneg ℓ n)]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    have hc := abs_neumannIntervalMode_le_test ℓ (n : ℕ) (x a - b a)
    have he : neumannIntervalCoefficient ℓ (n : ℕ) = Real.sqrt (2 / ℓ.val) := by
      simp [neumannIntervalCoefficient]
    rw [he] at hc
    have hnonneg : 0 ≤ 4 * M *
        (Real.sqrt (2 / ℓ.val) * intervalFrequency ℓ n) :=
      mul_nonneg (mul_nonneg (by norm_num) hM)
        (mul_nonneg (Real.sqrt_nonneg _) (intervalFrequency_nonneg ℓ n))
    calc
      _ ≤ Real.sqrt (2 / ℓ.val) * intervalFrequency ℓ n := by
        simpa only [mul_comm] using
          (mul_le_mul_of_nonneg_left hc (intervalFrequency_nonneg ℓ n))
      _ ≤ _ := le_add_of_nonneg_right hnonneg
  · exact norm_nonneg _
  · exact Finset.prod_nonneg fun _ _ => cubeTestFactorBound_nonneg ℓ k

theorem neumannCubeMixedDerivativeLimit_memLp
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) :
    MemLp (neumannCubeMixedDerivativeLimit ℓ b k a n) 2
      (volume.restrict (cubeInterior b ℓ)) := by
  obtain ⟨M, hM, -⟩ := exists_pos_bound_deriv_smoothTransition
  exact MemLp.of_bound
    (contDiff_neumannCubeMixedDerivativeLimit ℓ b k a n).continuous.aestronglyMeasurable
    (cubeTestDerivativeBound ℓ k a n M)
    (Eventually.of_forall (norm_neumannCubeMixedDerivativeLimit_le ℓ b k a n M hM.le))

noncomputable def neumannCubeMixedDerivativeLimitL2
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) : RegionState Position ℂ (cubeInterior b ℓ) :=
  (neumannCubeMixedDerivativeLimit_memLp ℓ b k a n).toLp
    (neumannCubeMixedDerivativeLimit ℓ b k a n)

theorem tendsto_localL2_fderiv_neumannCubeProductTest
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) :
    Tendsto (fun j => localTestFunctionL2 (cubeInterior b ℓ)
      (fun x => fderiv ℝ (neumannCubeProductTest ℓ b k a n j) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a))
      ((hasCompactSupport_neumannCubeProductTest ℓ b k a n j).fderiv_apply ℝ
        (EuclideanSpace.basisFun (Fin 3) ℝ a))
      (((contDiff_neumannCubeProductTest ℓ b k a n j).fderiv_right (n := ∞)
        (by simp)).clm_apply
        contDiff_const)) atTop
      (𝓝 (neumannCubeMixedDerivativeLimitL2 ℓ b k a n)) := by
  obtain ⟨M, hM, hderiv⟩ := exists_pos_bound_deriv_smoothTransition
  let B := cubeTestDerivativeBound ℓ k a n M
  have hsmooth (j : ℕ) : ContDiff ℝ ∞
      (fun x => fderiv ℝ (neumannCubeProductTest ℓ b k a n j) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a)) :=
    (((contDiff_neumannCubeProductTest ℓ b k a n j).fderiv_right (n := ∞)
      (by simp)).clm_apply contDiff_const)
  have hf (j : ℕ) : MemLp (fun x => fderiv ℝ
      (neumannCubeProductTest ℓ b k a n j) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a)) 2
      (volume.restrict (cubeInterior b ℓ)) :=
    ((hsmooth j).continuous.memLp_of_hasCompactSupport
      (μ := (volume : Measure Position))
      ((hasCompactSupport_neumannCubeProductTest ℓ b k a n j).fderiv_apply ℝ _)).restrict _
  have hseq (j : ℕ) : ∀ᵐ x ∂volume.restrict (cubeInterior b ℓ),
      ‖fderiv ℝ (neumannCubeProductTest ℓ b k a n j) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a)‖ ≤ B := by
    filter_upwards [ae_restrict_mem (measurableSet_cubeInterior b ℓ)] with x hx
    rw [fderiv_neumannCubeProductTest_apply_basis, norm_mul, norm_prod]
    apply mul_le_mul
    · apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i hi
      have hia : i ≠ a := Finset.ne_of_mem_erase hi
      simpa only [ite_eq_right hia] using
        compact_test_factor_le_bound ℓ k a n j i (x i - b i)
    · exact norm_fderiv_compactDirichletMode_le ℓ n hM.le
        (fun z => by simpa only [Real.norm_eq_abs] using hderiv z) j
        ⟨by linarith [(hx a).1], by linarith [(hx a).2]⟩
    · exact norm_nonneg _
    · exact Finset.prod_nonneg fun _ _ => cubeTestFactorBound_nonneg ℓ k
  have hlim : ∀ᵐ x ∂volume.restrict (cubeInterior b ℓ), Tendsto
      (fun j => fderiv ℝ (neumannCubeProductTest ℓ b k a n j) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a)) atTop
      (𝓝 (neumannCubeMixedDerivativeLimit ℓ b k a n x)) := by
    filter_upwards [ae_restrict_mem (measurableSet_cubeInterior b ℓ)] with x hx
    exact tendsto_fderiv_neumannCubeProductTest ℓ b k a n hx
  have ht := tendsto_complexL2_of_bounded_ae_tendsto hf
    (neumannCubeMixedDerivativeLimit_memLp ℓ b k a n) B hseq
    (Eventually.of_forall
      (norm_neumannCubeMixedDerivativeLimit_le ℓ b k a n M hM.le)) hlim
  simpa only [localTestFunctionL2, neumannCubeMixedDerivativeLimitL2] using ht

end LiebThirring.TFCubes

end
