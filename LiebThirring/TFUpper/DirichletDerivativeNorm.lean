/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.DirichletKineticApprox
import LiebThirring.TFCubes.CubeCoordinates
import LiebThirring.TFCubes.CubeSpin
import Mathlib.Tactic

/-! # The classical derivative norm of one literal Dirichlet product

The active factor is the normalized cosine and every other factor is the
normalized sine. Physical volume and Fubini give exactly the squared active
frequency. No basis completeness is involved. Proof: cube spectral theory, Lieb–Simon (1977) III.11.
-/

public section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace LiebThirring.TFUpper
open TFCubes

private noncomputable def derivativeIntervalFactor (ℓ : {ℓ : ℝ // 0 < ℓ})
    (k : Fin 3 → ℕ+) (a i : Fin 3) (t : ℝ) : ℝ :=
  if i = a then neumannIntervalMode ℓ (k i : ℕ) t else dirichletIntervalMode ℓ (k i) t

private theorem abs_derivativeIntervalFactor_le (ℓ : {ℓ : ℝ // 0 < ℓ})
    (k : Fin 3 → ℕ+) (a i : Fin 3) (t : ℝ) :
    |derivativeIntervalFactor ℓ k a i t| ≤ Real.sqrt (2 / ℓ.val) := by
  unfold derivativeIntervalFactor
  split_ifs
  · rw [neumannIntervalMode, neumannIntervalCoefficient, ite_eq_right (k i).ne_zero,
      abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
      (Real.sqrt_nonneg _)).trans_eq (mul_one _)
  · exact abs_dirichletIntervalMode_le ℓ _ _

private theorem integral_derivativeIntervalFactor_sq (ℓ : {ℓ : ℝ // 0 < ℓ})
    (k : Fin 3 → ℕ+) (a i : Fin 3) :
    ∫ t in Ioo 0 ℓ.val, derivativeIntervalFactor ℓ k a i t ^ 2 = 1 := by
  unfold derivativeIntervalFactor
  split_ifs
  · rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le ℓ.property.le, integral_neumannIntervalMode_sq]
  · rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le ℓ.property.le, integral_dirichletIntervalMode_sq]

private theorem dirichletCubeDerivativeValue_eq_single {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (p : DirichletCubeModeIndex q)
    (a : Fin 3) (x : Position) :
    dirichletCubeDerivativeValue ℓ b p a x = EuclideanSpace.single p.2
      ((intervalFrequency ℓ (p.1 a) : ℂ) *
        ∏ i : Fin 3, (derivativeIntervalFactor ℓ p.1 a i (x i - b i) : ℂ)) := by
  have hp : (∏ i : Fin 3,
      (derivativeIntervalFactor ℓ p.1 a i (x i - b i) : ℂ)) =
      (neumannIntervalMode ℓ (p.1 a : ℕ) (x a - b a) : ℂ) *
        ∏ i ∈ Finset.univ.erase a,
          (dirichletIntervalMode ℓ (p.1 i) (x i - b i) : ℂ) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
    simp only [derivativeIntervalFactor, ite_true]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_erase] at hi
    simp only [ite_eq_right hi.1]
  apply PiLp.ext
  intro s
  simp only [dirichletCubeDerivativeValue, PiLp.toLp_apply, PiLp.single_apply,
    hp, mul_assoc]

private theorem continuous_dirichletCubeDerivativeValue {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (p : DirichletCubeModeIndex q)
    (a : Fin 3) : Continuous (dirichletCubeDerivativeValue ℓ b p a) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin q => ℂ)).comp
  apply continuous_pi
  intro s
  split_ifs
  · apply Continuous.mul
    · exact continuous_const.mul (Complex.continuous_ofReal.comp
        ((continuous_neumannIntervalMode ℓ _).comp (by fun_prop)))
    · apply continuous_finsetProd
      intro i _
      exact Complex.continuous_ofReal.comp
        ((continuous_dirichletIntervalMode ℓ _).comp (by fun_prop))
  · exact continuous_const

theorem memLp_dirichletCubeDerivativeValue {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (p : DirichletCubeModeIndex q)
    (a : Fin 3) : MemLp (dirichletCubeDerivativeValue ℓ b p a) 2
      (volume.restrict (cubeInterior b ℓ)) := by
  apply MemLp.of_bound (continuous_dirichletCubeDerivativeValue ℓ b p a).aestronglyMeasurable
    (intervalFrequency ℓ (p.1 a) * ∏ _i : Fin 3, Real.sqrt (2 / ℓ.val))
  apply Filter.Eventually.of_forall
  intro x
  rw [dirichletCubeDerivativeValue_eq_single, PiLp.norm_single, norm_mul, norm_prod,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (intervalFrequency_nonneg ℓ _)]
  apply mul_le_mul_of_nonneg_left _ (intervalFrequency_nonneg ℓ _)
  simp only [Complex.norm_real, Real.norm_eq_abs]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ =>
    abs_derivativeIntervalFactor_le ℓ p.1 a i _

theorem norm_toLp_dirichletCubeDerivativeValue_sq {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (p : DirichletCubeModeIndex q)
    (a : Fin 3) :
    ‖(memLp_dirichletCubeDerivativeValue ℓ b p a).toLp
      (dirichletCubeDerivativeValue ℓ b p a)‖ ^ 2 = intervalFrequency ℓ (p.1 a) ^ 2 := by
  rw [norm_sq_localL2]
  trans ∫ x, ‖dirichletCubeDerivativeValue ℓ b p a x‖ ^ 2
    ∂(volume.restrict (cubeInterior b ℓ))
  · exact integral_congr_ae ((memLp_dirichletCubeDerivativeValue ℓ b p a).coeFn_toLp.fun_comp
      (fun z => ‖z‖ ^ 2))
  rw [← (measurePreserving_cubeFromCoordinates_restrict b ℓ).integral_comp
    (cubeCoordinateEquiv b).symm.measurableEmbedding]
  simp only [dirichletCubeDerivativeValue_eq_single, PiLp.norm_single, norm_mul, norm_prod,
    cubeFromCoordinates, PiLp.add_apply, add_sub_cancel_right,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, ← Finset.prod_pow, sq_abs]
  rw [integral_const_mul]
  unfold cubeCoordinateMeasure
  rw [integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (μ := fun _ : Fin 3 => volume.restrict (Ioo 0 ℓ.val))
    (fun i t => derivativeIntervalFactor ℓ p.1 a i t ^ 2)]
  simp only [integral_derivativeIntervalFactor_sq, Finset.prod_const, one_pow, mul_one]

theorem sum_norm_toLp_dirichletCubeDerivativeValue_sq {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (p : DirichletCubeModeIndex q) :
    (∑ a : Fin 3, ‖(memLp_dirichletCubeDerivativeValue ℓ b p a).toLp
      (dirichletCubeDerivativeValue ℓ b p a)‖ ^ 2) = dirichletCubeEigenvalue ℓ p := by
  simp only [norm_toLp_dirichletCubeDerivativeValue_sq, dirichletCubeEigenvalue]

end LiebThirring.TFUpper
end
