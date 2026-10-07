/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.DirichletKineticApprox
import Mathlib.Tactic

/-! # Actual derivatives of the compact product approximants

The coordinate product rule, local convergence, and a bound independent of the
cutoff index give the inputs for convergence in the physical derivative graph.
explicit Dirichlet product construction.
-/

public section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace LiebThirring.TFUpper
open TFCubes

private theorem fderiv_translatedFactor_apply
    (b : Position) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (i a : Fin 3) (x : Position) :
    fderiv ℝ (fun y : Position => f (y i - b i)) x (positionCoordinateVector a) =
      if i = a then fderiv ℝ f (x i - b i) 1 else 0 := by
  let P : Position →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i
  have hc : HasFDerivAt (fun y : Position => y i - b i) P x := by
    simpa only [P, PiLp.proj_apply] using P.hasFDerivAt.sub_const (b i)
  have h := (((hf.differentiable (by simp)).differentiableAt).hasFDerivAt.comp x hc).fderiv
  change fderiv ℝ (fun y : Position => f (y i - b i)) x =
    (fderiv ℝ f (x i - b i)).comp P at h
  rw [h]
  by_cases hia : i = a
  · subst i
    simp [P, positionCoordinateVector]
  · simp [P, positionCoordinateVector, hia]

private theorem fderiv_dirichletTranslatedProductTest_apply
    (b : Position) (f : Fin 3 → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (a : Fin 3) (x : Position) :
    fderiv ℝ (dirichletTranslatedProductTest b f) x (positionCoordinateVector a) =
      (∏ i ∈ Finset.univ.erase a, f i (x i - b i)) *
        fderiv ℝ (f a) (x a - b a) 1 := by
  unfold dirichletTranslatedProductTest
  have hd := fderiv_finsetProd (𝕜 := ℝ) (u := Finset.univ)
    (g := fun (i : Fin 3) (y : Position) => f i (y i - b i))
    (fun i _ => ((hf i).comp (by fun_prop)).differentiable (by simp) |>.differentiableAt)
    (x := x)
  rw [hd]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  simp_rw [fderiv_translatedFactor_apply b _ (hf _) _ a x]
  rw [Finset.sum_eq_single a]
  · simp only [ite_true]
  · intro i _ hia
    simp only [ite_eq_right hia, mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

theorem dirichletCubeApproxDerivativeValue_eq {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (p : DirichletCubeModeIndex q)
    (a : Fin 3) (k : ℕ) (x : Position) :
    dirichletCubeApproxDerivativeValue ℓ b p a k x = EuclideanSpace.single p.2
      ((∏ i ∈ Finset.univ.erase a, compactDirichletMode ℓ (p.1 i) k (x i - b i)) *
        fderiv ℝ (compactDirichletMode ℓ (p.1 a) k) (x a - b a) 1) := by
  have hdiff := ((contDiff_dirichletCubeApproxValue ℓ b p k).differentiable
    (by simp)).differentiableAt (x := x)
  apply PiLp.ext
  intro s
  let P := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin q => ℂ) s
  have hproj := (P.hasFDerivAt.comp x hdiff.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => dirichletCubeApproxValue ℓ b p k y s) x =
    P.comp (fderiv ℝ (dirichletCubeApproxValue ℓ b p k) x) at hproj
  have he : (fderiv ℝ (dirichletCubeApproxValue ℓ b p k) x
      (positionCoordinateVector a)) s =
      fderiv ℝ (fun y => dirichletCubeApproxValue ℓ b p k y s) x
        (positionCoordinateVector a) := by
    rw [hproj]
    rfl
  change (fderiv ℝ (dirichletCubeApproxValue ℓ b p k) x
      (positionCoordinateVector a)) s = _
  rw [he, PiLp.single_apply]
  by_cases hs : s = p.2
  · simp only [hs, ite_true, dirichletCubeApproxValue_apply]
    change fderiv ℝ (dirichletTranslatedProductTest b
        (fun i => compactDirichletMode ℓ (p.1 i) k)) x
        (positionCoordinateVector a) = _
    exact fderiv_dirichletTranslatedProductTest_apply b _
      (fun i => contDiff_compactDirichletMode ℓ (p.1 i) k) a x
  · simp only [dirichletCubeApproxValue_apply, hs, ite_false]
    simp

private theorem fderiv_complexDirichletMode_eq (ℓ : {ℓ : ℝ // 0 < ℓ})
    (n : ℕ+) (t : ℝ) :
    fderiv ℝ (fun y => (dirichletIntervalMode ℓ n y : ℂ)) t 1 =
      (intervalFrequency ℓ n : ℂ) * (neumannIntervalMode ℓ (n : ℕ) t : ℂ) := by
  rw [fderiv_apply_one_eq_deriv, (hasDerivAt_dirichletIntervalMode ℓ n t).ofReal_comp.deriv]
  simp only [neumannIntervalMode, neumannIntervalCoefficient, ite_eq_right n.ne_zero,
    Complex.ofReal_mul]
  ring

theorem tendsto_dirichletCubeApproxDerivativeValue {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (p : DirichletCubeModeIndex q)
    (a : Fin 3) {x : Position} (hx : x ∈ cubeInterior b ℓ) :
    Tendsto (fun k => dirichletCubeApproxDerivativeValue ℓ b p a k x) atTop
      (𝓝 (dirichletCubeDerivativeValue ℓ b p a x)) := by
  have hcoord (i : Fin 3) : x i - b i ∈ Ioo 0 ℓ.val :=
    ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
  have hp : Tendsto
      (fun k => ∏ i ∈ Finset.univ.erase a,
        compactDirichletMode ℓ (p.1 i) k (x i - b i)) atTop
      (𝓝 (∏ i ∈ Finset.univ.erase a,
        (dirichletIntervalMode ℓ (p.1 i) (x i - b i) : ℂ))) :=
    tendsto_finsetProd _ (fun i _ => tendsto_compactDirichletMode ℓ (p.1 i) (hcoord i))
  have hd := tendsto_fderiv_compactDirichletMode ℓ (p.1 a) (hcoord a)
  rw [fderiv_complexDirichletMode_eq] at hd
  have hc : Continuous (fun z : ℂ => EuclideanSpace.single p.2 z) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin q => ℂ)).comp
    apply continuous_pi
    intro s
    by_cases hs : s = p.2
    · simp only [Pi.single_apply, hs, ite_true]
      exact continuous_id
    · simp only [Pi.single_apply, hs, ite_false]
      exact continuous_const
  have h := (hc.tendsto _).comp (hp.mul hd)
  convert h using 1
  · funext k
    exact dirichletCubeApproxDerivativeValue_eq ℓ b p a k x
  · congr 1
    apply PiLp.ext
    intro s
    simp only [dirichletCubeDerivativeValue, PiLp.toLp_apply, PiLp.single_apply]
    split_ifs <;> ring

/-- The compact sine factors have the same uniform bound as the uncut sine. -/
theorem norm_compactDirichletMode_le (ℓ : {ℓ : ℝ // 0 < ℓ})
    (n : ℕ+) (k : ℕ) (t : ℝ) :
    ‖compactDirichletMode ℓ n k t‖ ≤ Real.sqrt (2 / ℓ.val) := by
  simp only [compactDirichletMode, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (intervalInteriorCutoff_nonneg ℓ k t)]
  exact (mul_le_mul (intervalInteriorCutoff_le_one ℓ k t)
    (abs_dirichletIntervalMode_le ℓ n t) (abs_nonneg _) zero_le_one).trans_eq
    (one_mul _)

theorem exists_bound_dirichletCubeApproxDerivativeValue {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (p : DirichletCubeModeIndex q)
    (a : Fin 3) : ∃ B : ℝ, 0 ≤ B ∧ ∀ k, ∀ x ∈ cubeInterior b ℓ,
      ‖dirichletCubeApproxDerivativeValue ℓ b p a k x‖ ≤ B := by
  obtain ⟨M, hM, hderiv⟩ := exists_pos_bound_deriv_smoothTransition
  let C := Real.sqrt (2 / ℓ.val) * intervalFrequency ℓ (p.1 a)
  let D := C + 4 * M * C
  let A := ∏ _i ∈ Finset.univ.erase a, Real.sqrt (2 / ℓ.val)
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) (intervalFrequency_nonneg ℓ _)
  have hD : 0 ≤ D := add_nonneg hC
    (mul_nonneg (mul_nonneg (by norm_num) hM.le) hC)
  have hA : 0 ≤ A := Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _
  refine ⟨A * D, mul_nonneg hA hD, ?_⟩
  intro k x hx
  rw [dirichletCubeApproxDerivativeValue_eq, PiLp.norm_single, norm_mul, norm_prod]
  have hp : (∏ i ∈ Finset.univ.erase a,
      ‖compactDirichletMode ℓ (p.1 i) k (x i - b i)‖) ≤ A :=
    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ =>
      norm_compactDirichletMode_le ℓ (p.1 i) k _
  have hd : ‖fderiv ℝ (compactDirichletMode ℓ (p.1 a) k) (x a - b a) 1‖ ≤ D :=
    norm_fderiv_compactDirichletMode_le ℓ (p.1 a) hM.le
      (fun z => by simpa only [Real.norm_eq_abs] using hderiv z) k
      ⟨by linarith [(hx a).1], by linarith [(hx a).2]⟩
  exact mul_le_mul hp hd (norm_nonneg _) hA

end LiebThirring.TFUpper
end
