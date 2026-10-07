/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeModes
public import LiebThirring.TFCubes.IntervalCutoffDerivative
public import LiebThirring.TFCubes.IntervalCutoffConvergence
import Mathlib.Tactic

/-! # Compact smooth product tests on a translated cube -/

@[expose] public section

open Set
open scoped BigOperators ContDiff Topology

namespace LiebThirring.TFCubes

/-- The product of three one-dimensional tests, translated to the cube with corner `b`. -/
noncomputable def translatedProductTest (b : Position) (f : Fin 3 → ℝ → ℂ)
    (x : Position) : ℂ :=
  ∏ i : Fin 3, f i (x i - b i)

theorem contDiff_translatedProductTest (b : Position) (f : Fin 3 → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    ContDiff ℝ ∞ (translatedProductTest b f) := by
  unfold translatedProductTest
  fun_prop

/-- A translated coordinate factor differentiates only in its own coordinate. -/
theorem fderiv_translatedCoordinate_apply_basis
    (b : Position) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (i a : Fin 3) (x : Position) :
    fderiv ℝ (fun y : Position => f (y i - b i)) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a) =
      if i = a then fderiv ℝ f (x i - b i) 1 else 0 := by
  let P : Position →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i
  have hc : HasFDerivAt (fun y : Position => y i - b i) P x := by
    simpa only [P, PiLp.proj_apply] using P.hasFDerivAt.sub_const (b i)
  have h := (((hf.differentiable (by simp)).differentiableAt).hasFDerivAt.comp x hc).fderiv
  have h' : fderiv ℝ (fun y : Position => f (y i - b i)) x =
      (fderiv ℝ f (x i - b i)).comp P := h
  rw [h']
  by_cases hia : i = a
  · subst i
    simp [P]
  · simp [P, hia]

/-- Directional derivative of a translated finite product along a coordinate vector. -/
theorem fderiv_translatedProductTest_apply_basis
    (b : Position) (f : Fin 3 → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (a : Fin 3) (x : Position) :
    fderiv ℝ (translatedProductTest b f) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a) =
      (∏ i ∈ Finset.univ.erase a, f i (x i - b i)) *
        fderiv ℝ (f a) (x a - b a) 1 := by
  unfold translatedProductTest
  have hdiff (i : Fin 3) : Differentiable ℝ (fun y : Position => f i (y i - b i)) :=
    (((hf i).comp ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).contDiff.sub
      contDiff_const)).differentiable (by simp))
  have hd := fderiv_finsetProd (𝕜 := ℝ) (u := Finset.univ)
    (g := fun (i : Fin 3) (y : Position) => f i (y i - b i))
    (fun i _ => (hdiff i).differentiableAt) (x := x)
  rw [hd]
  change (∑ i ∈ Finset.univ, (∏ j ∈ Finset.univ.erase i, f j (x j - b j)) *
      fderiv ℝ (fun y : Position => f i (y i - b i)) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a)) = _
  rw [Finset.sum_eq_single a]
  · rw [fderiv_translatedCoordinate_apply_basis b (f := f a) (hf a) a a x]
    simp
  · intro i _ hia
    rw [fderiv_translatedCoordinate_apply_basis b (f := f i) (hf i) i a x]
    simp [hia]
  · simp

theorem hasCompactSupport_translatedProductTest (b : Position) (f : Fin 3 → ℝ → ℂ)
    (hf : ∀ i, HasCompactSupport (f i)) :
    HasCompactSupport (translatedProductTest b f) := by
  let K : Fin 3 → Set ℝ := fun i => (fun t : ℝ => t + b i) '' tsupport (f i)
  let P : Set (Fin 3 → ℝ) := Set.pi Set.univ K
  let C : Set Position := WithLp.toLp 2 '' P
  have hK : ∀ i, IsCompact (K i) := fun i => (hf i).image (by fun_prop)
  have hP : IsCompact P := isCompact_univ_pi hK
  have hC : IsCompact C := hP.image (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ))
  apply HasCompactSupport.intro hC
  intro x hx
  have hx' : ¬ ∀ i, x i ∈ K i := by
    intro hall
    apply hx
    refine ⟨fun i => x i, ?_, ?_⟩
    · exact Set.mem_pi.mpr fun i _ => hall i
    · apply PiLp.ext
      intro i
      rfl
  push Not at hx'
  obtain ⟨i, hi⟩ := hx'
  have hzero : f i (x i - b i) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hi
    refine ⟨x i - b i, hmem, ?_⟩
    ring
  exact Finset.prod_eq_zero (f := fun i => f i (x i - b i))
    (Finset.mem_univ i) hzero

theorem tsupport_translatedProductTest_subset_cubeInterior
    (b : Position) (ℓ : {ℓ : ℝ // 0 < ℓ}) (f : Fin 3 → ℝ → ℂ)
    (hf : ∀ i, tsupport (f i) ⊆ Ioo 0 ℓ.val) :
    tsupport (translatedProductTest b f) ⊆ cubeInterior b ℓ := by
  let K : Set Position := {x | ∀ i, x i - b i ∈ tsupport (f i)}
  have hKclosed : IsClosed K := by
    rw [show K = ⋂ i : Fin 3,
        (fun x : Position => x i - b i) ⁻¹' tsupport (f i) by
      ext x
      simp [K]]
    exact isClosed_iInter fun i => (isClosed_tsupport (f i)).preimage (by fun_prop)
  have hsupp : Function.support (translatedProductTest b f) ⊆ K := by
    intro x hx i
    apply subset_tsupport
    intro hz
    apply hx
    exact Finset.prod_eq_zero (f := fun i => f i (x i - b i))
      (Finset.mem_univ i) hz
  have ht : tsupport (translatedProductTest b f) ⊆ K :=
    closure_minimal hsupp hKclosed
  intro x hx i
  have hi := hf i (ht hx i)
  exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

/-- A compactly supported cosine factor for spectator coordinates. -/
noncomputable def compactNeumannFactor (ℓ : {ℓ : ℝ // 0 < ℓ})
    (n j : ℕ) (x : ℝ) : ℂ :=
  intervalInteriorCutoff ℓ j x * neumannIntervalMode ℓ n x

theorem contDiff_compactNeumannFactor (ℓ : {ℓ : ℝ // 0 < ℓ}) (n j : ℕ) :
    ContDiff ℝ ∞ (compactNeumannFactor ℓ n j) := by
  unfold compactNeumannFactor
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_intervalInteriorCutoff ℓ j)).mul
    (Complex.ofRealCLM.contDiff.comp (by
      exact contDiff_const.mul
        (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))))

theorem hasCompactSupport_compactNeumannFactor
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (n j : ℕ) :
    HasCompactSupport (compactNeumannFactor ℓ n j) :=
  ((hasCompactSupport_intervalInteriorCutoff ℓ j).comp_left Complex.ofReal_zero).mul_right

theorem tsupport_compactNeumannFactor_subset_Ioo
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (n j : ℕ) :
    tsupport (compactNeumannFactor ℓ n j) ⊆ Ioo 0 ℓ.val := by
  refine tsupport_mul_subset_left.trans ?_
  refine (closure_mono ?_).trans (tsupport_intervalInteriorCutoff_subset_Ioo ℓ j)
  intro x hx
  simpa only [Function.mem_support, Ne, Complex.ofReal_eq_zero] using hx

/-- The compact product test used to extract a Neumann coefficient in coordinate `a`.
The active factor is a compact sine test. -/
noncomputable def neumannCubeProductTest (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (k : Fin 3 → ℕ) (a : Fin 3) (n : ℕ+) (j : ℕ) (x : Position) : ℂ :=
  translatedProductTest b (fun i => if i = a then compactDirichletMode ℓ n j
    else compactNeumannFactor ℓ (k i) j) x

theorem contDiff_neumannCubeProductTest (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (k : Fin 3 → ℕ) (a : Fin 3) (n : ℕ+) (j : ℕ) :
    ContDiff ℝ ∞ (neumannCubeProductTest ℓ b k a n j) := by
  unfold neumannCubeProductTest
  apply contDiff_translatedProductTest
  intro i
  split_ifs
  · exact contDiff_compactDirichletMode ℓ n j
  · exact contDiff_compactNeumannFactor ℓ (k i) j

theorem hasCompactSupport_neumannCubeProductTest (ℓ : {ℓ : ℝ // 0 < ℓ})
    (b : Position) (k : Fin 3 → ℕ) (a : Fin 3) (n : ℕ+) (j : ℕ) :
    HasCompactSupport (neumannCubeProductTest ℓ b k a n j) := by
  unfold neumannCubeProductTest
  apply hasCompactSupport_translatedProductTest
  intro i
  split_ifs
  · exact hasCompactSupport_compactDirichletMode ℓ n j
  · exact hasCompactSupport_compactNeumannFactor ℓ (k i) j

theorem tsupport_neumannCubeProductTest_subset_cubeInterior
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) (j : ℕ) :
    tsupport (neumannCubeProductTest ℓ b k a n j) ⊆ cubeInterior b ℓ := by
  unfold neumannCubeProductTest
  apply tsupport_translatedProductTest_subset_cubeInterior
  intro i
  split_ifs
  · exact tsupport_compactDirichletMode_subset_Ioo ℓ n j
  · exact tsupport_compactNeumannFactor_subset_Ioo ℓ (k i) j

/-- Only the active compact sine factor is differentiated in its coordinate direction. -/
theorem fderiv_neumannCubeProductTest_apply_basis
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) (j : ℕ) (x : Position) :
    fderiv ℝ (neumannCubeProductTest ℓ b k a n j) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a) =
      (∏ i ∈ Finset.univ.erase a, compactNeumannFactor ℓ (k i) j (x i - b i)) *
        fderiv ℝ (compactDirichletMode ℓ n j) (x a - b a) 1 := by
  unfold neumannCubeProductTest
  rw [fderiv_translatedProductTest_apply_basis]
  simp only [ite_true]
  · congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hia : i ≠ a := Finset.ne_of_mem_erase hi
    simp [hia]
  · intro i
    by_cases hia : i = a
    · simp [hia, contDiff_compactDirichletMode]
    · simp [hia, contDiff_compactNeumannFactor]

/-- The mixed sine/cosine product approached by the compact Neumann tests. -/
noncomputable def neumannCubeMixedTestLimit (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (k : Fin 3 → ℕ) (a : Fin 3) (n : ℕ+) (x : Position) : ℂ :=
  ∏ i : Fin 3, if i = a then (dirichletIntervalMode ℓ n (x i - b i) : ℂ)
    else (neumannIntervalMode ℓ (k i) (x i - b i) : ℂ)

/-- At every interior point, the compact product tests eventually agree with their
mixed sine/cosine limit. -/
theorem eventually_neumannCubeProductTest_eq
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) {x : Position} (hx : x ∈ cubeInterior b ℓ) :
    ∀ᶠ j in Filter.atTop,
      neumannCubeProductTest ℓ b k a n j x = neumannCubeMixedTestLimit ℓ b k a n x := by
  have hall : ∀ᶠ j in Filter.atTop, ∀ i : Fin 3,
      (if i = a then compactDirichletMode ℓ n j (x i - b i)
        else compactNeumannFactor ℓ (k i) j (x i - b i)) =
      (if i = a then (dirichletIntervalMode ℓ n (x i - b i) : ℂ)
        else (neumannIntervalMode ℓ (k i) (x i - b i) : ℂ)) := by
    apply Filter.eventually_all.mpr
    intro i
    have hxi : x i - b i ∈ Ioo 0 ℓ.val := by
      exact ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
    by_cases hia : i = a
    · subst i
      filter_upwards [eventually_compactDirichletMode_eq_nhds ℓ n hxi] with j hj
      simpa using hj.self_of_nhds
    ·
      filter_upwards [eventually_intervalInteriorCutoff_eq_one_nhds ℓ hxi] with j hj
      have hc := hj.self_of_nhds
      simpa [hia, compactNeumannFactor] using
        congrArg (fun c : ℝ => (c : ℂ) *
          neumannIntervalMode ℓ (k i) (x i - b i)) hc
  filter_upwards [hall] with j hj
  unfold neumannCubeProductTest translatedProductTest neumannCubeMixedTestLimit
  exact Finset.prod_congr rfl fun i _ => by simpa only [ite_apply] using hj i

theorem tendsto_neumannCubeProductTest
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) {x : Position} (hx : x ∈ cubeInterior b ℓ) :
    Filter.Tendsto (fun j => neumannCubeProductTest ℓ b k a n j x) Filter.atTop
      (𝓝 (neumannCubeMixedTestLimit ℓ b k a n x)) := by
  have he : (fun j => neumannCubeProductTest ℓ b k a n j x) =ᶠ[Filter.atTop]
      (fun _ => neumannCubeMixedTestLimit ℓ b k a n x) :=
    eventually_neumannCubeProductTest_eq ℓ b k a n hx
  exact tendsto_const_nhds.congr' he.symm

/-- The directional derivative limit of the mixed product test. -/
noncomputable def neumannCubeMixedDerivativeLimit
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) (x : Position) : ℂ :=
  (∏ i ∈ Finset.univ.erase a,
      (neumannIntervalMode ℓ (k i) (x i - b i) : ℂ)) *
    fderiv ℝ (fun y => (dirichletIntervalMode ℓ n y : ℂ)) (x a - b a) 1

theorem eventually_fderiv_neumannCubeProductTest_eq
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) {x : Position} (hx : x ∈ cubeInterior b ℓ) :
    ∀ᶠ j in Filter.atTop,
      fderiv ℝ (neumannCubeProductTest ℓ b k a n j) x
          (EuclideanSpace.basisFun (Fin 3) ℝ a) =
        neumannCubeMixedDerivativeLimit ℓ b k a n x := by
  have hxa : x a - b a ∈ Ioo 0 ℓ.val :=
    ⟨by linarith [(hx a).1], by linarith [(hx a).2]⟩
  have hspectator : ∀ᶠ j in Filter.atTop, ∀ i : Fin 3, i ≠ a →
      compactNeumannFactor ℓ (k i) j (x i - b i) =
        (neumannIntervalMode ℓ (k i) (x i - b i) : ℂ) := by
    apply Filter.eventually_all.mpr
    intro i
    have hxi : x i - b i ∈ Ioo 0 ℓ.val :=
      ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
    filter_upwards [eventually_intervalInteriorCutoff_eq_one_nhds ℓ hxi] with j hj
    intro hia
    simp [compactNeumannFactor, hj.self_of_nhds]
  filter_upwards [hspectator,
    eventually_compactDirichletMode_eq_nhds ℓ n hxa] with j hj hactive
  rw [fderiv_neumannCubeProductTest_apply_basis]
  unfold neumannCubeMixedDerivativeLimit
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact hj i (Finset.ne_of_mem_erase hi)
  · exact congrArg (fun L : ℝ →L[ℝ] ℂ => L 1) hactive.fderiv_eq

theorem tendsto_fderiv_neumannCubeProductTest
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position) (k : Fin 3 → ℕ)
    (a : Fin 3) (n : ℕ+) {x : Position} (hx : x ∈ cubeInterior b ℓ) :
    Filter.Tendsto (fun j => fderiv ℝ (neumannCubeProductTest ℓ b k a n j) x
      (EuclideanSpace.basisFun (Fin 3) ℝ a)) Filter.atTop
      (𝓝 (neumannCubeMixedDerivativeLimit ℓ b k a n x)) := by
  have he : (fun j => fderiv ℝ (neumannCubeProductTest ℓ b k a n j) x
      (EuclideanSpace.basisFun (Fin 3) ℝ a)) =ᶠ[Filter.atTop]
      (fun _ => neumannCubeMixedDerivativeLimit ℓ b k a n x) :=
    eventually_fderiv_neumannCubeProductTest_eq ℓ b k a n hx
  exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)

end LiebThirring.TFCubes

end
