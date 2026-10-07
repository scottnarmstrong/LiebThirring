/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeModes
public import LiebThirring.TFCubes.IntervalCutoffEstimates
public import LiebThirring.TFCubes.IntervalCutoffConvergence
public import LiebThirring.TFCubes.IntervalDominatedConvergence
public import LiebThirring.TFCubes.IntervalModeDerivatives

/-!
# Compact smooth approximations to a Dirichlet cube orbital

The same interior cutoff is applied to the three normalized sine factors.
These literal compact smooth products will transport the one cube mode through
the closed global weak-derivative graph. Proof: explicit cube spectral calculations,
explicit product-density argument.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ContDiff Topology SchwartzMap

namespace LiebThirring.TFUpper

noncomputable def dirichletTranslatedProductTest (b : Position) (f : Fin 3 → ℝ → ℂ)
    (x : Position) : ℂ := ∏ i : Fin 3, f i (x i - b i)

theorem contDiff_dirichletTranslatedProductTest (b : Position) (f : Fin 3 → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    ContDiff ℝ ∞ (dirichletTranslatedProductTest b f) := by
  unfold dirichletTranslatedProductTest
  fun_prop

theorem hasCompactSupport_dirichletTranslatedProductTest
    (b : Position) (f : Fin 3 → ℝ → ℂ) (hf : ∀ i, HasCompactSupport (f i)) :
    HasCompactSupport (dirichletTranslatedProductTest b f) := by
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
    refine ⟨fun i => x i, Set.mem_pi.mpr fun i _ => hall i, ?_⟩
    apply PiLp.ext
    intro i
    rfl
  push Not at hx'
  obtain ⟨i, hi⟩ := hx'
  apply Finset.prod_eq_zero (f := fun i => f i (x i - b i)) (Finset.mem_univ i)
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  apply hi
  exact ⟨x i - b i, hmem, by ring⟩

/-- Compactly supported sine product with its fixed spin vector. -/
noncomputable def dirichletCubeApproxValue {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (k : ℕ)
    (x : Position) : EuclideanSpace ℂ (Fin q) :=
  EuclideanSpace.single p.2 (dirichletTranslatedProductTest b
    (fun i => TFCubes.compactDirichletMode ℓ (p.1 i) k) x)

theorem dirichletCubeApproxValue_apply {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (k : ℕ)
    (x : Position) (s : Fin q) :
    dirichletCubeApproxValue ℓ b p k x s = if s = p.2 then
      dirichletTranslatedProductTest b
        (fun i => TFCubes.compactDirichletMode ℓ (p.1 i) k) x else 0 := by
  simp only [dirichletCubeApproxValue, PiLp.single_apply]

theorem contDiff_dirichletCubeApproxValue {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (k : ℕ) :
    ContDiff ℝ ∞ (dirichletCubeApproxValue ℓ b p k) := by
  apply (contDiff_piLp 2).mpr
  intro s
  by_cases hs : s = p.2
  · simp only [dirichletCubeApproxValue_apply, hs, ite_eq_left]
    exact contDiff_dirichletTranslatedProductTest b _ fun i =>
      TFCubes.contDiff_compactDirichletMode ℓ (p.1 i) k
  · simp only [dirichletCubeApproxValue_apply, hs]
    exact contDiff_const

theorem hasCompactSupport_dirichletCubeApproxValue {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (k : ℕ) :
    HasCompactSupport (dirichletCubeApproxValue ℓ b p k) := by
  have hscalar := hasCompactSupport_dirichletTranslatedProductTest b
    (fun i => TFCubes.compactDirichletMode ℓ (p.1 i) k)
    (fun i => TFCubes.hasCompactSupport_compactDirichletMode ℓ (p.1 i) k)
  apply HasCompactSupport.intro hscalar
  intro x hx
  apply PiLp.ext
  intro s
  rw [dirichletCubeApproxValue_apply]
  split_ifs
  · exact image_eq_zero_of_notMem_tsupport hx
  · rfl

theorem tsupport_dirichletCubeApproxValue_subset_cubeInterior {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (k : ℕ) :
    tsupport (dirichletCubeApproxValue ℓ b p k) ⊆
      TFCubes.cubeInterior b ℓ := by
  have hscalar : tsupport (dirichletTranslatedProductTest b
      (fun i => TFCubes.compactDirichletMode ℓ (p.1 i) k)) ⊆
      TFCubes.cubeInterior b ℓ := by
    let K : Set Position := {x | ∀ i,
      x i - b i ∈ tsupport (TFCubes.compactDirichletMode ℓ (p.1 i) k)}
    have hKclosed : IsClosed K := by
      rw [show K = ⋂ i : Fin 3, (fun x : Position => x i - b i) ⁻¹'
          tsupport (TFCubes.compactDirichletMode ℓ (p.1 i) k) by
        ext x
        simp [K]]
      exact isClosed_iInter fun i => (isClosed_tsupport _).preimage (by fun_prop)
    have hsupp : Function.support (dirichletTranslatedProductTest b
        (fun i => TFCubes.compactDirichletMode ℓ (p.1 i) k)) ⊆ K := by
      intro x hx i
      apply subset_tsupport
      intro hz
      apply hx
      exact Finset.prod_eq_zero (Finset.mem_univ i) hz
    intro x hx i
    have hi := TFCubes.tsupport_compactDirichletMode_subset_Ioo ℓ (p.1 i) k
      (closure_minimal hsupp hKclosed hx i)
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
  refine (closure_mono ?_).trans hscalar
  intro x hx
  change dirichletTranslatedProductTest b
    (fun i => TFCubes.compactDirichletMode ℓ (p.1 i) k) x ≠ 0
  intro hz
  apply hx
  apply PiLp.ext
  intro s
  rw [dirichletCubeApproxValue_apply, hz]
  split_ifs <;> simp

/-- The compact product, bundled as a spatial-spin Schwartz function. -/
noncomputable def dirichletCubeApproxSchwartz {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (k : ℕ) :
    𝓢(Position, EuclideanSpace ℂ (Fin q)) :=
  (hasCompactSupport_dirichletCubeApproxValue ℓ b p k).toSchwartzMap
    (contDiff_dirichletCubeApproxValue ℓ b p k)

/-- Coordinate direction in physical space. -/
noncomputable def positionCoordinateVector (a : Fin 3) : Position :=
  PiLp.single 2 a (1 : ℝ)

/-- The actual classical derivative of the compact product approximation. -/
noncomputable def dirichletCubeApproxDerivativeValue {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (a : Fin 3) (k : ℕ)
    (x : Position) : EuclideanSpace ℂ (Fin q) :=
  fderiv ℝ (dirichletCubeApproxValue ℓ b p k) x
    (positionCoordinateVector a)

/-- The literal derivative of a cube sine product in coordinate `a`. -/
noncomputable def dirichletCubeDerivativeValue {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (a : Fin 3)
    (x : Position) : EuclideanSpace ℂ (Fin q) :=
  WithLp.toLp 2 fun s => if s = p.2 then
    (TFCubes.intervalFrequency ℓ (p.1 a) : ℂ) *
      (TFCubes.neumannIntervalMode ℓ (p.1 a : ℕ) (x a - b a) : ℂ) *
      ∏ i ∈ Finset.univ.erase a,
        (TFCubes.dirichletIntervalMode ℓ (p.1 i) (x i - b i) : ℂ)
    else 0

theorem tendsto_dirichletCubeApproxValue {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) {x : Position}
    (hx : x ∈ TFCubes.cubeInterior b ℓ) :
    Tendsto (fun k => dirichletCubeApproxValue ℓ b p k x) atTop
      (𝓝 (TFCubes.dirichletCubeModeValue ℓ b p x)) := by
  have hcoord : Tendsto
      (fun k s => dirichletCubeApproxValue ℓ b p k x s) atTop
      (𝓝 (fun s => TFCubes.dirichletCubeModeValue ℓ b p x s)) := by
    apply tendsto_pi_nhds.mpr
    intro s
    rw [show (fun k => dirichletCubeApproxValue ℓ b p k x s) = fun k =>
        if s = p.2 then ∏ i : Fin 3,
          TFCubes.compactDirichletMode ℓ (p.1 i) k (x i - b i) else 0 by
      funext k
      rw [dirichletCubeApproxValue_apply]
      rfl]
    by_cases hs : s = p.2
    · simp only [hs, ite_eq_left, TFCubes.dirichletCubeModeValue_apply]
      apply tendsto_finsetProd
      intro i _
      exact TFCubes.tendsto_compactDirichletMode ℓ (p.1 i)
        ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
    · simp only [hs, TFCubes.dirichletCubeModeValue_apply]
      exact tendsto_const_nhds
  have h := ((PiLp.continuous_toLp 2 (fun _ : Fin q => ℂ)).tendsto
    (fun s => TFCubes.dirichletCubeModeValue ℓ b p x s)).comp hcoord
  convert h using 1
  · ext k s
    simp only [Function.comp_apply, PiLp.toLp_apply]

end LiebThirring.TFUpper

end
