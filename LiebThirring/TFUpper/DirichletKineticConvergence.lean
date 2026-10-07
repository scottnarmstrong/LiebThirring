/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFUpper.DirichletOrbitals
public import LiebThirring.TFUpper.DirichletApproxDerivative
public import LiebThirring.TFUpper.DirichletDerivativeNorm

/-!
# L2 convergence tools for a single Dirichlet cube mode

This file isolates the vector-valued dominated-convergence step used to pass
the compact product tests to the zero-extended sine product in the global weak
derivative graph. Proof: explicit cube spectral calculations, explicit product
density argument.
-/

public section

open MeasureTheory Filter LineDeriv
open scoped Topology SchwartzMap

namespace LiebThirring.TFUpper

theorem norm_complexHilbertL2_sq {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {μ : Measure α}
    (u : Lp F 2 μ) : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def,
    ← integral_re (L2.integrable_inner u u)]
  apply integral_congr_ae
  filter_upwards [] with x
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (u x)).symm

/-- Uniformly bounded, a.e. convergent Hilbert-valued functions converge in L2
on a finite measure space. -/
theorem tendsto_complexHilbertL2_of_bounded_ae_tendsto
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] {μ : Measure α} [IsFiniteMeasure μ]
    {f : ℕ → α → F} {g : α → F}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (B : ℝ) (hfb : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ B)
    (hgb : ∀ᵐ x ∂μ, ‖g x‖ ≤ B)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hsq : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (F := fun n x => ‖f n x - g x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun _ : α => (2 * B) ^ 2)
      (fun n => (continuous_pow 2).comp_aestronglyMeasurable
        ((hf n).aestronglyMeasurable.fun_sub hg.aestronglyMeasurable).norm)
      (integrable_const ((2 * B) ^ 2))
      (fun n => by
        filter_upwards [hfb n, hgb] with x hx hy
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _)
          ((norm_sub_le _ _).trans (add_le_add hx hy) |>.trans_eq (two_mul B).symm) 2)
      (by
        filter_upwards [hlim] with x hx
        have h := (hx.sub_const (g x)).norm.pow 2
        simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using h)
    simpa only [integral_zero] using h
  have hn : Tendsto
      (fun n => ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2) atTop (𝓝 0) := by
    convert hsq using 1
    ext n
    rw [norm_complexHilbertL2_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf n).toLp (f n)) (hg.toLp g),
      (hf n).coeFn_toLp, hg.coeFn_toLp] with x hs hx hy
    simp only [Pi.sub_apply] at hs
    rw [hs, hx, hy]
  have hn' := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  have hnorm : Tendsto
      (fun n => ‖(hf n).toLp (f n) - hg.toLp g‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hn'
  exact tendsto_iff_dist_tendsto_zero.mpr
    (by simpa only [dist_eq_norm] using hnorm)

noncomputable def dirichletCubeApproxLocalL2 {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (k : ℕ) :
    TFCubes.CubeState q b ℓ :=
  (((contDiff_dirichletCubeApproxValue ℓ b p k).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_dirichletCubeApproxValue ℓ b p k)).restrict _).toLp
      (dirichletCubeApproxValue ℓ b p k)

theorem tendsto_dirichletCubeApproxLocalL2 {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) :
    Tendsto (fun k => dirichletCubeApproxLocalL2 ℓ b p k) atTop
      (𝓝 (TFCubes.dirichletCubeModeL2 ℓ b p)) := by
  let A := Real.sqrt (2 / ℓ.val)
  let B := ∏ _i : Fin 3, A
  have hfb (k : ℕ) : ∀ᵐ x ∂volume.restrict (TFCubes.cubeInterior b ℓ),
      ‖dirichletCubeApproxValue ℓ b p k x‖ ≤ B := by
    filter_upwards [] with x
    rw [dirichletCubeApproxValue, PiLp.norm_single]
    change ‖∏ i : Fin 3, TFCubes.compactDirichletMode ℓ (p.1 i) k (x i - b i)‖ ≤ B
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ =>
      norm_compactDirichletMode_le ℓ (p.1 i) k _
  have hgb : ∀ᵐ x ∂volume.restrict (TFCubes.cubeInterior b ℓ),
      ‖TFCubes.dirichletCubeModeValue ℓ b p x‖ ≤ B := by
    filter_upwards [] with x
    exact TFCubes.norm_dirichletCubeModeValue_le ℓ b p x
  have hlim : ∀ᵐ x ∂volume.restrict (TFCubes.cubeInterior b ℓ),
      Tendsto (fun k => dirichletCubeApproxValue ℓ b p k x) atTop
        (𝓝 (TFCubes.dirichletCubeModeValue ℓ b p x)) := by
    filter_upwards [ae_restrict_mem (TFCubes.measurableSet_cubeInterior b ℓ)] with x hx
    exact tendsto_dirichletCubeApproxValue ℓ b p hx
  have ht := tendsto_complexHilbertL2_of_bounded_ae_tendsto
    (fun k => ((contDiff_dirichletCubeApproxValue ℓ b p k).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_dirichletCubeApproxValue ℓ b p k)).restrict _)
    (TFCubes.dirichletCubeModeValue_memLp ℓ b p) B hfb hgb hlim
  simpa only [dirichletCubeApproxLocalL2, TFCubes.dirichletCubeModeL2] using ht

theorem zeroExtend_dirichletCubeApproxLocalL2 {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (k : ℕ) :
    TFCubes.regionZeroExtendL2 volume (TFCubes.measurableSet_cubeInterior b ℓ)
      (dirichletCubeApproxLocalL2 ℓ b p k) =
      (dirichletCubeApproxSchwartz ℓ b p k).toLp 2 volume := by
  have hl : dirichletCubeApproxLocalL2 ℓ b p k =ᵐ[
      volume.restrict (TFCubes.cubeInterior b ℓ)]
      dirichletCubeApproxValue ℓ b p k :=
    (((contDiff_dirichletCubeApproxValue ℓ b p k).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_dirichletCubeApproxValue ℓ b p k)).restrict _).coeFn_toLp
  have hi : (TFCubes.cubeInterior b ℓ).indicator
      (dirichletCubeApproxLocalL2 ℓ b p k) =ᵐ[volume]
      (TFCubes.cubeInterior b ℓ).indicator
        (dirichletCubeApproxValue ℓ b p k) :=
    (ae_eq_restrict_iff_indicator_ae_eq
      (TFCubes.measurableSet_cubeInterior b ℓ)).mp hl
  apply Lp.ext
  filter_upwards [TFCubes.regionZeroExtendL2_ae volume
      (TFCubes.measurableSet_cubeInterior b ℓ) (dirichletCubeApproxLocalL2 ℓ b p k),
    hi,
    (dirichletCubeApproxSchwartz ℓ b p k).coeFn_toLp 2 volume] with x hx hl hs
  rw [hx, hl, hs]
  by_cases hmem : x ∈ TFCubes.cubeInterior b ℓ
  · rw [Set.indicator_of_mem hmem]
    rfl
  · rw [Set.indicator_of_notMem hmem]
    exact (image_eq_zero_of_notMem_tsupport fun ht =>
      hmem (tsupport_dirichletCubeApproxValue_subset_cubeInterior ℓ b p k ht)).symm

theorem tendsto_dirichletCubeApproxSchwartz_toLp {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) :
    Tendsto (fun k => (dirichletCubeApproxSchwartz ℓ b p k).toLp 2 volume) atTop
      (𝓝 (dirichletCubeSpatialL2 ℓ b p)) := by
  have ht := ((TFCubes.regionZeroExtendL2LI (𝕜 := ℂ) volume
    (TFCubes.measurableSet_cubeInterior b ℓ)).continuous.tendsto
      (TFCubes.dirichletCubeModeL2 ℓ b p)).comp
      (tendsto_dirichletCubeApproxLocalL2 ℓ b p)
  change Tendsto (fun k => (dirichletCubeApproxSchwartz ℓ b p k).toLp 2 volume) atTop
    (𝓝 (TFCubes.regionZeroExtendL2 volume (TFCubes.measurableSet_cubeInterior b ℓ)
      (TFCubes.dirichletCubeModeL2 ℓ b p)))
  exact ht.congr' (Eventually.of_forall fun k => by
    simp only [Function.comp_apply, TFCubes.regionZeroExtendL2LI]
    exact zeroExtend_dirichletCubeApproxLocalL2 ℓ b p k)

theorem memLp_dirichletCubeApproxDerivativeValue_global {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (a : Fin 3) (k : ℕ) :
    MemLp (dirichletCubeApproxDerivativeValue ℓ b p a k) 2 volume := by
  exact (((contDiff_dirichletCubeApproxValue ℓ b p k).fderiv_right (m := 1) (by simp)).clm_apply
    contDiff_const).continuous.memLp_of_hasCompactSupport
      ((hasCompactSupport_dirichletCubeApproxValue ℓ b p k).fderiv_apply ℝ
        (positionCoordinateVector a))

theorem memLp_dirichletCubeApproxDerivativeValue {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (a : Fin 3) (k : ℕ) :
    MemLp (dirichletCubeApproxDerivativeValue ℓ b p a k) 2
      (volume.restrict (TFCubes.cubeInterior b ℓ)) :=
  (memLp_dirichletCubeApproxDerivativeValue_global ℓ b p a k).restrict _

noncomputable def dirichletCubeApproxDerivativeLocalL2 {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (a : Fin 3) (k : ℕ) :
    TFCubes.CubeState q b ℓ :=
  (memLp_dirichletCubeApproxDerivativeValue ℓ b p a k).toLp
    (dirichletCubeApproxDerivativeValue ℓ b p a k)

theorem tendsto_dirichletCubeApproxDerivativeLocalL2 {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (a : Fin 3) :
    Tendsto (fun k => dirichletCubeApproxDerivativeLocalL2 ℓ b p a k) atTop
      (𝓝 ((memLp_dirichletCubeDerivativeValue ℓ b p a).toLp
        (dirichletCubeDerivativeValue ℓ b p a))) := by
  obtain ⟨B, hB, hbound⟩ := exists_bound_dirichletCubeApproxDerivativeValue ℓ b p a
  have hfb (k : ℕ) : ∀ᵐ x ∂volume.restrict (TFCubes.cubeInterior b ℓ),
      ‖dirichletCubeApproxDerivativeValue ℓ b p a k x‖ ≤ B := by
    filter_upwards [ae_restrict_mem (TFCubes.measurableSet_cubeInterior b ℓ)] with x hx
    exact hbound k x hx
  have hgb : ∀ᵐ x ∂volume.restrict (TFCubes.cubeInterior b ℓ),
      ‖dirichletCubeDerivativeValue ℓ b p a x‖ ≤ B := by
    filter_upwards [ae_restrict_mem (TFCubes.measurableSet_cubeInterior b ℓ)] with x hx
    have ht := (tendsto_dirichletCubeApproxDerivativeValue ℓ b p a hx).norm
    exact le_of_tendsto ht (Eventually.of_forall fun k => hbound k x hx)
  have hlim : ∀ᵐ x ∂volume.restrict (TFCubes.cubeInterior b ℓ),
      Tendsto (fun k => dirichletCubeApproxDerivativeValue ℓ b p a k x) atTop
        (𝓝 (dirichletCubeDerivativeValue ℓ b p a x)) := by
    filter_upwards [ae_restrict_mem (TFCubes.measurableSet_cubeInterior b ℓ)] with x hx
    exact tendsto_dirichletCubeApproxDerivativeValue ℓ b p a hx
  apply tendsto_complexHilbertL2_of_bounded_ae_tendsto
    (fun k => memLp_dirichletCubeApproxDerivativeValue ℓ b p a k)
    (memLp_dirichletCubeDerivativeValue ℓ b p a) B hfb hgb hlim

@[expose] noncomputable def dirichletCubeDerivativeSpatialL2 {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (a : Fin 3) :
    Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position) :=
  TFCubes.regionZeroExtendL2 volume (TFCubes.measurableSet_cubeInterior b ℓ)
    ((memLp_dirichletCubeDerivativeValue ℓ b p a).toLp
      (dirichletCubeDerivativeValue ℓ b p a))

theorem zeroExtend_dirichletCubeApproxDerivativeLocalL2 {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (a : Fin 3) (k : ℕ) :
    TFCubes.regionZeroExtendL2 volume (TFCubes.measurableSet_cubeInterior b ℓ)
      (dirichletCubeApproxDerivativeLocalL2 ℓ b p a k) =
      ((memLp_dirichletCubeApproxDerivativeValue_global ℓ b p a k).toLp
        (dirichletCubeApproxDerivativeValue ℓ b p a k)) := by
  let Ω := TFCubes.cubeInterior b ℓ
  let f := dirichletCubeApproxDerivativeValue ℓ b p a k
  have hfglobal := memLp_dirichletCubeApproxDerivativeValue_global ℓ b p a k
  have hl := (hfglobal.restrict Ω).coeFn_toLp
  have hi : Ω.indicator (dirichletCubeApproxDerivativeLocalL2 ℓ b p a k) =ᵐ[volume]
      Ω.indicator f := (ae_eq_restrict_iff_indicator_ae_eq
        (TFCubes.measurableSet_cubeInterior b ℓ)).mp hl
  apply Lp.ext
  filter_upwards [TFCubes.regionZeroExtendL2_ae volume
      (TFCubes.measurableSet_cubeInterior b ℓ)
        (dirichletCubeApproxDerivativeLocalL2 ℓ b p a k), hi,
      hfglobal.coeFn_toLp] with x hx hi hf
  rw [hx, hi, hf]
  by_cases hmem : x ∈ Ω
  · rw [Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem hmem]
    exact (image_eq_zero_of_notMem_tsupport fun ht => hmem
      (tsupport_dirichletCubeApproxValue_subset_cubeInterior ℓ b p k
        (tsupport_fderiv_apply_subset ℝ (positionCoordinateVector a) ht))).symm

theorem tendsto_dirichletCubeApproxDerivativeSpatialL2 {q : ℕ}
    (ℓ : {ℓ : ℝ // 0 < ℓ}) (b : Position)
    (p : TFCubes.DirichletCubeModeIndex q) (a : Fin 3) :
    Tendsto (fun k => (memLp_dirichletCubeApproxDerivativeValue_global ℓ b p a k).toLp
      (dirichletCubeApproxDerivativeValue ℓ b p a k)) atTop
      (𝓝 (dirichletCubeDerivativeSpatialL2 ℓ b p a)) := by
  have ht := ((TFCubes.regionZeroExtendL2LI (𝕜 := ℂ) volume
    (TFCubes.measurableSet_cubeInterior b ℓ)).continuous.tendsto
      ((memLp_dirichletCubeDerivativeValue ℓ b p a).toLp
        (dirichletCubeDerivativeValue ℓ b p a))).comp
          (tendsto_dirichletCubeApproxDerivativeLocalL2 ℓ b p a)
  change Tendsto (fun k =>
      (memLp_dirichletCubeApproxDerivativeValue_global ℓ b p a k).toLp
        (dirichletCubeApproxDerivativeValue ℓ b p a k)) atTop
    (𝓝 (TFCubes.regionZeroExtendL2 volume
      (TFCubes.measurableSet_cubeInterior b ℓ)
        ((memLp_dirichletCubeDerivativeValue ℓ b p a).toLp
          (dirichletCubeDerivativeValue ℓ b p a))))
  exact ht.congr' (Eventually.of_forall fun k => by
    simp only [Function.comp_apply, TFCubes.regionZeroExtendL2LI]
    exact zeroExtend_dirichletCubeApproxDerivativeLocalL2 ℓ b p a k)

end LiebThirring.TFUpper

end
