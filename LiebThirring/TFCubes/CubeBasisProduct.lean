/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Products of scalar L² vectors

This file supplies the analytic product operation needed to tensor two
possibly infinitely indexed Hilbert bases of scalar L² spaces.
-/

@[expose] public section

open MeasureTheory

namespace LiebThirring.TFCubes

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]

omit [SigmaFinite μ] in
theorem memLp_two_prod_mul (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    MemLp (fun z : X × Y => f z.1 * g z.2) 2 (μ.prod ν) := by
  have hfm : AEStronglyMeasurable (fun z : X × Y => f z.1 * g z.2) (μ.prod ν) :=
    f.1.aestronglyMeasurable.comp_fst.mul
      g.1.aestronglyMeasurable.comp_snd
  rw [memLp_two_iff_integrable_sq_norm hfm]
  have hf := (memLp_two_iff_integrable_sq_norm f.1.aestronglyMeasurable).mp f.2
  have hg := (memLp_two_iff_integrable_sq_norm g.1.aestronglyMeasurable).mp g.2
  convert hf.mul_prod hg using 1
  ext z
  simp only [norm_mul, mul_pow]

/-- The pointwise product of two scalar L² vectors, regarded as an L²
vector for the product measure. -/
noncomputable def lpProd (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    Lp ℂ 2 (μ.prod ν) :=
  (memLp_two_prod_mul f g).toLp (fun z => f z.1 * g z.2)

omit [SigmaFinite μ] in
theorem lpProd_coeFn (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    lpProd f g =ᵐ[μ.prod ν] fun z => f z.1 * g z.2 :=
  (memLp_two_prod_mul f g).coeFn_toLp

omit [SigmaFinite μ] in
theorem lpProd_add_left (f₁ f₂ : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    lpProd (f₁ + f₂) g = lpProd f₁ g + lpProd f₂ g := by
  apply Lp.ext
  filter_upwards [lpProd_coeFn (f₁ + f₂) g, lpProd_coeFn f₁ g, lpProd_coeFn f₂ g,
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_add f₁ f₂),
    Lp.coeFn_add (lpProd f₁ g) (lpProd f₂ g)] with z hz h1 h2 ha hs
  simp only [hz, h1, h2, ha, hs, Pi.add_apply, add_mul]

omit [SigmaFinite μ] in
theorem lpProd_add_right (f : Lp ℂ 2 μ) (g₁ g₂ : Lp ℂ 2 ν) :
    lpProd f (g₁ + g₂) = lpProd f g₁ + lpProd f g₂ := by
  apply Lp.ext
  filter_upwards [lpProd_coeFn f (g₁ + g₂), lpProd_coeFn f g₁, lpProd_coeFn f g₂,
    Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_add g₁ g₂),
    Lp.coeFn_add (lpProd f g₁) (lpProd f g₂)] with z hz h1 h2 ha hs
  simp only [hz, h1, h2, ha, hs, Pi.add_apply, mul_add]

omit [SigmaFinite μ] in
theorem lpProd_smul_left (c : ℂ) (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    lpProd (c • f) g = c • lpProd f g := by
  apply Lp.ext
  filter_upwards [lpProd_coeFn (c • f) g, lpProd_coeFn f g,
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_smul c f),
    Lp.coeFn_smul c (lpProd f g)] with z hz hp hf hs
  simp only [hz, hp, hf, hs, Pi.smul_apply, smul_eq_mul, mul_assoc]

omit [SigmaFinite μ] in
theorem lpProd_smul_right (c : ℂ) (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    lpProd f (c • g) = c • lpProd f g := by
  apply Lp.ext
  filter_upwards [lpProd_coeFn f (c • g), lpProd_coeFn f g,
    Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_smul c g),
    Lp.coeFn_smul c (lpProd f g)] with z hz hp hg hs
  simp only [hz, hp, hg, hs, Pi.smul_apply, smul_eq_mul]
  ring

/-- Inner products of product vectors factor into the inner products of their
factors. -/
theorem inner_lpProd (f₁ f₂ : Lp ℂ 2 μ) (g₁ g₂ : Lp ℂ 2 ν) :
    inner ℂ (lpProd f₁ g₁) (lpProd f₂ g₂) =
      inner ℂ f₁ f₂ * inner ℂ g₁ g₂ := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def]
  calc
    ∫ z, inner ℂ (lpProd f₁ g₁ z) (lpProd f₂ g₂ z) ∂μ.prod ν =
        ∫ z : X × Y, (starRingEnd ℂ (f₁ z.1) * f₂ z.1) *
          (starRingEnd ℂ (g₁ z.2) * g₂ z.2) ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [lpProd_coeFn f₁ g₁, lpProd_coeFn f₂ g₂] with z h1 h2
      simp only [h1, h2, RCLike.inner_apply', map_mul]
      ring
    _ = (∫ x, starRingEnd ℂ (f₁ x) * f₂ x ∂μ) *
        ∫ y, starRingEnd ℂ (g₁ y) * g₂ y ∂ν := by
      simpa only [RCLike.inner_apply'] using
        (integral_prod_mul (μ := μ) (ν := ν)
          (fun x => inner ℂ (f₁ x) (f₂ x)) (fun y => inner ℂ (g₁ y) (g₂ y)))
    _ = (∫ x, inner ℂ (f₁ x) (f₂ x) ∂μ) *
        ∫ y, inner ℂ (g₁ y) (g₂ y) ∂ν := by
      simp only [RCLike.inner_apply']

theorem norm_lpProd (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    ‖lpProd f g‖ = ‖f‖ * ‖g‖ := by
  have h := inner_lpProd f f g g
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K] at h
  have hreal : ‖lpProd f g‖ ^ 2 = ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
    exact_mod_cast h
  rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  simpa [mul_pow] using hreal

/-- For fixed right factor, pointwise product is a continuous linear map. -/
noncomputable def lpProdRight (g : Lp ℂ 2 ν) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearMap.mkContinuous
    { toFun := fun f => lpProd f g
      map_add' := fun f₁ f₂ => lpProd_add_left f₁ f₂ g
      map_smul' := fun c f => lpProd_smul_left c f g }
    ‖g‖ fun f => by
      change ‖lpProd f g‖ ≤ ‖g‖ * ‖f‖
      rw [norm_lpProd, mul_comm]

/-- For fixed left factor, pointwise product is a continuous linear map. -/
noncomputable def lpProdLeft (f : Lp ℂ 2 μ) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearMap.mkContinuous
    { toFun := fun g => lpProd f g
      map_add' := lpProd_add_right f
      map_smul' := fun c g => lpProd_smul_right c f g }
    ‖f‖ fun g => by
      change ‖lpProd f g‖ ≤ ‖f‖ * ‖g‖
      rw [norm_lpProd]

end LiebThirring.TFCubes

end

