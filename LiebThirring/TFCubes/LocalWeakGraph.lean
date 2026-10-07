/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.LocalWeakDerivative
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Uniqueness and the closed local weak-derivative graph -/

public section

open MeasureTheory
open scoped ContDiff Topology

namespace LiebThirring.TFCubes

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Weak derivatives on an open region are unique in the local L² carrier. -/
theorem HasWeakDerivativeOn.unique {Ω : Set E} {v : E} {u g h : RegionState E F Ω}
    (hg : HasWeakDerivativeOn Ω v u g) (hh : HasWeakDerivativeOn Ω v u h)
    (hΩ : IsOpen Ω) : g = h := by
  let d : RegionState E F Ω := g - h
  have htest (η : E → F) (hηc : HasCompactSupport η) (hηs : ContDiff ℝ ∞ η)
      (hηΩ : tsupport η ⊆ Ω) : inner ℂ (localTestFunctionL2 Ω η hηc hηs) d = 0 := by
    dsimp [d]
    rw [inner_sub_right, hasWeakDerivativeOn_iff_inner.mp hg η hηc hηs hηΩ,
      hasWeakDerivativeOn_iff_inner.mp hh η hηc hηs hηΩ, sub_self]
  have hd : LocallyIntegrable d (volume.restrict Ω) :=
    (Lp.memLp d).locallyIntegrable (by norm_num)
  have hzero : ∀ᵐ x ∂volume.restrict Ω, x ∈ Ω → d x = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hd.locallyIntegrableOn Ω)
    intro ψ hψs hψc hψΩ
    have hfi := hd.integrable_smul_left_of_hasCompactSupport hψs.continuous hψc
    apply integral_eq_zero_of_forall_integral_inner_eq_zero ℂ _ hfi
    intro z
    let η : E → F := fun x ↦ (ψ x : ℂ) • z
    have hηc : HasCompactSupport η := (hψc.comp_left Complex.ofReal_zero).smul_right
    have hηs : ContDiff ℝ ∞ η :=
      (Complex.ofRealCLM.contDiff.comp hψs).smul contDiff_const
    have hηΩ : tsupport η ⊆ Ω :=
      (tsupport_smul_subset_left _ _).trans ((tsupport_comp_subset Complex.ofReal_zero ψ).trans hψΩ)
    have ht := htest η hηc hηs hηΩ
    rw [inner_localTestFunctionL2] at ht
    convert ht using 1
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [η]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (ψ x) (d x)]
    exact (inner_smul_real_right (𝕜 := ℂ) z (d x) (ψ x)).trans
      (inner_smul_real_left (𝕜 := ℂ) z (d x) (ψ x)).symm
  have hd0 : d = 0 := by
    apply Lp.ext
    filter_upwards [hzero, ae_restrict_mem hΩ.measurableSet, Lp.coeFn_zero (E := F)
      (p := 2) (μ := volume.restrict Ω)] with x hx hmem hz
    exact (hx hmem).trans hz.symm
  exact sub_eq_zero.mp hd0

end LiebThirring.TFCubes

end
