/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Local weak derivatives in restricted L²

Test functions are globally smooth, compactly supported, and have their
closed support inside the region. The weak derivative belongs to local L²;
no boundary value or normal derivative is imposed.
-/

public section

open MeasureTheory
open scoped ContDiff Topology

namespace LiebThirring.TFCubes

/-- The physical L² carrier on a region, with restricted Lebesgue measure. -/
noncomputable abbrev RegionState (E F : Type*) [MeasureSpace E]
    [NormedAddCommGroup F] (Ω : Set E) := Lp F 2 (volume.restrict Ω)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- A weak directional derivative tested only inside the region. -/
@[expose] def HasWeakDerivativeOn (Ω : Set E) (v : E) (u g : RegionState E F Ω) : Prop :=
  ∀ η : E → F, HasCompactSupport η → ContDiff ℝ ∞ η → tsupport η ⊆ Ω →
    (∫ x in Ω, inner ℂ (η x) (g x)) =
      -(∫ x in Ω, inner ℂ (fderiv ℝ η x v) (u x))

variable [FiniteDimensional ℝ E] [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)]

/-- A compact smooth test function as an element of the local L² carrier. -/
@[expose] noncomputable def localTestFunctionL2 (Ω : Set E) (η : E → F)
    (hηc : HasCompactSupport η) (hηs : ContDiff ℝ ∞ η) : RegionState E F Ω :=
  ((hηs.continuous.memLp_of_hasCompactSupport hηc).restrict Ω).toLp η

/-- The local test inner product is exactly the restricted physical integral. -/
theorem inner_localTestFunctionL2 (Ω : Set E) (η : E → F)
    (hηc : HasCompactSupport η) (hηs : ContDiff ℝ ∞ η) (u : RegionState E F Ω) :
    inner ℂ (localTestFunctionL2 Ω η hηc hηs) u = ∫ x in Ω, inner ℂ (η x) (u x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((hηs.continuous.memLp_of_hasCompactSupport hηc).restrict Ω).coeFn_toLp]
    with x hx
  change inner ℂ (((hηs.continuous.memLp_of_hasCompactSupport hηc).restrict Ω).toLp η x) _ = _
  rw [hx]

/-- Weak local differentiation as an identity of bounded L² pairings. -/
theorem hasWeakDerivativeOn_iff_inner {Ω : Set E} {v : E} {u g : RegionState E F Ω} :
    HasWeakDerivativeOn Ω v u g ↔ ∀ η : E → F,
      ∀ hηc : HasCompactSupport η, ∀ hηs : ContDiff ℝ ∞ η, tsupport η ⊆ Ω →
        inner ℂ (localTestFunctionL2 Ω η hηc hηs) g =
          -inner ℂ (localTestFunctionL2 Ω (fun x ↦ fderiv ℝ η x v)
            (hηc.fderiv_apply ℝ v)
            ((hηs.fderiv_right (by simp)).clm_apply contDiff_const)) u := by
  constructor
  · intro h η hηc hηs hηΩ
    rw [inner_localTestFunctionL2, inner_localTestFunctionL2]
    exact h η hηc hηs hηΩ
  · intro h η hηc hηs hηΩ
    simpa only [inner_localTestFunctionL2] using h η hηc hηs hηΩ

/-- The zero function has zero local weak derivative. -/
theorem HasWeakDerivativeOn.zero (Ω : Set E) (v : E) :
    HasWeakDerivativeOn Ω v (0 : RegionState E F Ω) 0 := by
  rw [hasWeakDerivativeOn_iff_inner]
  intro η hηc hηs hηΩ
  simp only [inner_zero_right, neg_zero]

/-- Local weak derivatives are additive. -/
theorem HasWeakDerivativeOn.add {Ω : Set E} {v : E} {u g w h : RegionState E F Ω}
    (hu : HasWeakDerivativeOn Ω v u g) (hw : HasWeakDerivativeOn Ω v w h) :
    HasWeakDerivativeOn Ω v (u + w) (g + h) := by
  rw [hasWeakDerivativeOn_iff_inner] at hu hw ⊢
  intro η hηc hηs hηΩ
  rw [inner_add_right, inner_add_right, hu η hηc hηs hηΩ, hw η hηc hηs hηΩ, neg_add]

/-- Local weak derivatives commute with complex scalar multiplication. -/
theorem HasWeakDerivativeOn.smul {Ω : Set E} {v : E} {u g : RegionState E F Ω}
    (h : HasWeakDerivativeOn Ω v u g) (c : ℂ) :
    HasWeakDerivativeOn Ω v (c • u) (c • g) := by
  rw [hasWeakDerivativeOn_iff_inner] at h ⊢
  intro η hηc hηs hηΩ
  simpa only [inner_smul_right, mul_neg] using congrArg (c * ·) (h η hηc hηs hηΩ)

end LiebThirring.TFCubes

end
