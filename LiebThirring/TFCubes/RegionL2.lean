/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Restriction and zero extension for local L² functions

The local carrier is `Lp E 2 (μ.restrict Ω)`. Restriction preserves the original
representative almost everywhere on Ω, and zero extension uses the literal
indicator function. These are L² transports; no weak derivative across the
boundary is asserted.
-/

public section

open MeasureTheory

namespace LiebThirring.TFCubes

variable {α E 𝕜 : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [RCLike 𝕜] [NormedSpace 𝕜 E] (μ : Measure α) (Ω : Set α)

/-- Restriction of a global L² function to the restricted measure. -/
@[expose] noncomputable def regionRestrictL2 (u : Lp E 2 μ) : Lp E 2 (μ.restrict Ω) :=
  ((Lp.memLp u).restrict Ω).toLp u

/-- The restriction has the original representative almost everywhere locally. -/
theorem regionRestrictL2_ae (u : Lp E 2 μ) :
    regionRestrictL2 μ Ω u =ᵐ[μ.restrict Ω] u :=
  ((Lp.memLp u).restrict Ω).coeFn_toLp

/-- Restriction contracts the L² norm. -/
theorem norm_regionRestrictL2_le (u : Lp E 2 μ) : ‖regionRestrictL2 μ Ω u‖ ≤ ‖u‖ := by
  rw [regionRestrictL2, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top u)
    (eLpNorm_mono_measure u Measure.restrict_le_self)

/-- The restriction map is linear. -/
@[expose] noncomputable def regionRestrictL2Linear : Lp E 2 μ →ₗ[𝕜] Lp E 2 (μ.restrict Ω) where
  toFun := regionRestrictL2 μ Ω
  map_add' u v := by
    apply Lp.ext
    filter_upwards [regionRestrictL2_ae μ Ω (u + v), (Lp.coeFn_add u v).filter_mono (ae_mono Measure.restrict_le_self), Lp.coeFn_add (regionRestrictL2 μ Ω u) (regionRestrictL2 μ Ω v),
      regionRestrictL2_ae μ Ω u, regionRestrictL2_ae μ Ω v] with x hsum hglob hlocal hu hv
    simp only [Pi.add_apply] at hglob hlocal
    rw [hsum, hglob, hlocal, hu, hv]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [regionRestrictL2_ae μ Ω (c • u), (Lp.coeFn_smul c u).filter_mono (ae_mono Measure.restrict_le_self), Lp.coeFn_smul c (regionRestrictL2 μ Ω u),
      regionRestrictL2_ae μ Ω u] with x hsum hglob hlocal hu
    simp only [Pi.smul_apply] at hglob hlocal
    change regionRestrictL2 μ Ω (c • u) x = (c • regionRestrictL2 μ Ω u) x
    rw [hsum, hglob, hlocal, hu]

variable {Ω} (hΩ : MeasurableSet Ω)

/-- Zero extension of a local L² function by the literal indicator. -/
@[expose] noncomputable def regionZeroExtendL2 (u : Lp E 2 (μ.restrict Ω)) : Lp E 2 μ :=
  ((memLp_indicator_iff_restrict hΩ).mpr (Lp.memLp u)).toLp (Ω.indicator u)

/-- Zero extension has its indicator representative almost everywhere globally. -/
theorem regionZeroExtendL2_ae (u : Lp E 2 (μ.restrict Ω)) :
    regionZeroExtendL2 μ hΩ u =ᵐ[μ] Ω.indicator u :=
  ((memLp_indicator_iff_restrict hΩ).mpr (Lp.memLp u)).coeFn_toLp

/-- Zero extension preserves the local L² norm. -/
theorem norm_regionZeroExtendL2 (u : Lp E 2 (μ.restrict Ω)) :
    ‖regionZeroExtendL2 μ hΩ u‖ = ‖u‖ := by
  rw [regionZeroExtendL2, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hΩ, Lp.norm_def]

/-- The indicator zero extension is linear. -/
@[expose] noncomputable def regionZeroExtendL2Linear : Lp E 2 (μ.restrict Ω) →ₗ[𝕜] Lp E 2 μ where
  toFun := regionZeroExtendL2 μ hΩ
  map_add' u v := by
    apply Lp.ext
    have hsum : Ω.indicator (u + v : Lp E 2 (μ.restrict Ω)) =ᵐ[μ]
        Ω.indicator (fun x ↦ u x + v x) :=
      (ae_eq_restrict_iff_indicator_ae_eq hΩ).mp (Lp.coeFn_add u v)
    filter_upwards [regionZeroExtendL2_ae μ hΩ (u + v), hsum,
      Lp.coeFn_add (regionZeroExtendL2 μ hΩ u) (regionZeroExtendL2 μ hΩ v),
      regionZeroExtendL2_ae μ hΩ u, regionZeroExtendL2_ae μ hΩ v] with x hz hs hl hu hv
    simp only [Pi.add_apply] at hl
    change regionZeroExtendL2 μ hΩ (u + v) x = (regionZeroExtendL2 μ hΩ u + regionZeroExtendL2 μ hΩ v) x
    rw [hz, hs, hl, hu, hv]
    exact congrFun (Set.indicator_add Ω u v) x
  map_smul' c u := by
    apply Lp.ext
    have hsmul : Ω.indicator (c • u : Lp E 2 (μ.restrict Ω)) =ᵐ[μ]
        Ω.indicator (fun x ↦ c • u x) :=
      (ae_eq_restrict_iff_indicator_ae_eq hΩ).mp (Lp.coeFn_smul c u)
    filter_upwards [regionZeroExtendL2_ae μ hΩ (c • u), hsmul,
      Lp.coeFn_smul c (regionZeroExtendL2 μ hΩ u),
      regionZeroExtendL2_ae μ hΩ u] with x hz hs hl hu
    simp only [Pi.smul_apply] at hl
    change regionZeroExtendL2 μ hΩ (c • u) x = (c • regionZeroExtendL2 μ hΩ u) x
    rw [hz, hs, hl, hu]
    by_cases hx : x ∈ Ω <;> simp [hx]

/-- The local L² carrier embeds linearly and isometrically into global L². -/
@[expose] noncomputable def regionZeroExtendL2LI : Lp E 2 (μ.restrict Ω) →ₗᵢ[𝕜] Lp E 2 μ where
  toLinearMap := regionZeroExtendL2Linear μ hΩ
  norm_map' := by
    intro u
    change ‖regionZeroExtendL2 μ hΩ u‖ = ‖u‖
    exact norm_regionZeroExtendL2 μ hΩ u

end LiebThirring.TFCubes

end
