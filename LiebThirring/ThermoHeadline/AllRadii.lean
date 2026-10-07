/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoHeadline.ZeroDensity
public import LiebThirring.ThermoBounds.LowerRadii
public import LiebThirring.ThermoBounds.PhysicalPacking
public import LiebThirring.ThermoLimit.ConditionalEngine
public import Mathlib.Tactic

/-!
# All-density limits from the integer physics laws

The canonical engine supplies the continuous convex
limit, interior packing comparison and lower-limit comparison control every positive-density radius sequence, and
actual unit-ball lattice trials give the zero-density endpoint. All physical
inputs remain explicit in this internal abstract helper.
-/

public section

open Filter Topology Finset Metric Set
open scoped NNReal
open LiebThirring.ThermoLimit LiebThirring.ThermoBounds

namespace LiebThirring.ThermoHeadline

/-- Arbitrary-sequence convergence on real finite energies, including zero density. -/
theorem exists_all_ball_limits_of_integer_physics
    {E : Set Position → ℕ → ℝ} {A : ℝ}
    (hlower : ∀ L m, 0 < L → -A * m ≤ E (ball (0 : Position) L) m)
    (hmono : ∀ Ω Ω', IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω →
      IsOpen Ω' → Ω'.Nonempty → Bornology.IsBounded Ω' →
      Ω ⊆ Ω' → ∀ m, E Ω' m ≤ E Ω m)
    (htranslation : ∀ c R, 0 < R → ∀ m,
      E (ball c R) m = E (ball (0 : Position) R) m)
    (hpacking : ∀ (ι : Type) (Ω : Set Position) (s : Finset ι)
      (c : ι → Position) (r : ι → ℝ) (m : ι → ℕ),
      IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω →
      (∀ i ∈ s, 0 < r i) → (∀ i ∈ s, ball (c i) (r i) ⊆ Ω) →
      (s : Set ι).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E Ω (∑ i ∈ s, m i) ≤ ∑ i ∈ s, E (ball (c i) (r i)) (m i)) :
    ∃ e : ℝ≥0 → ℝ,
      e 0 = 0 ∧ Continuous e ∧
      (∀ (ρ₁ ρ₂ t : ℝ≥0), t ≤ 1 →
        e (t * ρ₁ + (1 - t) * ρ₂) ≤
          (t : ℝ) * e ρ₁ + (1 - (t : ℝ)) * e ρ₂) ∧
      ∀ (ρ : ℝ≥0) (L : ℕ → ℝ) (m : ℕ → ℕ),
        (∀ j, 0 < L j) → Tendsto L atTop atTop →
        Tendsto (fun j => (m j : ℝ) / neutralBallVolume (L j)) atTop (𝓝 (ρ : ℝ)) →
        Tendsto (fun j => neutralBallDensity E (L j) (m j)) atTop (𝓝 (e ρ)) := by
  have hcanonical := canonical_packing_of_domain_packing hpacking
  have hunion := union_packing_of_domain_packing hpacking
  obtain ⟨e, ⟨he0, hec, heconv, _, heuniform⟩, _⟩ :=
    existsUnique_conditional_canonical_limit htranslation hcanonical hlower
  let eR : ℝ → ℝ := fun x => e x.toNNReal
  have heR : ContinuousOn eR (Ici 0) :=
    (hec.comp continuous_real_toNNReal).continuousOn
  have huniformR : ∀ (l u : ℝ), 0 ≤ l → l ≤ u → ∀ δ > 0, ∃ n₀,
      ∀ n ≥ n₀, ∀ x ∈ Set.Icc l u, |neutralStandardSequence E n x - eR x| ≤ δ := by
    intro l u hl _ δ hδ
    let J : Set ℝ≥0 := Real.toNNReal '' Set.Icc l u
    have hJ : IsCompact J := isCompact_Icc.image continuous_real_toNNReal
    have hu := heuniform J hJ
    rw [Metric.tendstoUniformlyOn_iff] at hu
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hu δ hδ)
    refine ⟨N, ?_⟩
    intro n hn x hx
    have hh := hN n hn x.toNNReal (mem_image_of_mem Real.toNNReal hx)
    have hx0 : 0 ≤ x := hl.trans hx.1
    have habs : |neutralStandardSequence E n x - eR x| < δ := by
      simpa only [neutralStandardSequence, eR, Real.coe_toNNReal x hx0,
        Real.dist_eq, abs_sub_comm] using hh
    exact habs.le
  refine ⟨e, he0, hec, heconv, ?_⟩
  intro ρ L m hLpos hL hs
  by_cases hρ : ρ = 0
  · subst ρ
    simpa only [he0, NNReal.coe_zero] using
      neutralBallDensity_zero_of_integer_physics hlower htranslation hpacking hL hs
  · have hρR : 0 < (ρ : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hρ)
    have hupper := eventually_arbitrary_ball_le_limit_add_of_integer_inputs
      hmono htranslation hunion heR huniformR hLpos hL hρR hs
    have hlower' := eventually_limit_sub_le_arbitrary_ball_of_integer_inputs
      hmono htranslation hunion heR huniformR hLpos hL hρR hs
    simp only [eR, Real.toNNReal_coe] at hupper hlower'
    apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [hlower' ((e ρ - a) / 2) (by linarith only [ha])] with j hj
      linarith only [hj, ha]
    · intro a ha
      filter_upwards [hupper ((a - e ρ) / 2) (by linarith only [ha])] with j hj
      linarith only [hj, ha]

end LiebThirring.ThermoHeadline

end
