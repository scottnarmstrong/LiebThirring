/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.CanonicalLimit
public import LiebThirring.ThermoLimit.Residual
import Mathlib.Tactic

/-!
# Conditional canonical analytic engine

Integer interpolation, the canonical recurrence and uniform convergence give the limiting energy. The energy
is abstract and its physical inputs are explicit. This is a standard-ball
sequence theorem, not the all-radius thermodynamic theorem.
-/

public section

open Finset Metric Set Filter Topology
open scoped NNReal

namespace LiebThirring.ThermoLimit

/-- Integer neutral packing, translation invariance, and extensive stability
determine a unique continuous convex standard-sequence limit,
with uniform convergence on every compact density set. -/
theorem existsUnique_conditional_canonical_limit {E : Set Position → ℕ → ℝ} {A : ℝ}
    (htranslation : ∀ c R, 0 < R → ∀ m,
      E (ball c R) m = E (ball (0 : Position) R) m)
    (hpacking : ∀ L (s : Finset SwissCheeseLabel) (c : SwissCheeseLabel → Position)
      (r : SwissCheeseLabel → ℝ) (m : SwissCheeseLabel → ℕ), 0 < L →
      (∀ i ∈ s, 0 < r i) →
      (∀ i ∈ s, ball (c i) (r i) ⊆ ball (0 : Position) L) →
      (s : Set SwissCheeseLabel).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E (ball (0 : Position) L) (∑ i ∈ s, m i) ≤ ∑ i ∈ s, E (ball (c i) (r i)) (m i))
    (hlower : ∀ L m, 0 < L → -A * m ≤ E (ball (0 : Position) L) m) :
    ∃! e : ℝ≥0 → ℝ,
      e 0 = 0 ∧ Continuous e ∧
      (∀ (ρ₁ ρ₂ t : ℝ≥0), t ≤ 1 →
        e (t * ρ₁ + (1 - t) * ρ₂) ≤ (t : ℝ) * e ρ₁ + (1 - (t : ℝ)) * e ρ₂) ∧
      (∀ ρ : ℝ≥0, Tendsto (canonicalBallSequence E (ρ : ℝ)) atTop (𝓝 (e ρ))) ∧
      ∀ I : Set ℝ≥0, IsCompact I →
        TendstoUniformlyOn (fun n (ρ : ℝ≥0) => canonicalBallSequence E (ρ : ℝ) n) e atTop I := by
  have hvacuum : ∀ L, 0 < L → E (ball (0 : Position) L) 0 = 0 :=
    fun _ hL => canonicalBall_vacuum_of_lower_bound_and_packing hpacking hlower hL
  obtain ⟨e, he, huniq⟩ := existsUnique_canonicalBallSequence_limit htranslation hpacking hlower
  let eR : ℝ → ℝ := fun ρ => e ρ.toNNReal
  have heR : ∀ ρ, 0 ≤ ρ → Tendsto (canonicalBallSequence E ρ) atTop (𝓝 (eR ρ)) := by
    intro ρ hρ
    simpa only [Real.coe_toNNReal ρ hρ] using he ρ.toNNReal
  have hcR := canonicalLimit_continuousOn htranslation hpacking hlower hvacuum eR heR
  have hconvR := canonicalLimit_convexOn htranslation hpacking hlower hvacuum eR heR
  have he0 : e 0 = 0 := by
    simpa only [eR, Real.toNNReal_zero] using
      canonicalLimit_zero htranslation hpacking hlower hvacuum eR heR
  have hc : Continuous e := by
    simpa only [Function.comp_def, eR, Real.toNNReal_coe] using
      hcR.comp_continuous NNReal.continuous_coe (fun ρ => ρ.coe_nonneg)
  refine ⟨e, ⟨he0, hc, ?_, he, ?_⟩, ?_⟩
  · intro ρ₁ ρ₂ t ht
    have ht1 : (t : ℝ) ≤ 1 := by exact_mod_cast ht
    have hh := hconvR.2 ρ₁.coe_nonneg ρ₂.coe_nonneg t.coe_nonneg
      (sub_nonneg.mpr ht1) (by ring : (t : ℝ) + (1 - (t : ℝ)) = 1)
    have harg : ((t * ρ₁ + (1 - t) * ρ₂ : ℝ≥0) : ℝ) =
        (t : ℝ) * (ρ₁ : ℝ) + (1 - (t : ℝ)) * (ρ₂ : ℝ) := by
      rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_sub ht, NNReal.coe_one]
    simp only [smul_eq_mul] at hh
    rw [← harg] at hh
    simpa only [smul_eq_mul, eR, Real.toNNReal_coe] using hh
  · intro I hI
    have hJ : IsCompact ((fun ρ : ℝ≥0 => (ρ : ℝ)) '' I) := hI.image NNReal.continuous_coe
    have hJ0 : ((fun ρ : ℝ≥0 => (ρ : ℝ)) '' I) ⊆ Ici 0 := by
      rintro _ ⟨ρ, _, rfl⟩
      exact ρ.coe_nonneg
    have hu := canonicalLimit_uniform htranslation hpacking hlower hvacuum eR heR hJ hJ0
    rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
    intro ε hε
    filter_upwards [hu ε hε] with n hn
    intro ρ hρ
    simpa only [eR, Real.toNNReal_coe] using hn (ρ : ℝ) (Set.mem_image_of_mem _ hρ)
  · intro e' he'
    exact huniq e' he'.2.2.2.1

end LiebThirring.ThermoLimit

end
