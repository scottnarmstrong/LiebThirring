/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Variational.RellichLocal
public import LiebThirring.Variational.CompactLimits
public import LiebThirring.Variational.CompactBox

/-! # Global L² convergence from local Rellich compactness and tightness -/

public section

open MeasureTheory Filter WithLp
open scoped Topology

namespace LiebThirring

/-- Restriction and its complement add to the original state. -/
theorem stateIndicatorCLM_add_compl {N q : ℕ}
    (b : Set (Configuration N)) (hb : MeasurableSet b) (u : State N q) :
    stateIndicatorCLM b hb u + stateIndicatorCLM bᶜ hb.compl u = u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (stateIndicatorCLM b hb u) (stateIndicatorCLM bᶜ hb.compl u),
    stateIndicatorCLM_coeFn b hb u, stateIndicatorCLM_coeFn bᶜ hb.compl u] with x h₁ h₂ h₃
  rw [h₁, Pi.add_apply, h₂, h₃]
  by_cases hx : x ∈ b <;> simp [hx]

/-- An eventual norm bound also bounds the weak limit. -/
theorem norm_le_of_tendsto_inner_eventually_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {u : ℕ → E} {v : E}
    (hu : ∀ w, Tendsto (fun n => inner ℂ (u n) w) atTop (𝓝 (inner ℂ v w)))
    (K : ℝ) (hK : ∀ n, ‖u n‖ ≤ K) (ε : ℝ)
    (hε : ∀ᶠ n in atTop, ‖u n‖ ≤ ε) : ‖v‖ ≤ ε := by
  apply (norm_le_liminf_of_tendsto_inner hu K hK).trans
  have hlo : IsBoundedUnder (· ≥ ·) atTop (fun n => ‖u n‖) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n : ℕ in atTop, 0 ≤ ‖u n‖
    exact Eventually.of_forall fun n => norm_nonneg _
  apply liminf_le_of_le hlo
  intro a ha
  obtain ⟨n, hn, hn'⟩ := (ha.and hε).exists
  exact hn.trans hn'

/-- Local Rellich convergence plus tightness gives global strong convergence.
Tightness is expressed by eventual small tails on finite-measure measurable sets; the sets
may depend on the requested error, and no uniform support assumption is made. -/
theorem tendsto_state_of_formGraph_weak_of_tight {N q : ℕ}
    {u : ℕ → Sobolev.formGraph N q} {v : Sobolev.formGraph N q}
    (hu : ∀ w, Tendsto (fun n => inner ℂ (u n) w) atTop (𝓝 (inner ℂ v w)))
    (K : ℝ) (hK : ∀ n, ‖u n‖ ≤ K)
    (htight : ∀ ε > 0, ∃ b : Set (Configuration N), ∃ hb : MeasurableSet b,
      volume b ≠ ⊤ ∧ ∀ᶠ n in atTop,
        ‖stateIndicatorCLM bᶜ hb.compl ((u n : Sobolev.FormGraphAmbient N q) none)‖ ≤ ε) :
    Tendsto (fun n => (u n : Sobolev.FormGraphAmbient N q) none) atTop
      (𝓝 ((v : Sobolev.FormGraphAmbient N q) none)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨b, hb, hμb, htail⟩ := htight (ε / 4) (by positivity)
  have hweak := tendsto_inner_formGraph_coordinate hu none
  have hstate (n : ℕ) : ‖(u n : Sobolev.FormGraphAmbient N q) none‖ ≤ K :=
    (PiLp.norm_apply_le (u n : Sobolev.FormGraphAmbient N q) none).trans (hK n)
  have hweakTail := fun w => tendsto_inner_map_of_tendsto_inner hweak
    (stateIndicatorCLM bᶜ hb.compl) w
  have hvTail : ‖stateIndicatorCLM bᶜ hb.compl ((v : Sobolev.FormGraphAmbient N q) none)‖ ≤ ε / 4 :=
    norm_le_of_tendsto_inner_eventually_le hweakTail K
      (fun n => (norm_stateIndicatorCLM_le bᶜ hb.compl _).trans (hstate n)) _ htail
  have hlocal := tendsto_stateIndicator_of_formGraph_weak b hb hμb hu K hK
  filter_upwards [htail, (Metric.tendsto_nhds.mp hlocal) (ε / 4) (by positivity)] with n hn hn'
  rw [dist_eq_norm]
  calc
    _ = ‖stateIndicatorCLM b hb
        (((u n : Sobolev.FormGraphAmbient N q) none) - ((v : Sobolev.FormGraphAmbient N q) none)) +
        stateIndicatorCLM bᶜ hb.compl
        (((u n : Sobolev.FormGraphAmbient N q) none) - ((v : Sobolev.FormGraphAmbient N q) none))‖ :=
      congrArg norm (stateIndicatorCLM_add_compl b hb _).symm
    _ ≤ ‖stateIndicatorCLM b hb
        (((u n : Sobolev.FormGraphAmbient N q) none) - ((v : Sobolev.FormGraphAmbient N q) none))‖ +
        ‖stateIndicatorCLM bᶜ hb.compl
        (((u n : Sobolev.FormGraphAmbient N q) none) - ((v : Sobolev.FormGraphAmbient N q) none))‖ := norm_add_le _ _
    _ ≤ ‖stateIndicatorCLM b hb
        (((u n : Sobolev.FormGraphAmbient N q) none) - ((v : Sobolev.FormGraphAmbient N q) none))‖ +
        (‖stateIndicatorCLM bᶜ hb.compl ((u n : Sobolev.FormGraphAmbient N q) none)‖ +
        ‖stateIndicatorCLM bᶜ hb.compl ((v : Sobolev.FormGraphAmbient N q) none)‖) := by
      rw [map_sub (stateIndicatorCLM bᶜ hb.compl)]
      exact add_le_add le_rfl (norm_sub_le _ _)
    _ < ε / 4 + (ε / 4 + ε / 4) := by
      have hl : ‖stateIndicatorCLM b hb
          (((u n : Sobolev.FormGraphAmbient N q) none) - ((v : Sobolev.FormGraphAmbient N q) none))‖ < ε / 4 := by
        simpa only [map_sub, dist_eq_norm] using hn'
      exact add_lt_add_of_lt_of_le hl (add_le_add hn hvTail)
    _ < ε := by linarith

/-- Every bounded tight graph sequence has a weak graph / strong state subsequence. -/
theorem exists_formGraph_subsequence_of_tight {N q : ℕ}
    (u : ℕ → Sobolev.formGraph N q) (K : ℝ) (hK : ∀ n, ‖u n‖ ≤ K)
    (htight : ∀ ε > 0, ∃ b : Set (Configuration N), ∃ hb : MeasurableSet b,
      volume b ≠ ⊤ ∧ ∀ᶠ n in atTop,
        ‖stateIndicatorCLM bᶜ hb.compl ((u n : Sobolev.FormGraphAmbient N q) none)‖ ≤ ε) :
    ∃ v : Sobolev.formGraph N q, ‖v‖ ≤ K ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ w, Tendsto (fun n => inner ℂ (u (φ n)) w) atTop (𝓝 (inner ℂ v w))) ∧
      Tendsto (fun n => (u (φ n) : Sobolev.FormGraphAmbient N q) none) atTop
        (𝓝 ((v : Sobolev.FormGraphAmbient N q) none)) := by
  obtain ⟨v, hv, φ, hφ, hweak⟩ := exists_formGraph_weak_subsequence u K hK
  refine ⟨v, hv, φ, hφ, hweak, tendsto_state_of_formGraph_weak_of_tight hweak K
    (fun n => hK (φ n)) ?_⟩
  intro ε hε
  obtain ⟨b, hb, hμb, ht⟩ := htight ε hε
  exact ⟨b, hb, hμb, hφ.tendsto_atTop.eventually ht⟩

/-- The argument iterated limsup particle-tail condition supplies eventual small L² tails. -/
theorem state_tight_of_limsup_particle_tail {N q : ℕ}
    (u : ℕ → State N q) (K : ℝ) (hK : ∀ n, ‖u n‖ ≤ K)
    (htight : Tendsto (fun R : ℝ => limsup (fun n =>
      ∫ x in {x : Configuration N | ∃ i : Fin N, R < ‖particlePosition x i‖},
        ‖u n x‖ ^ 2) atTop) atTop (𝓝 0)) :
    ∀ ε > 0, ∃ b : Set (Configuration N), ∃ hb : MeasurableSet b,
      volume b ≠ ⊤ ∧ ∀ᶠ n in atTop, ‖stateIndicatorCLM bᶜ hb.compl (u n)‖ ≤ ε := by
  intro ε hε
  obtain ⟨R, hR⟩ := (htight.eventually_lt_const (sq_pos_of_pos hε)).exists
  have hhi : IsBoundedUnder (· ≤ ·) atTop (fun n =>
      ∫ x in {x : Configuration N | ∃ i : Fin N, R < ‖particlePosition x i‖}, ‖u n x‖ ^ 2) := by
    refine ⟨K ^ 2, ?_⟩
    change ∀ᶠ n : ℕ in atTop, _ ≤ K ^ 2
    apply Eventually.of_forall
    intro n
    calc
      _ ≤ ∫ x, ‖u n x‖ ^ 2 := integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall fun x => sq_nonneg ‖u n x‖) (integrable_state_norm_sq (u n))
      _ = ‖u n‖ ^ 2 := integral_state_norm_sq _
      _ ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hK n) 2
  refine ⟨configurationBox N R, configurationBox_measurableSet N R,
    (configurationBox_volume_lt_top N R).ne, ?_⟩
  filter_upwards [eventually_lt_of_limsup_lt hR hhi] with n hn
  apply (sq_le_sq₀ (norm_nonneg _) hε.le).mp
  rw [norm_stateIndicatorCLM_sq]
  exact ((integral_compl_configurationBox_norm_sq_le_particle_tail R (u n)).trans_lt hn).le

/-- Bounded particle-tight sequences have a weak graph and globally strong L² subsequence. -/
theorem exists_formGraph_subsequence_of_particle_tight {N q : ℕ}
    (u : ℕ → Sobolev.formGraph N q) (K : ℝ) (hK : ∀ n, ‖u n‖ ≤ K)
    (htight : Tendsto (fun R : ℝ => limsup (fun n =>
      ∫ x in {x : Configuration N | ∃ i : Fin N, R < ‖particlePosition x i‖},
        ‖(u n : Sobolev.FormGraphAmbient N q) none x‖ ^ 2) atTop) atTop (𝓝 0)) :
    ∃ v : Sobolev.formGraph N q, ‖v‖ ≤ K ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ w, Tendsto (fun n => inner ℂ (u (φ n)) w) atTop (𝓝 (inner ℂ v w))) ∧
      Tendsto (fun n => (u (φ n) : Sobolev.FormGraphAmbient N q) none) atTop
        (𝓝 ((v : Sobolev.FormGraphAmbient N q) none)) :=
  exists_formGraph_subsequence_of_tight u K hK
    (state_tight_of_limsup_particle_tail _ K
      (fun n => (PiLp.norm_apply_le (u n : Sobolev.FormGraphAmbient N q) none).trans (hK n)) htight)

end LiebThirring
end
