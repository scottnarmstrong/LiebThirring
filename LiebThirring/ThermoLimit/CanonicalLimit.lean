/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.CanonicalMidpoint
public import LiebThirring.ThermoLimit.CanonicalRenewal
public import LiebThirring.ThermoLimit.ConvexityLimit
public import LiebThirring.ThermoLimit.LimitContinuity
public import LiebThirring.ThermoLimit.Uniformity
import Mathlib.Tactic

/-!
# The conditional analytic engine for canonical ball energies

Assembled from integer packing, translation invariance,
extensive stability, and the vacuum energy. The geometric family is proved
in `LiebThirring.Packing`; none of the analytic conclusions is a physical
input.
-/

public section

open Finset Metric Set Filter Topology

namespace LiebThirring.ThermoLimit

variable {E : Set Position → ℕ → ℝ} {A : ℝ}
variable (htranslation : ∀ c R, 0 < R → ∀ m,
  E (ball c R) m = E (ball (0 : Position) R) m)
variable (hpacking : ∀ L (s : Finset SwissCheeseLabel) (c : SwissCheeseLabel → Position)
  (r : SwissCheeseLabel → ℝ) (m : SwissCheeseLabel → ℕ), 0 < L →
  (∀ i ∈ s, 0 < r i) →
  (∀ i ∈ s, ball (c i) (r i) ⊆ ball (0 : Position) L) →
  (s : Set SwissCheeseLabel).PairwiseDisjoint (fun i => ball (c i) (r i)) →
  E (ball (0 : Position) L) (∑ i ∈ s, m i) ≤ ∑ i ∈ s, E (ball (c i) (r i)) (m i))
variable (hlower : ∀ L m, 0 < L → -A * m ≤ E (ball (0 : Position) L) m)
variable (hvacuum : ∀ L, 0 < L → E (ball (0 : Position) L) 0 = 0)
variable (e : ℝ → ℝ)
variable (he : ∀ ρ, 0 ≤ ρ → Tendsto (canonicalBallSequence E ρ) atTop (𝓝 (e ρ)))

include hpacking hlower in
theorem canonicalBall_vacuum_of_lower_bound_and_packing {L : ℝ} (hL : 0 < L) :
    E (ball (0 : Position) L) 0 = 0 := by
  classical
  have hhi := hpacking L ∅ (fun _ => 0) (fun _ => 1) (fun _ => 0) hL
    (by simp) (by simp) (by simp)
  simp only [sum_empty] at hhi
  have hlo := hlower L 0 hL
  simp only [Nat.cast_zero, mul_zero] at hlo
  exact le_antisymm hhi hlo

include htranslation hpacking hlower he in
theorem canonicalLimit_midpoint :
    ∀ x, 0 ≤ x → ∀ y, 0 ≤ y → e ((x + y) / 2) ≤ (e x + e y) / 2 := by
  apply midpoint_of_finite_defect_packing he
    (fun ρ hρ => canonicalLimit_defect_tendsto htranslation hpacking hlower hρ)
  intro n x y hx hy
  exact canonicalBallSequence_midpoint htranslation hpacking hx hy n

include htranslation hpacking hlower hvacuum he in
theorem canonicalLimit_zero : e 0 = 0 := by
  have hb := canonicalLimit_bounds htranslation hpacking hlower e he (ρ := 0) le_rfl
  rw [canonicalBallSequence_vacuum hvacuum] at hb
  simp only [mul_zero] at hb
  exact le_antisymm hb.2 hb.1

include htranslation hpacking hlower hvacuum he in
theorem canonicalLimit_continuousOn : ContinuousOn e (Ici 0) := by
  have hu : ContinuousOn (fun ρ => (1 / 28 : ℝ) * canonicalBallSequence E ρ 0) (Ici 0) :=
    continuousOn_const.mul (canonicalBallSequence_continuousOn E 0)
  apply continuousOn_limit_of_midpoint_and_seed
    (δ := 1 / (28 * ballVolumeConstant)) (B := E (ball (0 : Position) 1) 1)
    (canonicalLimit_midpoint htranslation hpacking hlower e he) hu
    (fun ρ hρ => (canonicalLimit_bounds htranslation hpacking hlower e he hρ).1)
    (fun ρ hρ => (canonicalLimit_bounds htranslation hpacking hlower e he hρ).2)
  · rw [canonicalBallSequence_vacuum hvacuum, mul_zero]
  · exact div_pos zero_lt_one (mul_pos (by norm_num) ballVolumeConstant_pos)
  · intro ρ hρ
    rw [canonicalBallSequence_seed_small (hvacuum 1 zero_lt_one) hρ]
    exact mul_comm _ _

include htranslation hpacking hlower hvacuum he in
theorem canonicalLimit_convexOn : ConvexOn ℝ (Ici 0) e :=
  convexOn_nonneg_of_midpoint_and_continuous
    (canonicalLimit_midpoint htranslation hpacking hlower e he)
    (canonicalLimit_continuousOn htranslation hpacking hlower hvacuum e he)

theorem continuousOn_canonicalMajorant (E : Set Position → ℕ → ℝ) (n : ℕ) :
    ContinuousOn (fun ρ => renewalMajorant (canonicalBallSequence E ρ)
      (1 / 28) swissCheeseGamma n) (Ici 0) := by
  unfold renewalMajorant
  apply ContinuousOn.sub
    (continuousOn_const.mul (canonicalBallSequence_continuousOn E 0))
  apply continuousOn_const.mul
  apply continuousOn_finsetSum
  intro j _
  unfold renewalDefect
  apply ContinuousOn.sub
  · apply continuousOn_finsetSum
    intro k _
    exact continuousOn_const.mul (canonicalBallSequence_continuousOn E k)
  · exact canonicalBallSequence_continuousOn E (j + 1)

include htranslation hpacking hlower hvacuum he in
theorem canonicalLimit_uniform {I : Set ℝ} (hI : IsCompact I) (hI0 : I ⊆ Ici 0) :
    TendstoUniformlyOn (fun n ρ => canonicalBallSequence E ρ n) e atTop I := by
  have htail : TendstoUniformlyOn (fun n ρ => canonicalBallSequence E ρ (n + 1)) e atTop I := by
    apply renewal_tendstoUniformlyOn
      (H := fun n ρ => renewalMajorant (canonicalBallSequence E ρ)
        (1 / 28) swissCheeseGamma n)
      (d := fun n ρ => renewalDefect (canonicalBallSequence E ρ)
        (1 / 28) swissCheeseGamma n) hI
      (fun n => (continuousOn_canonicalMajorant E n).mono hI0)
      (fun ρ hρ => antitone_canonicalBallSequence_majorant htranslation hpacking hlower
        ⟨ρ, hI0 hρ⟩)
      ((canonicalLimit_continuousOn htranslation hpacking hlower hvacuum e he).mono hI0)
      (fun ρ hρ => canonicalLimit_majorant_tendsto htranslation hpacking hlower e he (hI0 hρ))
      (by norm_num : (0 : ℝ) < 1 / 28)
    · intro n ρ
      rw [renewalMajorant_succ]
      ring
    · intro n ρ
      rw [renewalMajorant_eq_add_defect _ _ _ (by norm_num [swissCheeseGamma])]
      ring
  rw [Metric.tendstoUniformlyOn_iff] at htail ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htail ε hε)
  refine eventually_atTop.mpr ⟨N + 1, ?_⟩
  intro n hn x hx
  have heq : n - 1 + 1 = n := by omega
  simpa only [heq] using hN (n - 1) (by omega) x hx

end LiebThirring.ThermoLimit

end
