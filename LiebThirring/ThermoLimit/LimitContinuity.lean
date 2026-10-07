/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.Convexity
public import LiebThirring.ThermoLimit.Renewal
import Mathlib.Tactic

/-!
# Passing midpoint packing to the limit and controlling the endpoint

Internal analytic steps of limit convexity. All input inequalities are explicit;
the canonical assembly derives them from the preceding packing and renewal
lemmas. The linear seed estimate is local, as in the source.
-/

public section

open Filter Topology Set

namespace LiebThirring.ThermoLimit

theorem midpoint_of_finite_defect_packing
    {f d : ℕ → ℝ → ℝ} {e : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ x → Tendsto (fun n => f n x) atTop (𝓝 (e x)))
    (hd : ∀ x, 0 ≤ x → Tendsto (fun n => d n x) atTop (𝓝 0))
    (hpacking : ∀ n x y, 0 ≤ x → 0 ≤ y →
      f (n + 1) ((x + y) / 2) ≤
        (f (n + 1) x + d n x + f (n + 1) y + d n y) / 2) :
    ∀ x, 0 ≤ x → ∀ y, 0 ≤ y → e ((x + y) / 2) ≤ (e x + e y) / 2 := by
  intro x hx y hy
  have hxy : 0 ≤ (x + y) / 2 := by positivity
  have hleft := (hf _ hxy).comp (tendsto_add_atTop_nat 1)
  have hright := (((hf x hx).comp (tendsto_add_atTop_nat 1)).add (hd x hx)).add
    ((hf y hy).comp (tendsto_add_atTop_nat 1)) |>.add (hd y hy) |>.div_const 2
  simp only [add_zero] at hright
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall
    (fun n => hpacking n x y hx hy))

theorem locally_boundedAbove_of_continuous_majorant {e u : ℝ → ℝ}
    (hu : ContinuousOn u (Ici 0)) (hbound : ∀ y, 0 ≤ y → e y ≤ u y) :
    ∀ x, 0 < x → ∃ r > 0, r ≤ x ∧ ∃ U,
      ∀ y ∈ Icc (x - r) (x + r), e y ≤ U := by
  intro x hx
  have hsub : Icc (x - x / 2) (x + x / 2) ⊆ Ici (0 : ℝ) := by
    intro y hy
    change 0 ≤ y
    linarith only [hx, hy.1]
  obtain ⟨U, hU⟩ := (isCompact_Icc.bddAbove_image (hu.mono hsub))
  refine ⟨x / 2, half_pos hx, by linarith only [hx], U, ?_⟩
  intro y hy
  exact (hbound y (hsub hy)).trans (hU (mem_image_of_mem _ hy))

/-- Midpoint packing, a continuous upper seed, and its local vacuum formula
give continuity on the complete nonnegative density axis. -/
theorem continuousOn_limit_of_midpoint_and_seed {e u : ℝ → ℝ} {A B δ : ℝ}
    (hmid : ∀ x, 0 ≤ x → ∀ y, 0 ≤ y → e ((x + y) / 2) ≤ (e x + e y) / 2)
    (hu : ContinuousOn u (Ici 0))
    (hlower : ∀ x, 0 ≤ x → -A * x ≤ e x)
    (hupper : ∀ x, 0 ≤ x → e x ≤ u x)
    (hu0 : u 0 = 0) (hδ : 0 < δ)
    (hseed : ∀ x ∈ Icc (0 : ℝ) δ, u x = B * x) :
    ContinuousOn e (Ici 0) := by
  have he0 : e 0 = 0 := by
    have hlo := hlower 0 le_rfl
    have hhi := hupper 0 le_rfl
    rw [hu0] at hhi
    simp only [mul_zero] at hlo
    exact le_antisymm hhi hlo
  apply continuousOn_nonneg_of_midpointConvex_of_bounds hmid
    (locally_boundedAbove_of_continuous_majorant hu hupper) he0 hlower hδ
  intro x hx
  rw [← hseed x hx]
  exact hupper x hx.1

end LiebThirring.ThermoLimit

end
