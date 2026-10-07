/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Renewal convergence for thermodynamic energy densities

A scalar renewal estimate. Indices are zero based:
`renewalDefect f α γ n` is the defect in the estimate for `f (n + 1)`.
-/

@[expose] public section

open Filter Finset Topology

namespace LiebThirring.ThermoLimit

/-- The defect in the renewal inequality for `f (n + 1)`. -/
def renewalDefect (f : ℕ → ℝ) (α γ : ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ range (n + 1), α * γ ^ (n - j) * f j) - f (n + 1)

/-- The decreasing majorant obtained by subtracting accumulated renewal defects. -/
def renewalMajorant (f : ℕ → ℝ) (α γ : ℝ) (n : ℕ) : ℝ :=
  α * f 0 - α * ∑ j ∈ range n, renewalDefect f α γ j

theorem renewalDefect_nonneg (f : ℕ → ℝ) (α γ : ℝ)
    (hrec : ∀ n, f (n + 1) ≤ ∑ j ∈ range (n + 1), α * γ ^ (n - j) * f j)
    (n : ℕ) :
    0 ≤ renewalDefect f α γ n := by
  unfold renewalDefect
  exact sub_nonneg.mpr (hrec n)

theorem renewalDefect_succ (f : ℕ → ℝ) (α γ : ℝ) (hαγ : α + γ = 1) (n : ℕ) :
    renewalDefect f α γ (n + 1) =
      γ * renewalDefect f α γ n + f (n + 1) - f (n + 2) := by
  rw [renewalDefect, renewalDefect, sum_range_succ]
  have hsum :
      (∑ x ∈ range (n + 1), α * γ ^ (n + 1 - x) * f x) =
        γ * ∑ x ∈ range (n + 1), α * γ ^ (n - x) * f x := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x hx
    have hxn : x ≤ n := Nat.le_of_lt_succ (mem_range.mp hx)
    rw [show n + 1 - x = (n - x) + 1 by omega, pow_succ]
    ring
  rw [hsum]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.add_assoc]
  have hα : α = 1 - γ := by linarith
  rw [hα]
  ring

theorem renewalMajorant_eq_add_defect (f : ℕ → ℝ) (α γ : ℝ)
    (hαγ : α + γ = 1) (n : ℕ) :
    renewalMajorant f α γ n = f (n + 1) + renewalDefect f α γ n := by
  induction n with
  | zero =>
      simp [renewalMajorant, renewalDefect]
  | succ n ih =>
      rw [renewalMajorant, sum_range_succ, mul_add, sub_add_eq_sub_sub,
        ← renewalMajorant]
      rw [ih, renewalDefect_succ f α γ hαγ n]
      have hα : α = 1 - γ := by linarith
      rw [hα]
      ring

theorem renewalMajorant_succ (f : ℕ → ℝ) (α γ : ℝ) (n : ℕ) :
    renewalMajorant f α γ (n + 1) =
      renewalMajorant f α γ n - α * renewalDefect f α γ n := by
  rw [renewalMajorant, renewalMajorant, sum_range_succ, mul_add]
  ring

theorem antitone_renewalMajorant (f : ℕ → ℝ) (α γ : ℝ) (hα : 0 ≤ α)
    (hdef : ∀ n, 0 ≤ renewalDefect f α γ n) :
    Antitone (renewalMajorant f α γ) := by
  exact antitone_nat_of_succ_le fun n => by
    rw [renewalMajorant_succ]
    exact sub_le_self _ (mul_nonneg hα (hdef n))

/-- A renewal inequality with a uniform lower bound has a finite limit.  Its
defects are nonnegative and tend to zero, while the canonical majorants decrease
to the same limit. -/
theorem renewal_convergence (f : ℕ → ℝ) (α γ m : ℝ)
    (hγ1 : γ < 1) (hα : α = 1 - γ)
    (hrec : ∀ n, f (n + 1) ≤ ∑ j ∈ range (n + 1), α * γ ^ (n - j) * f j)
    (hlower : ∀ n, m ≤ f (n + 1)) :
    ∃ e : ℝ,
      Tendsto f atTop (𝓝 e) ∧
      m ≤ e ∧ e ≤ α * f 0 ∧
      (∀ n, 0 ≤ renewalDefect f α γ n) ∧
      Tendsto (renewalDefect f α γ) atTop (𝓝 0) ∧
      Antitone (renewalMajorant f α γ) ∧
      Tendsto (renewalMajorant f α γ) atTop (𝓝 e) ∧
      ∀ n, renewalMajorant f α γ n = f (n + 1) + renewalDefect f α γ n := by
  have hα0 : 0 < α := by rw [hα]; linarith
  have hαγ : α + γ = 1 := by rw [hα]; ring
  have hdef : ∀ n, 0 ≤ renewalDefect f α γ n :=
    renewalDefect_nonneg f α γ hrec
  have hmajorant_eq : ∀ n, renewalMajorant f α γ n =
      f (n + 1) + renewalDefect f α γ n :=
    renewalMajorant_eq_add_defect f α γ hαγ
  have hmajorant_lower : ∀ n, m ≤ renewalMajorant f α γ n := by
    intro n
    rw [hmajorant_eq n]
    exact (hlower n).trans (le_add_of_nonneg_right (hdef n))
  have hanti : Antitone (renewalMajorant f α γ) :=
    antitone_renewalMajorant f α γ hα0.le hdef
  let e := ⨅ n, renewalMajorant f α γ n
  have hbdd : BddBelow (Set.range (renewalMajorant f α γ)) := by
    exact ⟨m, by rintro _ ⟨n, rfl⟩; exact hmajorant_lower n⟩
  have hmajorant_tendsto : Tendsto (renewalMajorant f α γ) atTop (𝓝 e) :=
    tendsto_atTop_ciInf hanti hbdd
  have he_lower : m ≤ e := by
    exact le_ciInf hmajorant_lower
  have he_upper : e ≤ α * f 0 := by
    have hle := hanti.le_of_tendsto hmajorant_tendsto 0
    simpa [renewalMajorant] using hle
  have hsum_bound : ∀ n, ∑ j ∈ range n, renewalDefect f α γ j ≤
      (α * f 0 - m) / α := by
    intro n
    have h := hmajorant_lower n
    rw [renewalMajorant] at h
    apply (le_div_iff₀ hα0).2
    linarith
  have hsummable : Summable (renewalDefect f α γ) :=
    summable_of_sum_range_le hdef hsum_bound
  have hdef_tendsto : Tendsto (renewalDefect f α γ) atTop (𝓝 0) :=
    hsummable.tendsto_atTop_zero
  have htail_tendsto : Tendsto (fun n => f (n + 1)) atTop (𝓝 e) := by
    have := hmajorant_tendsto.sub hdef_tendsto
    simpa only [hmajorant_eq, add_sub_cancel_right, sub_zero] using this
  have hf_tendsto : Tendsto f atTop (𝓝 e) := by
    exact (tendsto_add_atTop_iff_nat 1).mp (by simpa [Nat.add_comm] using htail_tendsto)
  exact ⟨e, hf_tendsto, he_lower, he_upper, hdef, hdef_tendsto, hanti,
    hmajorant_tendsto, hmajorant_eq⟩

end LiebThirring.ThermoLimit

end
