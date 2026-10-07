/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.FirstNeumann
public import LiebThirring.TFLattice.ShiftOccupation
import all Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Sharp first-n Dirichlet and Neumann lattice moments

Both signs have a common constant depending only on q. The Dirichlet trial
is a translated Neumann occupation; the lower bound follows by occupation
minimality. Source: Lieb–Simon (1977) III.13, pp. 67–69 (sharp eigenvalue sums).
-/

@[expose] public section

namespace LiebThirring.TFLattice

noncomputable def fermiMomentConstant (q : ℕ) : ℝ :=
  fermiMomentUpperConstant q + 12 * Real.sqrt 3 + 42

theorem fermiMomentConstant_nonneg (q : ℕ) : 0 ≤ fermiMomentConstant q := by
  unfold fermiMomentConstant
  have h := fermiMomentUpperConstant_nonneg q
  positivity

theorem first_dirichlet_moment_lower {q : ℕ} (hq : 0 < q)
    {s : Finset (ModeIndex q)} (_hs : IsFilled IsDirichletIndex s) :
    (q : ℝ) * (Real.pi / 10) * fermiRadius q s.card ^ 5 -
      (12 * Real.sqrt 3 + 3) * (s.card : ℝ) ^ (4 / 3 : ℝ) ≤
        ∑ p ∈ s, (squaredRadius p.1 : ℝ) := by
  obtain ⟨t, htc, ht⟩ := exists_isFilled_neumann hq s.card
  have hl := first_neumann_moment_lower hq ht
  rw [htc] at hl
  exact hl.trans (sum_squaredRadius_le_of_isFilled ht (fun _ _ => trivial) htc)

theorem first_dirichlet_moment_upper {q : ℕ} (hq : 0 < q)
    {s : Finset (ModeIndex q)} (hs : IsFilled IsDirichletIndex s) :
    (∑ p ∈ s, (squaredRadius p.1 : ℝ)) ≤
      (q : ℝ) * (Real.pi / 10) * fermiRadius q s.card ^ 5 +
        (fermiMomentUpperConstant q + 39) * (s.card : ℝ) ^ (4 / 3 : ℝ) := by
  classical
  obtain ⟨t, htc, ht⟩ := exists_isFilled_neumann hq s.card
  have hshift : (t.image shiftMode).card = s.card := by
    rw [Finset.card_image_of_injective _ (shiftMode_injective q), htc]
  have hmin := sum_squaredRadius_le_of_isFilled hs
    (fun p hp => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
      exact isDirichletIndex_shiftMode r) hshift.symm
  have hc := sum_squaredRadius_shiftMode_le hq ht
  have hu := first_neumann_moment_upper hq ht
  rw [htc] at hc hu
  nlinarith only [hmin, hc, hu]

theorem first_neumann_moment_error_le {q : ℕ} (hq : 0 < q)
    {s : Finset (ModeIndex q)} (hs : IsFilled (fun _ => True) s) :
    |(∑ p ∈ s, (squaredRadius p.1 : ℝ)) -
      (q : ℝ) * (Real.pi / 10) * fermiRadius q s.card ^ 5| ≤
      fermiMomentConstant q * (s.card : ℝ) ^ (4 / 3 : ℝ) := by
  have hl := first_neumann_moment_lower hq hs
  have hu := first_neumann_moment_upper hq hs
  have hn := Real.rpow_nonneg (Nat.cast_nonneg s.card) (4 / 3 : ℝ)
  have hc := fermiMomentUpperConstant_nonneg q
  have hsqrt := Real.sqrt_nonneg (3 : ℝ)
  unfold fermiMomentConstant
  apply abs_le.mpr
  constructor <;> nlinarith only [hl, hu, hn, hc, hsqrt,
    mul_nonneg hn hc, mul_nonneg hn hsqrt]

theorem first_dirichlet_moment_error_le {q : ℕ} (hq : 0 < q)
    {s : Finset (ModeIndex q)} (hs : IsFilled IsDirichletIndex s) :
    |(∑ p ∈ s, (squaredRadius p.1 : ℝ)) -
      (q : ℝ) * (Real.pi / 10) * fermiRadius q s.card ^ 5| ≤
      fermiMomentConstant q * (s.card : ℝ) ^ (4 / 3 : ℝ) := by
  have hl := first_dirichlet_moment_lower hq hs
  have hu := first_dirichlet_moment_upper hq hs
  have hn := Real.rpow_nonneg (Nat.cast_nonneg s.card) (4 / 3 : ℝ)
  have hc := fermiMomentUpperConstant_nonneg q
  have hsqrt := Real.sqrt_nonneg (3 : ℝ)
  unfold fermiMomentConstant
  apply abs_le.mpr
  constructor <;> nlinarith only [hl, hu, hn, hc, hsqrt,
    mul_nonneg hn hc, mul_nonneg hn hsqrt]

end LiebThirring.TFLattice

end
