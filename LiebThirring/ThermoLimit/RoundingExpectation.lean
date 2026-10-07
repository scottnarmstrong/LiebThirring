/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.BalancedRounding
public import LiebThirring.ThermoLimit.FloorExpectation

/-! # Expected values of balanced finite roundings -/

@[expose] public section

open MeasureTheory Set

namespace LiebThirring.ThermoLimit

/-- The natural-valued version of prefix-floor rounding. -/
noncomputable def balancedRoundNat {k : ℕ} (x : Fin k → ℝ) (u : ℝ) (i : Fin k) : ℕ :=
  natFloor (budgetPrefix x (i.val + 1) + u) - natFloor (budgetPrefix x i.val + u)

theorem budgetPrefix_nonneg {k : ℕ} {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i)
    {j : ℕ} (hj : j ≤ k) : 0 ≤ budgetPrefix x j := by
  unfold budgetPrefix
  apply Finset.sum_nonneg
  intro i hi
  have hik : i < k := lt_of_lt_of_le (Finset.mem_range.mp hi) hj
  simp [hik, hx ⟨i, hik⟩]

theorem natFloor_budgetPrefix_mono {k : ℕ} {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i)
    (u : ℝ) (i : Fin k) :
    natFloor (budgetPrefix x i.val + u) ≤ natFloor (budgetPrefix x (i.val + 1) + u) := by
  apply Int.toNat_le_toNat
  apply Int.floor_mono
  rw [budgetPrefix_succ]
  linarith [hx i]

theorem balancedRoundNat_cast {k : ℕ} {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i)
    (u : ℝ) (i : Fin k) :
    (balancedRoundNat x u i : ℝ) =
      (natFloor (budgetPrefix x (i.val + 1) + u) : ℝ) -
        natFloor (budgetPrefix x i.val + u) := by
  rw [balancedRoundNat, Nat.cast_sub (natFloor_budgetPrefix_mono hx u i)]

theorem balancedRoundNat_eq_int_toNat {k : ℕ} {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i)
    {u : ℝ} (hu : 0 ≤ u) (i : Fin k) :
    balancedRoundNat x u i = (balancedRound x u i).toNat := by
  have hp0 : 0 ≤ budgetPrefix x i.val := budgetPrefix_nonneg hx (Nat.le_of_lt i.isLt)
  have hp1 : 0 ≤ budgetPrefix x (i.val + 1) :=
    budgetPrefix_nonneg hx (Nat.succ_le_iff.mpr i.isLt)
  have hf0 : 0 ≤ ⌊budgetPrefix x i.val + u⌋ := Int.floor_nonneg.mpr (add_nonneg hp0 hu)
  have hf1 : 0 ≤ ⌊budgetPrefix x (i.val + 1) + u⌋ :=
    Int.floor_nonneg.mpr (add_nonneg hp1 hu)
  have hmono : ⌊budgetPrefix x i.val + u⌋ ≤ ⌊budgetPrefix x (i.val + 1) + u⌋ := by
    apply Int.floor_mono
    rw [budgetPrefix_succ]
    linarith [hx i]
  simp only [balancedRoundNat, natFloor, balancedRound]
  omega

theorem abs_balancedRoundNat_sub_lt_one {k : ℕ} {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i)
    {u : ℝ} (hu : 0 ≤ u) (i : Fin k) :
    |(balancedRoundNat x u i : ℝ) - x i| < 1 := by
  have heq := balancedRoundNat_eq_int_toNat hx hu i
  have hint : 0 ≤ balancedRound x u i := by
    rw [balancedRound]
    exact sub_nonneg.mpr (by
      apply Int.floor_mono
      rw [budgetPrefix_succ]
      linarith [hx i])
  have hcast : (balancedRoundNat x u i : ℝ) = (balancedRound x u i : ℝ) := by
    rw [heq]
    have hz := Int.toNat_of_nonneg hint
    exact_mod_cast hz
  rw [hcast]
  exact abs_balancedRound_sub_lt_one x u i

/-- An integer strictly within one of a nonnegative real budget is one of its two adjacent
integers, so its energy is the affine expression used by interpolation. -/
theorem value_eq_affine_of_nat_close (F : ℕ → ℝ) {x : ℝ} (hx : 0 ≤ x) (m : ℕ)
    (hm : |(m : ℝ) - x| < 1) :
    F m = F (natFloor x) + ((m : ℝ) - natFloor x) *
      (F (natFloor x + 1) - F (natFloor x)) := by
  have ht := sub_floor_mem_Icc hx
  have hmx : (m : ℝ) < x + 1 := by rw [abs_lt] at hm; linarith [hm.2]
  have hxm : x - 1 < (m : ℝ) := by rw [abs_lt] at hm; linarith [hm.1]
  have hfrac : x - (natFloor x : ℝ) < 1 := sub_natFloor_lt_one hx
  have hmle : m ≤ natFloor x + 1 := by
    have hr : (m : ℝ) < ((natFloor x + 2 : ℕ) : ℝ) := by push_cast; linarith
    have hn : m < natFloor x + 2 := by exact_mod_cast hr
    omega
  have hle : natFloor x ≤ m := by
    by_contra h
    have hmle' : m + 1 ≤ natFloor x := by omega
    have : (m : ℝ) + 1 ≤ natFloor x := by exact_mod_cast hmle'
    linarith [ht.1]
  have hm_cases : m = natFloor x ∨ m = natFloor x + 1 := by omega
  rcases hm_cases with rfl | rfl <;> simp

/-- Every regional rounded count has expectation equal to its real budget. -/
theorem integral_balancedRoundNat {k : ℕ} {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i)
    (i : Fin k) :
    ∫ u in Ico (0 : ℝ) 1, (balancedRoundNat x u i : ℝ) = x i := by
  have hp0 : 0 ≤ budgetPrefix x i.val := budgetPrefix_nonneg hx (Nat.le_of_lt i.isLt)
  have hp1 : 0 ≤ budgetPrefix x (i.val + 1) :=
    budgetPrefix_nonneg hx (Nat.succ_le_iff.mpr i.isLt)
  have hI0 := integrableOn_comp_natFloor_add (fun n => (n : ℝ)) hp0
  have hI1 := integrableOn_comp_natFloor_add (fun n => (n : ℝ)) hp1
  rw [setIntegral_congr_fun measurableSet_Ico (fun u _ => balancedRoundNat_cast hx u i)]
  rw [integral_sub hI1 hI0, integral_natFloor_add hp1, integral_natFloor_add hp0]
  rw [budgetPrefix_succ]
  ring

/-- Applying any sector energy to a regional balanced rounding has expectation equal to its
linear interpolation at the real budget. -/
theorem integral_comp_balancedRoundNat {k : ℕ} (G : ℕ → ℝ) {x : Fin k → ℝ}
    (hx : ∀ i, 0 ≤ x i) (i : Fin k) :
    ∫ u in Ico (0 : ℝ) 1, G (balancedRoundNat x u i) = interpolate G (x i) := by
  let n := natFloor (x i)
  let a := G (n + 1) - G n
  have hp0 : 0 ≤ budgetPrefix x i.val := budgetPrefix_nonneg hx (Nat.le_of_lt i.isLt)
  have hp1 : 0 ≤ budgetPrefix x (i.val + 1) :=
    budgetPrefix_nonneg hx (Nat.succ_le_iff.mpr i.isLt)
  have hI0 := integrableOn_comp_natFloor_add (fun q => (q : ℝ)) hp0
  have hI1 := integrableOn_comp_natFloor_add (fun q => (q : ℝ)) hp1
  have hround : IntegrableOn (fun u => (balancedRoundNat x u i : ℝ)) (Ico 0 1) := by
    refine (hI1.sub hI0).congr_fun ?_ measurableSet_Ico
    intro u hu
    symm
    exact balancedRoundNat_cast hx u i
  have hfun : EqOn (fun u => G (balancedRoundNat x u i))
      (fun u => G n + ((balancedRoundNat x u i : ℝ) - n) * a) (Ico 0 1) := by
    intro u hu
    exact value_eq_affine_of_nat_close G (hx i) _
      (abs_balancedRoundNat_sub_lt_one hx hu.1 i)
  have hconst : IntegrableOn (fun _ : ℝ => G n) (Ico 0 1) :=
    integrableOn_const measure_Ico_lt_top.ne
  have hnconst : IntegrableOn (fun _ : ℝ => (n : ℝ)) (Ico 0 1) :=
    integrableOn_const measure_Ico_lt_top.ne
  have hsub := hround.sub hnconst
  have hmul := hsub.mul_const a
  have hsubint :
      (∫ u in Ico (0 : ℝ) 1, (((fun v => (balancedRoundNat x v i : ℝ)) -
        fun _ : ℝ => (n : ℝ)) u)) = x i - n := by
    change (∫ u in Ico (0 : ℝ) 1, (balancedRoundNat x u i : ℝ) - (n : ℝ)) = _
    rw [integral_sub hround hnconst, integral_balancedRoundNat hx i, setIntegral_const]
    simp only [Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal, zero_le_one, sub_zero,
      one_smul]
  rw [setIntegral_congr_fun measurableSet_Ico hfun]
  change (∫ u in Ico (0 : ℝ) 1,
    (fun _ : ℝ => G n) u + (((fun v => (balancedRoundNat x v i : ℝ)) -
      fun _ : ℝ => (n : ℝ)) u) * a) = interpolate G (x i)
  rw [integral_add hconst hmul]
  rw [setIntegral_const, integral_mul_const, hsubint]
  simp only [Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal, zero_le_one, sub_zero,
    one_smul]
  change G n + (x i - n) * a = interpolate G (x i)
  simp only [interpolate, n, a]
  ring

theorem integrableOn_comp_balancedRoundNat {k : ℕ} (G : ℕ → ℝ) {x : Fin k → ℝ}
    (hx : ∀ i, 0 ≤ x i) (i : Fin k) :
    IntegrableOn (fun u => G (balancedRoundNat x u i)) (Ico (0 : ℝ) 1) := by
  let n := natFloor (x i)
  let a := G (n + 1) - G n
  have hp0 : 0 ≤ budgetPrefix x i.val := budgetPrefix_nonneg hx (Nat.le_of_lt i.isLt)
  have hp1 : 0 ≤ budgetPrefix x (i.val + 1) :=
    budgetPrefix_nonneg hx (Nat.succ_le_iff.mpr i.isLt)
  have hI0 := integrableOn_comp_natFloor_add (fun q => (q : ℝ)) hp0
  have hI1 := integrableOn_comp_natFloor_add (fun q => (q : ℝ)) hp1
  have hround : IntegrableOn (fun u => (balancedRoundNat x u i : ℝ)) (Ico 0 1) := by
    refine (hI1.sub hI0).congr_fun ?_ measurableSet_Ico
    intro u hu
    symm
    exact balancedRoundNat_cast hx u i
  have haffine : IntegrableOn
      (fun u => G n + ((balancedRoundNat x u i : ℝ) - n) * a) (Ico 0 1) :=
    (integrableOn_const measure_Ico_lt_top.ne).add
      ((hround.sub (integrableOn_const measure_Ico_lt_top.ne)).mul_const a)
  refine haffine.congr_fun ?_ measurableSet_Ico
  intro u hu
  symm
  exact value_eq_affine_of_nat_close G (hx i) _
    (abs_balancedRoundNat_sub_lt_one hx hu.1 i)

/-- The coupled allocation has the shifted floor of the total budget as its exact total. -/
theorem sum_balancedRoundNat {k : ℕ} {x : Fin k → ℝ} (hx : ∀ i, 0 ≤ x i)
    {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    ∑ i, balancedRoundNat x u i = natFloor ((∑ i, x i) + u) := by
  have hsumx : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
  have hflooru : ⌊u⌋ = 0 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · norm_num
      exact hu.1
    · norm_num
      exact hu.2
  have hfloor_total : 0 ≤ ⌊(∑ i, x i) + u⌋ :=
    Int.floor_nonneg.mpr (add_nonneg hsumx hu.1)
  apply Nat.cast_injective (R := ℤ)
  push_cast
  calc
    (∑ i, (balancedRoundNat x u i : ℤ)) = ∑ i, balancedRound x u i := by
      apply Finset.sum_congr rfl
      intro i _
      have hri : 0 ≤ balancedRound x u i := by
        rw [balancedRound]
        exact sub_nonneg.mpr (by
          apply Int.floor_mono
          rw [budgetPrefix_succ]
          linarith [hx i])
      rw [balancedRoundNat_eq_int_toNat hx hu.1 i, Int.toNat_of_nonneg hri]
    _ = ⌊(∑ i, x i) + u⌋ := by rw [sum_balancedRound, hflooru, sub_zero]
    _ = (natFloor ((∑ i, x i) + u) : ℤ) := by
      rw [natFloor, Int.toNat_of_nonneg hfloor_total]

end LiebThirring.ThermoLimit

end
