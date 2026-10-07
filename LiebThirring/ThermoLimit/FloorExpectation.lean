/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoLimit.Interpolation
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Expectation of randomly shifted integer floors

Uniformly shifting a nonnegative real number by `u ∈ [0,1)` rounds it to its
two adjacent natural numbers with the linear-interpolation weights.
-/

@[expose] public section

open MeasureTheory Set

namespace LiebThirring.ThermoLimit

/-- The natural floor is constant on each nonnegative unit interval. -/
theorem natFloor_eq_of_mem_Ico (n : ℕ) {x : ℝ}
    (hx : x ∈ Ico (n : ℝ) (n + 1 : ℝ)) :
    natFloor x = n := by
  have hfloor : ⌊x⌋ = (n : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact hx.1
    · simpa only [Int.cast_natCast, Nat.cast_add, Nat.cast_one] using hx.2
  simp [natFloor, hfloor]

theorem sub_natFloor_lt_one {s : ℝ} (hs : 0 ≤ s) :
    s - (natFloor s : ℝ) < 1 := by
  have hfloor_nonneg : 0 ≤ ⌊s⌋ := Int.floor_nonneg.mpr hs
  have hcast : ((natFloor s : ℕ) : ℝ) = (⌊s⌋ : ℤ) := by
    rw [natFloor]
    exact_mod_cast Int.toNat_of_nonneg hfloor_nonneg
  rw [hcast]
  linarith [Int.lt_floor_add_one s]

/-- Below the complementary fractional threshold, shifted floor rounding selects
the lower adjacent natural number. -/
theorem natFloor_add_eq_of_lt {s u : ℝ} (hs : 0 ≤ s) (hu0 : 0 ≤ u)
    (hu : u < 1 - (s - (natFloor s : ℝ))) :
    natFloor (s + u) = natFloor s := by
  apply natFloor_eq_of_mem_Ico (natFloor s)
  have ht := sub_floor_mem_Icc hs
  constructor
  · have hn : (natFloor s : ℝ) ≤ s := by linarith [ht.1]
    exact hn.trans (le_add_of_nonneg_right hu0)
  · linarith

/-- At or above the complementary fractional threshold (but below one), shifted
floor rounding selects the upper adjacent natural number. -/
theorem natFloor_add_eq_succ_of_le {s u : ℝ} (hs : 0 ≤ s)
    (hu : 1 - (s - (natFloor s : ℝ)) ≤ u) (hu1 : u < 1) :
    natFloor (s + u) = natFloor s + 1 := by
  apply natFloor_eq_of_mem_Ico (natFloor s + 1)
  have ht := sub_natFloor_lt_one hs
  constructor <;> push_cast
  · linarith
  · linarith

/-- The shifted-floor function is integrable on the unit interval. -/
theorem integrableOn_comp_natFloor_add (F : ℕ → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    IntegrableOn (fun u => F (natFloor (s + u))) (Ico (0 : ℝ) 1) := by
  let n := natFloor s
  let a := 1 - (s - (n : ℝ))
  have ha : a ∈ Icc (0 : ℝ) 1 := by
    have ht := sub_floor_mem_Icc hs
    dsimp [a, n]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hA : EqOn (fun u => F (natFloor (s + u))) (fun _ => F n) (Ico 0 a) := by
    intro u hu
    change F (natFloor (s + u)) = F n
    rw [natFloor_add_eq_of_lt hs hu.1 (by simpa [a, n] using hu.2)]
  have hB : EqOn (fun u => F (natFloor (s + u))) (fun _ => F (n + 1)) (Ico a 1) := by
    intro u hu
    change F (natFloor (s + u)) = F (n + 1)
    rw [natFloor_add_eq_succ_of_le hs (by simpa [a, n] using hu.1) hu.2]
  have hIA : IntegrableOn (fun u => F (natFloor (s + u))) (Ico 0 a) :=
    (integrableOn_const measure_Ico_lt_top.ne :
      IntegrableOn (fun _ : ℝ => F n) (Ico 0 a)).congr_fun hA.symm measurableSet_Ico
  have hIB : IntegrableOn (fun u => F (natFloor (s + u))) (Ico a 1) :=
    (integrableOn_const measure_Ico_lt_top.ne :
      IntegrableOn (fun _ : ℝ => F (n + 1)) (Ico a 1)).congr_fun hB.symm measurableSet_Ico
  rw [(Ico_union_Ico_eq_Ico ha.1 ha.2).symm]
  exact hIA.union hIB

/-- Uniform shifted-floor rounding realizes linear interpolation exactly. -/
theorem integral_comp_natFloor_add (F : ℕ → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ∫ u in Ico (0 : ℝ) 1, F (natFloor (s + u)) = interpolate F s := by
  let n := natFloor s
  let t := s - (n : ℝ)
  let a := 1 - t
  have ht : t ∈ Icc (0 : ℝ) 1 := sub_floor_mem_Icc hs
  have ha : a ∈ Icc (0 : ℝ) 1 := by
    dsimp [a]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hA : EqOn (fun u => F (natFloor (s + u))) (fun _ => F n) (Ico 0 a) := by
    intro u hu
    change F (natFloor (s + u)) = F n
    rw [natFloor_add_eq_of_lt hs hu.1 (by simpa [a, t, n] using hu.2)]
  have hB : EqOn (fun u => F (natFloor (s + u))) (fun _ => F (n + 1)) (Ico a 1) := by
    intro u hu
    change F (natFloor (s + u)) = F (n + 1)
    rw [natFloor_add_eq_succ_of_le hs (by simpa [a, t, n] using hu.1) hu.2]
  have hIA : IntegrableOn (fun u => F (natFloor (s + u))) (Ico 0 a) :=
    (integrableOn_const measure_Ico_lt_top.ne :
      IntegrableOn (fun _ : ℝ => F n) (Ico 0 a)).congr_fun hA.symm measurableSet_Ico
  have hIB : IntegrableOn (fun u => F (natFloor (s + u))) (Ico a 1) :=
    (integrableOn_const measure_Ico_lt_top.ne :
      IntegrableOn (fun _ : ℝ => F (n + 1)) (Ico a 1)).congr_fun hB.symm measurableSet_Ico
  have hunion : Ico (0 : ℝ) 1 = Ico 0 a ∪ Ico a 1 :=
    (Ico_union_Ico_eq_Ico ha.1 ha.2).symm
  rw [hunion, setIntegral_union Ico_disjoint_Ico_same measurableSet_Ico hIA hIB]
  rw [setIntegral_congr_fun measurableSet_Ico hA, setIntegral_congr_fun measurableSet_Ico hB]
  rw [setIntegral_const, setIntegral_const]
  simp only [Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal,
    sub_nonneg.mpr ha.2, sub_zero, smul_eq_mul]
  rw [ENNReal.toReal_ofReal ha.1]
  change a * F n + (1 - a) * F (n + 1) = interpolate F s
  simp only [interpolate, n, t, a]
  ring

/-- In particular, the expectation of the shifted natural floor is the original
nonnegative real number. -/
theorem integral_natFloor_add {s : ℝ} (hs : 0 ≤ s) :
    ∫ u in Ico (0 : ℝ) 1, (natFloor (s + u) : ℝ) = s := by
  rw [integral_comp_natFloor_add (fun n => (n : ℝ)) hs]
  simp only [interpolate]
  push_cast
  ring

end LiebThirring.ThermoLimit

end
