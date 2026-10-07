/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFFunctional.CompactApproximationInterpolation

/-! # Joint compact continuous approximation of Thomas--Fermi densities -/

public section

open MeasureTheory Set Filter Finset
open scoped ENNReal NNReal Topology
namespace LiebThirring.TFFunctional

/-- Every TF density has nonnegative compactly supported continuous approximants
simultaneously in L1 and L5/3. -/
theorem exists_compact_nonneg_joint_approximation (ρ : TFDensity) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : Position → ℝ, (∀ x, 0 ≤ f x) ∧ Continuous f ∧ HasCompactSupport f ∧
      eLpNorm (f - (ρ.val : Position → ℝ)) ((5 : ℝ≥0∞) / 3) volume ≤ ENNReal.ofReal ε ∧
      eLpNorm (f - (ρ.val : Position → ℝ)) 1 volume ≤ ENNReal.ofReal ε := by
  let u : Position → ℝ := fun x => max 0 ((ρ.val : Position → ℝ) x)
  have hueq : u =ᵐ[volume] (ρ.val : Position → ℝ) := by
    filter_upwards [ρ.property.1] with x hx
    simp [u, max_eq_right hx]
  have humeas : Measurable u := measurable_const.max (Lp.stronglyMeasurable ρ.val).measurable
  have hu5 : MemLp u ((5 : ℝ≥0∞) / 3) volume :=
    (memLp_congr_ae hueq).2 (Lp.memLp ρ.val)
  have hu1 : MemLp u 1 volume :=
    (memLp_congr_ae hueq).2 (memLp_one_iff_integrable.mpr ρ.property.2)
  let s : ℕ → SimpleFunc Position ℝ := fun n => SimpleFunc.approxOn u humeas
    (range u ∪ {0}) 0 (by simp) n
  have hs5 := SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm
    (p := (5 : ℝ≥0∞) / 3) (ENNReal.div_ne_top (by norm_num) (by norm_num))
      humeas hu5.eLpNorm_lt_top
  have hs1 := SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm
    (p := (1 : ℝ≥0∞)) ENNReal.one_ne_top humeas hu1.eLpNorm_lt_top
  have hhalf : 0 < ε / 2 := half_pos hε
  have hepos : 0 < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr hhalf
  obtain ⟨n, hn5, hn1⟩ := ((hs5.eventually_lt_const hepos).and
    (hs1.eventually_lt_const hepos)).exists
  let sn : SimpleFunc Position ℝ := s n
  have hsn0 : ∀ x, 0 ≤ sn x := by
    intro x
    exact SimpleFunc.approxOn_range_nonneg (fun x => le_max_left 0 (ρ.val x)) n x
  let C : ℝ≥0 := ⟨∑ y ∈ sn.range, |y|, sum_nonneg fun _ _ => abs_nonneg _⟩
  have hsnC : ∀ x, sn x ≤ (C : ℝ) := by
    intro x
    calc
      sn x ≤ |sn x| := le_abs_self _
      _ ≤ ∑ y ∈ sn.range, |y| := single_le_sum (fun y _ => abs_nonneg y) (sn.mem_range_self x)
      _ = (C : ℝ) := rfl
  have hsnint : Integrable sn volume :=
    SimpleFunc.integrable_approxOn_range humeas (memLp_one_iff_integrable.mp hu1) n
  obtain ⟨f, hf0, hfcont, hfcomp, hf5, hf1⟩ :=
    exists_compact_nonneg_joint_approximation_of_bounded sn hsnint C
      (Eventually.of_forall hsn0) (Eventually.of_forall hsnC) (ε / 2) hhalf
  refine ⟨f, hf0, hfcont, hfcomp, ?_, ?_⟩
  · calc
      eLpNorm (f - (ρ.val : Position → ℝ)) ((5 : ℝ≥0∞) / 3) volume =
          eLpNorm (f - u) ((5 : ℝ≥0∞) / 3) volume :=
        eLpNorm_congr_ae (EventuallyEq.rfl.sub hueq.symm)
      _ ≤ eLpNorm (f - (sn : Position → ℝ)) ((5 : ℝ≥0∞) / 3) volume +
          eLpNorm ((sn : Position → ℝ) - u) ((5 : ℝ≥0∞) / 3) volume := by
        simpa only [sub_add_sub_cancel] using
          (eLpNorm_add_le (f := f - (sn : Position → ℝ))
            (g := (sn : Position → ℝ) - u) (by
              rw [ENNReal.le_div_iff_mul_le]
              all_goals norm_num : (1 : ℝ≥0∞) ≤ (5 : ℝ≥0∞) / 3))
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        add_le_add hf5 hn5.le
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add hhalf.le hhalf.le]; congr; ring
  · calc
      eLpNorm (f - (ρ.val : Position → ℝ)) 1 volume = eLpNorm (f - u) 1 volume :=
        eLpNorm_congr_ae (EventuallyEq.rfl.sub hueq.symm)
      _ ≤ eLpNorm (f - (sn : Position → ℝ)) 1 volume +
          eLpNorm ((sn : Position → ℝ) - u) 1 volume := by
        simpa only [sub_add_sub_cancel] using
          (eLpNorm_add_le (f := f - (sn : Position → ℝ))
            (g := (sn : Position → ℝ) - u) (le_rfl : (1 : ℝ≥0∞) ≤ 1))
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hf1 hn1.le
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add hhalf.le hhalf.le]; congr; ring

end LiebThirring.TFFunctional

end
