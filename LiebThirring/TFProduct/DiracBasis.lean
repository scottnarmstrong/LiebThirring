/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Count

/-! # The constant basis for a Dirac measure

This supplies the genuine empty-product L² base case: mass one, one constant
mode, and no spatial derivatives.
-/

@[expose] public section
open MeasureTheory Submodule Set
open scoped InnerProductSpace
namespace LiebThirring.TFProduct

variable {X J : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] (a : X)

/-- The constant unit amplitude in the actual Dirac L² carrier. -/
noncomputable def diracOne : Lp ℂ 2 (Measure.dirac a) :=
  (memLp_const (μ := Measure.dirac a) (p := 2) (1 : ℂ)).toLp (fun _ => 1)

omit [MeasurableSingletonClass X] in
theorem diracOne_ae : diracOne a =ᵐ[Measure.dirac a] fun _ => (1 : ℂ) :=
  (memLp_const (μ := Measure.dirac a) (p := 2) (1 : ℂ)).coeFn_toLp

theorem norm_diracOne : ‖diracOne a‖ = 1 := by
  rw [diracOne, Lp.norm_toLp, eLpNorm_dirac _ _ (by norm_num)]
  simp only [enorm_one, ENNReal.toReal_one]

theorem inner_diracOne (u : Lp ℂ 2 (Measure.dirac a)) :
    inner ℂ (diracOne a) u = u a := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, u x ∂Measure.dirac a := by
      apply integral_congr_ae
      filter_upwards [diracOne_ae a] with x hx
      simp only [hx, RCLike.inner_apply', map_one, one_mul]
    _ = u a := integral_dirac _ _

theorem orthonormal_diracOne [Unique J] :
    Orthonormal ℂ (fun _ : J => diracOne a) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  have hij : i = j := Subsingleton.elim _ _
  simp only [hij, ite_true, inner_self_eq_norm_sq_to_K, norm_diracOne]
  norm_num

theorem diracOne_span_orthogonal_eq_bot [Unique J] :
    (span ℂ (range (fun _ : J => diracOne a)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  rw [mem_bot]
  have hz : u a = 0 := (inner_diracOne a u).symm.trans
    (inner_right_of_mem_orthogonal (subset_span (mem_range_self (default : J))) hu)
  apply Lp.ext
  filter_upwards [ae_eq_dirac (fun x => u x), Lp.coeFn_zero ℂ 2 (Measure.dirac a)]
    with x hx hzero
  rw [hx, hzero]
  simpa only [Function.const_apply, Pi.zero_apply] using hz

/-- The complete singleton basis of Dirac L², for any singleton index carrier. -/
noncomputable def diracHilbertBasis [Unique J] :
    HilbertBasis J ℂ (Lp ℂ 2 (Measure.dirac a)) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_diracOne (J := J) a)
    (diracOne_span_orthogonal_eq_bot (J := J) a)

@[simp] theorem diracHilbertBasis_apply [Unique J] (j : J) :
    diracHilbertBasis (J := J) a j = diracOne a :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) j

end LiebThirring.TFProduct
end
