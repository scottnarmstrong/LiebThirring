/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCoulomb.CubeKernel
public import LiebThirring.Electrostatics.CoulombPositivity
public import LiebThirring.TFCoulomb.NearEstimate

/-! # The discrete Coulomb functional and its continuum comparison

The countable sum is over every ordered pair of lattice labels,
including equal labels.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring.TFCoulomb

/-- The box kernel evaluated at the unique half-open cube labels. -/
@[expose] noncomputable def boxCoulombKernel (ℓ : ℝ) (x y : Position) : ℝ≥0∞ :=
  ENNReal.ofReal (cubeWeight ℓ (latticeLabel ℓ x) (latticeLabel ℓ y))

/-- The literal discretized half-energy, including diagonal cube pairs. -/
@[expose] noncomputable def boxCoulombEnergy (ℓ : ℝ) (μ : Measure Position) : ℝ≥0∞ :=
  (∑' β : LatticeIndex, ∑' γ : LatticeIndex,
    ENNReal.ofReal (cubeWeight ℓ β γ) * μ (latticeCell ℓ β) * μ (latticeCell ℓ γ)) / 2

/-- The real discrete TF Coulomb functional. Finiteness is proved below. -/
@[expose] noncomputable def tfBoxCoulombEnergy (ℓ : ℝ) (ρ : TFDensity) : ℝ :=
  (boxCoulombEnergy ℓ (tfDensityMeasure ρ)).toReal

theorem measurable_latticeLabel {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Measurable (latticeLabel ℓ) := by
  apply measurable_to_countable
  intro y
  have heq : (latticeLabel ℓ) ⁻¹' {latticeLabel ℓ y} = latticeCell ℓ (latticeLabel ℓ y) := by
    ext x
    constructor
    · intro hx
      have he : latticeLabel ℓ x = latticeLabel ℓ y := hx
      rw [← he]
      exact mem_latticeCell_label hℓ x
    · intro hx
      exact latticeLabel_eq_of_mem hℓ hx
  rw [heq]
  exact measurableSet_latticeCell _ _

theorem measurable_cubeWeight (ℓ : ℝ) :
    Measurable (fun p : LatticeIndex × LatticeIndex => ENNReal.ofReal (cubeWeight ℓ p.1 p.2)) :=
  measurable_of_countable _

theorem measurable_pair_latticeLabel {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Measurable (fun p : Position × Position => (latticeLabel ℓ p.1, latticeLabel ℓ p.2)) :=
  ((measurable_latticeLabel hℓ).comp measurable_fst).prodMk
    ((measurable_latticeLabel hℓ).comp measurable_snd)

theorem measurable_boxCoulombKernel {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Measurable (Function.uncurry (boxCoulombKernel ℓ)) := by
  change Measurable ((fun p : LatticeIndex × LatticeIndex =>
    ENNReal.ofReal (cubeWeight ℓ p.1 p.2)) ∘
      (fun p : Position × Position => (latticeLabel ℓ p.1, latticeLabel ℓ p.2)))
  exact (measurable_cubeWeight ℓ).comp (measurable_pair_latticeLabel hℓ)

theorem measurable_boxCoulombKernel_right {ℓ : ℝ} (hℓ : 0 < ℓ) (x : Position) :
    Measurable (boxCoulombKernel ℓ x) :=
  (measurable_boxCoulombKernel hℓ).of_uncurry_left

theorem boxCoulombKernel_le {ℓ : ℝ} (hℓ : 0 < ℓ) (x y : Position) :
    boxCoulombKernel ℓ x y ≤ coulombKernel x y :=
  ofReal_cubeWeight_le_coulombKernel hℓ
    (latticeCell_subset_closedCell _ _ (mem_latticeCell_label hℓ x))
    (latticeCell_subset_closedCell _ _ (mem_latticeCell_label hℓ y))

theorem lintegral_boxCoulombKernel {ℓ : ℝ} (hℓ : 0 < ℓ) (μ : Measure Position)
    (x : Position) :
    (∫⁻ y, boxCoulombKernel ℓ x y ∂μ) =
      ∑' γ : LatticeIndex, ENNReal.ofReal (cubeWeight ℓ (latticeLabel ℓ x) γ) *
        μ (latticeCell ℓ γ) := by
  have he := lintegral_iUnion (μ := μ) (measurableSet_latticeCell ℓ)
    (fun β γ hne => latticeCell_disjoint hℓ hne) (boxCoulombKernel ℓ x)
  rw [iUnion_latticeCell hℓ, Measure.restrict_univ] at he
  rw [he]
  apply tsum_congr
  intro γ
  calc
    _ = ∫⁻ _y in latticeCell ℓ γ,
        ENNReal.ofReal (cubeWeight ℓ (latticeLabel ℓ x) γ) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_latticeCell ℓ γ)] with y hy
      rw [boxCoulombKernel, latticeLabel_eq_of_mem hℓ hy]
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

theorem boxCoulombEnergy_eq_lintegral {ℓ : ℝ} (hℓ : 0 < ℓ) (μ : Measure Position) :
    boxCoulombEnergy ℓ μ =
      (∫⁻ x, ∫⁻ y, boxCoulombKernel ℓ x y ∂μ ∂μ) / 2 := by
  unfold boxCoulombEnergy
  congr 1
  have he := lintegral_iUnion (μ := μ) (measurableSet_latticeCell ℓ)
    (fun β γ hne => latticeCell_disjoint hℓ hne)
    (fun x => ∫⁻ y, boxCoulombKernel ℓ x y ∂μ)
  rw [iUnion_latticeCell hℓ, Measure.restrict_univ] at he
  rw [he]
  apply tsum_congr
  intro β
  calc
    _ = (∑' γ : LatticeIndex,
        ENNReal.ofReal (cubeWeight ℓ β γ) * μ (latticeCell ℓ γ)) * μ (latticeCell ℓ β) := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro γ
      ac_rfl
    _ = _ := by
      symm
      calc
        _ = ∫⁻ _x in latticeCell ℓ β, ∑' γ : LatticeIndex,
            ENNReal.ofReal (cubeWeight ℓ β γ) * μ (latticeCell ℓ γ) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem (measurableSet_latticeCell ℓ β)] with x hx
          rw [lintegral_boxCoulombKernel hℓ, latticeLabel_eq_of_mem hℓ hx]
        _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

theorem boxCoulombEnergy_le {ℓ : ℝ} (hℓ : 0 < ℓ) (μ : Measure Position) :
    boxCoulombEnergy ℓ μ ≤ coulombEnergy μ μ / 2 := by
  rw [boxCoulombEnergy_eq_lintegral hℓ]
  apply ENNReal.div_le_div_right
  rw [coulombEnergy_eq_lintegral]
  exact lintegral_mono fun x => lintegral_mono (boxCoulombKernel_le hℓ x)

/-- Near/far kernel comparison with an explicit constant, even at collisions. -/
theorem coulombKernel_le_box_add_near {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s)
    (x y : Position) :
    coulombKernel x y ≤ boxCoulombKernel ℓ x y + nearCoulombKernel s x y +
      ENNReal.ofReal (2 * Real.sqrt 3 * ℓ / s ^ 2) := by
  by_cases hnear : ‖x - y‖ < s
  · rw [nearCoulombKernel, ite_eq_left hnear]
    exact (le_add_self).trans (le_add_right le_rfl)
  · have hfar : s ≤ dist x y := by simpa only [dist_eq_norm] using le_of_not_gt hnear
    have hd : 0 < ‖x - y‖ := hs.trans_le (le_of_not_gt hnear)
    have hb := (inv_dist_sub_cubeWeight_le hℓ hs
      (latticeCell_subset_closedCell _ _ (mem_latticeCell_label hℓ x))
      (latticeCell_subset_closedCell _ _ (mem_latticeCell_label hℓ y)) hfar).2
    have hr : ‖x - y‖⁻¹ ≤
        cubeWeight ℓ (latticeLabel ℓ x) (latticeLabel ℓ y) + 2 * Real.sqrt 3 * ℓ / s ^ 2 := by
      rw [dist_eq_norm] at hb
      linarith only [hb]
    rw [nearCoulombKernel, ite_eq_right hnear, add_zero, coulombKernel,
      ← ENNReal.ofReal_inv_of_pos hd, boxCoulombKernel,
      ← ENNReal.ofReal_add (cubeWeight_pos hℓ _ _).le (by positivity)]
    exact ENNReal.ofReal_le_ofReal hr

end LiebThirring.TFCoulomb

end
