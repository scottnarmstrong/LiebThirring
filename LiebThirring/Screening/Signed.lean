/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Screening.Newton
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# Screening of neutral radial signed charges

A finite signed charge is represented either by its two positive constituent
measures (as in the electron/nucleus charge distribution), or by its canonical
Jordan decomposition. The second charge need not be radial or neutral.
Uniform separation makes the Coulomb integrals finite.

Lieb–Lebowitz (1972) II.D--E (2.21)--(2.25).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring

/-- Screening in the four-term charge representation used by cluster energies. -/
theorem neutral_radial_mutual_energy_zero (c : Position) (μp μn νp νn : Measure Position)
    [IsFiniteMeasure μp] [IsFiniteMeasure μn] [IsFiniteMeasure νp] [IsFiniteMeasure νn]
    (hp : IsRadial c μp) (hn : IsRadial c μn) (hneutral : μp univ = μn univ)
    {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε)
    (hsp : ∀ᵐ x ∂μp, ‖x-c‖ ≤ r) (hsn : ∀ᵐ x ∂μn, ‖x-c‖ ≤ r)
    (htp : ∀ᵐ y ∂νp, r+ε ≤ ‖y-c‖) (htn : ∀ᵐ y ∂νn, r+ε ≤ ‖y-c‖) :
    (∫ y, ∫ x, ‖y-x‖⁻¹ ∂μp ∂νp) - (∫ y, ∫ x, ‖y-x‖⁻¹ ∂μn ∂νp) -
      (∫ y, ∫ x, ‖y-x‖⁻¹ ∂μp ∂νn) + (∫ y, ∫ x, ‖y-x‖⁻¹ ∂μn ∂νn) = 0 := by
  have heq (ν : Measure Position) (ht : ∀ᵐ y ∂ν, r+ε ≤ ‖y-c‖) :
      (∫ y, ∫ x, ‖y-x‖⁻¹ ∂μp ∂ν) = (∫ y, ∫ x, ‖y-x‖⁻¹ ∂μn ∂ν) := by
    apply integral_congr_ae
    filter_upwards [ht] with y hy
    exact sub_eq_zero.mp (neutral_radial_potential_zero c y μp μn hp hn hneutral hr hsp hsn
      ((lt_add_of_pos_right r hε).trans_le hy))
  rw [heq νp htp, heq νn htn]
  ring

/-- In particular, two charge distributions in strictly separated balls screen each other. -/
theorem neutral_radial_mutual_energy_zero_of_ball_separation (c d : Position)
    (μp μn νp νn : Measure Position)
    [IsFiniteMeasure μp] [IsFiniteMeasure μn] [IsFiniteMeasure νp] [IsFiniteMeasure νn]
    (hp : IsRadial c μp) (hn : IsRadial c μn) (hneutral : μp univ = μn univ)
    {r s : ℝ} (hr : 0 ≤ r) (hcent : r+s < ‖d-c‖)
    (hsp : ∀ᵐ x ∂μp, ‖x-c‖ ≤ r) (hsn : ∀ᵐ x ∂μn, ‖x-c‖ ≤ r)
    (htp : ∀ᵐ y ∂νp, ‖y-d‖ ≤ s) (htn : ∀ᵐ y ∂νn, ‖y-d‖ ≤ s) :
    (∫ y, ∫ x, ‖y-x‖⁻¹ ∂μp ∂νp) - (∫ y, ∫ x, ‖y-x‖⁻¹ ∂μn ∂νp) -
      (∫ y, ∫ x, ‖y-x‖⁻¹ ∂μp ∂νn) + (∫ y, ∫ x, ‖y-x‖⁻¹ ∂μn ∂νn) = 0 := by
  have hε : 0 < ‖d-c‖ - s - r := by linarith only [hcent]
  have hsep (ν : Measure Position) (ht : ∀ᵐ y ∂ν, ‖y-d‖ ≤ s) :
      ∀ᵐ y ∂ν, r+(‖d-c‖ - s - r) ≤ ‖y-c‖ := by
    filter_upwards [ht] with y hy
    have htri : ‖d-c‖ ≤ ‖y-d‖ + ‖y-c‖ := by
      simpa only [sub_add_sub_cancel, norm_sub_rev d y] using norm_add_le (d-y) (y-c)
    linarith only [hy, htri]
  exact neutral_radial_mutual_energy_zero c μp μn νp νn hp hn hneutral hr hε hsp hsn
    (hsep νp htp) (hsep νn htn)

end LiebThirring

end
