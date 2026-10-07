/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Screening.Disintegration
public import LiebThirring.Screening.Exterior
import LiebThirring.Electrostatics.Gaussian

/-!
# Newton's theorem for arbitrary radial finite measures

The rotation-invariant measure is disintegrated into normalized shells, with
mixing measure the pushforward by radius. The atom at the center is included.
Outside a supporting closed ball its potential is its mass divided by the
distance to the center.

Proof: radial screening (Lieb–Lebowitz (1972) II.D, Theorem 2.5).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring

/-- Newton's mixture formula for an arbitrary finite SO(3)-invariant measure. -/
theorem coulombPotential_radial (c y : Position) (μ : Measure Position)
    [IsFiniteMeasure μ] (hμ : IsRadial c μ) :
    coulombPotential μ y = ∫⁻ x, (ENNReal.ofReal (max ‖y-c‖ ‖x-c‖))⁻¹ ∂μ := by
  calc
    coulombPotential μ y = coulombPotential (radialize c μ) y :=
      congrArg (fun ν => coulombPotential ν y) (radialize_eq_self_of_isRadial c μ hμ).symm
    _ = _ := coulombPotential_radialize c y μ

/-- The ordinary real potential is finite outside the support and obeys Newton's formula. -/
theorem integral_inverse_norm_radial_exterior (c y : Position) (μ : Measure Position)
    [IsFiniteMeasure μ] (hμ : IsRadial c μ) {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ᵐ x ∂μ, ‖x-c‖ ≤ r) (hy : r < ‖y-c‖) :
    (∫ x, ‖y-x‖⁻¹ ∂μ) = (μ univ).toReal / ‖y-c‖ := by
  have h := integral_inverse_norm_radialize_exterior c y μ hr hs hy
  rw [radialize_eq_self_of_isRadial c μ hμ] at h
  exact h

/-- The positive and negative charges may be any finite measures of the same mass. -/
theorem neutral_radial_potential_zero (c y : Position) (μp μn : Measure Position)
    [IsFiniteMeasure μp] [IsFiniteMeasure μn]
    (hp : IsRadial c μp) (hn : IsRadial c μn)
    (hneutral : μp univ = μn univ) {r : ℝ} (hr : 0 ≤ r)
    (hsp : ∀ᵐ x ∂μp, ‖x-c‖ ≤ r) (hsn : ∀ᵐ x ∂μn, ‖x-c‖ ≤ r)
    (hy : r < ‖y-c‖) :
    (∫ x, ‖y-x‖⁻¹ ∂μp) - (∫ x, ‖y-x‖⁻¹ ∂μn) = 0 := by
  rw [integral_inverse_norm_radial_exterior c y μp hp hr hsp hy,
    integral_inverse_norm_radial_exterior c y μn hn hr hsn hy, hneutral, sub_self]

end LiebThirring

end
