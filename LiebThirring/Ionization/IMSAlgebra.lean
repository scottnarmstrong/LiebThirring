/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Sobolev.WeakMultiplier

/-! # Finite-partition algebra for the IMS identity

Differentiation of the partition identity cancels every mixed gradient term.
These results are on the full configuration space and impose no antisymmetry condition.
-/

public section

open scoped ContDiff

namespace LiebThirring

/-- The pointwise IMS square identity in a complex Hilbert space. -/
theorem sum_norm_partition_product_sq {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (b d : ι → ℝ) (hpart : ∑ s, b s ^ 2 = 1) (hcross : ∑ s, b s * d s = 0)
    (u g : F) :
    (∑ s, ‖(b s : ℂ) • g + (d s : ℂ) • u‖ ^ 2) =
      ‖g‖ ^ 2 + (∑ s, d s ^ 2) * ‖u‖ ^ 2 := by
  have he (s : ι) : ‖(b s : ℂ) • g + (d s : ℂ) • u‖ ^ 2 =
      b s ^ 2 * ‖g‖ ^ 2 + 2 * (b s * d s) * (inner ℂ g u).re +
        d s ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), norm_smul, norm_smul, inner_smul_left, inner_smul_right]
    simp only [Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      RCLike.re_to_complex, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul,
    hpart, hcross, one_mul, mul_zero, zero_mul, add_zero]

end LiebThirring

end
