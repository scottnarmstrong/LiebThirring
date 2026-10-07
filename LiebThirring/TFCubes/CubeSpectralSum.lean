/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFCubes.CubeParseval

/-! # Reindexing the mixed-mode Parseval sums

The two helpers apply Parseval to an actual derivative Hilbert basis. Zero
coefficients outside the embedded index set allow exact reindexing; the
coefficient differentiation identities then give the weighted state sum.
-/

public section

open scoped InnerProductSpace

namespace LiebThirring.TFCubes

variable {ι κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Neumann assembly: the missing state indices have zero spectral weight. -/
theorem hasSum_weighted_state_of_basis_embedding
    (B : HilbertBasis κ ℂ E) (C : HilbertBasis ι ℂ E)
    (u g : E) (e : κ → ι) (he : Function.Injective e) (w : ι → ℝ)
    (hzero : ∀ i, i ∉ Set.range e → w i = 0)
    (hcoeff : ∀ k, ‖⟪B k, g⟫_ℂ‖ ^ 2 = w (e k) * ‖⟪C (e k), u⟫_ℂ‖ ^ 2) :
    HasSum (fun i => w i * ‖⟪C i, u⟫_ℂ‖ ^ 2) (‖g‖ ^ 2) := by
  have hs := hasSum_norm_sq_hilbertBasis B g
  have hz (i : ι) (hi : i ∉ Set.range e) : w i * ‖⟪C i, u⟫_ℂ‖ ^ 2 = 0 := by
    rw [hzero i hi, zero_mul]
  apply (he.hasSum_iff hz).mp
  exact hs.congr_fun fun k => (hcoeff k).symm

end LiebThirring.TFCubes

end
