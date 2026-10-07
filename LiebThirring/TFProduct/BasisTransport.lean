/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Transport and reindexing of complete Hilbert bases -/

@[expose] public section
open Submodule Set
open scoped InnerProductSpace
namespace LiebThirring.TFProduct

variable {E F ι κ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Transport a complete basis through a complex linear isometric equivalence. -/
noncomputable def mapHilbertBasis (B : HilbertBasis ι ℂ E) (T : E ≃ₗᵢ[ℂ] F) :
    HilbertBasis ι ℂ F :=
  HilbertBasis.ofRepr (T.symm.trans B.repr)

@[simp] theorem mapHilbertBasis_apply (B : HilbertBasis ι ℂ E)
    (T : E ≃ₗᵢ[ℂ] F) (i : ι) : mapHilbertBasis B T i = T (B i) := by
  classical
  rw [← HilbertBasis.repr_symm_single (mapHilbertBasis B T) i]
  change T (B.repr.symm (lp.single 2 i 1)) = _
  rw [HilbertBasis.repr_symm_single]

/-- A bijective reindexing preserves the literal orthonormal family. -/
theorem orthonormal_reindex_hilbertBasis (B : HilbertBasis ι ℂ E) (e : κ ≃ ι) :
    Orthonormal ℂ (fun i => B (e i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [orthonormal_iff_ite.mp B.orthonormal]
  simp only [e.injective.eq_iff]

theorem reindex_hilbertBasis_span_orthogonal_eq_bot
    (B : HilbertBasis ι ℂ E) (e : κ ≃ ι) :
    (span ℂ (range (fun i => B (e i))))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  rw [mem_bot]
  apply B.repr.injective
  ext j
  rw [B.repr_apply_apply, LinearIsometryEquiv.map_zero]
  apply inner_right_of_mem_orthogonal _ hu
  apply subset_span
  exact ⟨e.symm j, congrArg B (e.apply_symm_apply j)⟩

/-- Reindex a complete basis without a finite-dimensionality assumption. -/
noncomputable def reindexHilbertBasis [CompleteSpace E]
    (B : HilbertBasis ι ℂ E) (e : κ ≃ ι) : HilbertBasis κ ℂ E :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_reindex_hilbertBasis B e)
    (reindex_hilbertBasis_span_orthogonal_eq_bot B e)

@[simp] theorem reindexHilbertBasis_apply [CompleteSpace E]
    (B : HilbertBasis ι ℂ E) (e : κ ≃ ι) (i : κ) :
    reindexHilbertBasis B e i = B (e i) :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) i

end LiebThirring.TFProduct
end
