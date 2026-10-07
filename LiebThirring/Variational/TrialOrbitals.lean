/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Defs.Configuration
import Mathlib.Topology.NatEmbedding

/-! # Disjoint smooth orbitals for Slater trials -/

public section

open Set Function Filter
open scoped Topology ContDiff

namespace LiebThirring

/-- Finitely many compact smooth real orbitals with disjoint supports and an evaluation
matrix equal to the identity. The empty family also covers the vacuum. -/
theorem exists_disjoint_trial_orbitals (N : ℕ) :
    ∃ (a : Fin N → Position) (b : Fin N → Position → ℝ),
      (∀ i, HasCompactSupport (b i)) ∧
      (∀ i, ContDiff ℝ ∞ (b i)) ∧
      Pairwise (Disjoint on fun i => tsupport (b i)) ∧
      (∀ i j, b j (a i) = if i = j then 1 else 0) := by
  classical
  obtain ⟨U, hU, ho, hd⟩ := exists_seq_infinite_isOpen_pairwise_disjoint Position
  choose a ha using fun i : Fin N => (hU i.val).nonempty
  have hn (i : Fin N) : U i.val ∈ 𝓝 (a i) := (ho i.val).mem_nhds (ha i)
  choose b hb hc hs hr hv using fun i : Fin N =>
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hn i)
  refine ⟨a, b, hc, hs, ?_, ?_⟩
  · intro i j hij
    exact (hd (fun h => hij (Fin.ext h))).mono (hb i) (hb j)
  · intro i j
    split_ifs with hij
    · subst j
      exact hv i
    · apply image_eq_zero_of_notMem_tsupport
      intro hm
      exact Set.disjoint_left.mp (hd (fun h => hij (Fin.ext h))) (ha i) (hb j hm)

end LiebThirring

end
