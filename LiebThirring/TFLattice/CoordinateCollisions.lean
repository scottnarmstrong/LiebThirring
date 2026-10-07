/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.TFLattice.Indices
import Mathlib.Tactic

/-!
# Equal-coordinate counts for cube modes

Lieb–Simon (1977) III.14, pp. 69–71 (the filled-density convergence): only pairs sharing a spatial
coordinate contribute to the variance of the filled Dirichlet density. A
box of side `m` has at most `3 q m²` such partners for each mode, including
all spin labels. The estimates apply to every subset, including partially
filled degenerate shells.
-/

@[expose] public section

namespace LiebThirring.TFLattice

theorem card_modeBox_coordinate {q a m : ℕ} (i : Fin 3) (v : ℕ) :
    ((modeBox q a m).filter fun p => p.1 i = v).card ≤ q * m ^ 2 := by
  classical
  have heq : (modeBox q a m).filter (fun p => p.1 i = v) =
      ((Fintype.piFinset fun _ : Fin 3 => Finset.Ico a (a + m)).filter
        fun k => k i = v) ×ˢ (Finset.univ : Finset (Fin q)) := by
    ext p
    simp [modeBox]
  rw [heq, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  by_cases hv : v ∈ Finset.Ico a (a + m)
  · rw [Fintype.card_filter_piFinset_const_eq_of_mem _ i hv]
    simp [mul_comm]
  · have hempty : ((Fintype.piFinset fun _ : Fin 3 => Finset.Ico a (a + m)).filter
        fun k => k i = v) = ∅ := by
      ext k
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.notMem_empty,
        iff_false, not_and]
      intro hk he
      exact hv (he ▸ hk i)
    simp [hempty]

theorem card_coordinate_partners_le {q a m : ℕ} {s : Finset (ModeIndex q)}
    (hs : s ⊆ modeBox q a m) (k : ModeIndex q) (i : Fin 3) :
    (s.filter fun p => p.1 i = k.1 i).card ≤ q * m ^ 2 := by
  classical
  exact (Finset.card_le_card (Finset.filter_subset_filter _ hs)).trans
    (card_modeBox_coordinate i (k.1 i))

/-- The union bound retains spin multiplicities, and makes no assumption
about how the last energy shell was selected. -/
theorem card_shared_coordinate_partners_le {q a m : ℕ} {s : Finset (ModeIndex q)}
    (hs : s ⊆ modeBox q a m) (k : ModeIndex q) :
    (s.filter fun p => ∃ i : Fin 3, p.1 i = k.1 i).card ≤ 3 * q * m ^ 2 := by
  classical
  have heq : (s.filter fun p => ∃ i : Fin 3, p.1 i = k.1 i) =
      Finset.univ.biUnion (fun i : Fin 3 => s.filter fun p => p.1 i = k.1 i) := by
    ext p
    simp [and_comm]
  rw [heq]
  calc
    _ ≤ ∑ i : Fin 3, (s.filter fun p => p.1 i = k.1 i).card := Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin 3, q * m ^ 2 :=
      Finset.sum_le_sum fun i _ => card_coordinate_partners_le hs k i
    _ = 3 * q * m ^ 2 := by simp [mul_assoc]

theorem sum_card_shared_coordinate_partners_le {q a m : ℕ} {s : Finset (ModeIndex q)}
    (hs : s ⊆ modeBox q a m) :
    (∑ k ∈ s, (s.filter fun p => ∃ i : Fin 3, p.1 i = k.1 i).card) ≤
      s.card * (3 * q * m ^ 2) := by
  classical
  calc
    _ ≤ ∑ _ ∈ s, 3 * q * m ^ 2 :=
      Finset.sum_le_sum fun k _ => card_shared_coordinate_partners_le hs k
    _ = _ := by simp

end LiebThirring.TFLattice

end
