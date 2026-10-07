/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.Packing.SwissCheeseStage
import Mathlib.Tactic

/-!
# Covered and residual volumes of Swiss-cheese truncations

The volume identities follow from actual finite disjoint families, with no
assumption about the measure of an infinite union.
-/

public section

open Set MeasureTheory Metric Filter

namespace LiebThirring

/-- All balls in the infinite family are pairwise disjoint. -/
theorem swissCheeseInfinite_pairwiseDisjoint {Ω : Set Position}
    {c : SwissCheeseLabel → Position} (hc : ∀ t, isSwissCheeseStage Ω t c) :
    Pairwise (fun i j => Disjoint (ball (c i) (swissCheeseLabelRadius i))
      (ball (c j) (swissCheeseLabelRadius j))) := by
  intro i j hij
  exact (hc (max i.1 j.1 + 1)).2
    (mem_swissCheeseLevels.mpr (by omega)) (mem_swissCheeseLevels.mpr (by omega)) hij

end LiebThirring

end
