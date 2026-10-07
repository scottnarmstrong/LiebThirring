/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import LiebThirring.ThermoBounds.IntegerPhysics

/-!
# Specializing the full neutral variational packing input

Neutral variational packing on bounded nonempty open containing domains implies both the
union-domain form used in the finite arbitrary-radius comparisons and
the centered-ball form consumed by the canonical analytic engine. The
full input permits the empty family, hence includes the vacuum upper
bound without a separate vacuum hypothesis.
-/

public section

open Finset Metric Set

namespace LiebThirring.ThermoBounds

theorem union_packing_of_domain_packing {E : Set Position → ℕ → ℝ}
    (hpacking : ∀ (ι : Type) (Ω : Set Position) (s : Finset ι)
      (c : ι → Position) (r : ι → ℝ) (m : ι → ℕ),
      IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω →
      (∀ i ∈ s, 0 < r i) → (∀ i ∈ s, ball (c i) (r i) ⊆ Ω) →
      (s : Set ι).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E Ω (∑ i ∈ s, m i) ≤ ∑ i ∈ s, E (ball (c i) (r i)) (m i)) :
    ∀ (ι : Type) (s : Finset ι) (c : ι → Position) (r : ι → ℝ) (m : ι → ℕ),
      s.Nonempty → (∀ i ∈ s, 0 < r i) →
      (s : Set ι).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E (⋃ i ∈ s, ball (c i) (r i)) (∑ i ∈ s, m i) ≤
        ∑ i ∈ s, E (ball (c i) (r i)) (m i) := by
  intro ι s c r m hs hpos hdisj
  have hopen : IsOpen (⋃ i ∈ s, ball (c i) (r i)) :=
    isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  have hnonempty : (⋃ i ∈ s, ball (c i) (r i)).Nonempty := by
    obtain ⟨i, hi⟩ := hs
    exact ⟨c i, mem_iUnion₂.mpr ⟨i, hi, mem_ball_self (hpos i hi)⟩⟩
  have hbounded : Bornology.IsBounded (⋃ i ∈ s, ball (c i) (r i)) :=
    (Bornology.isBounded_biUnion_finset s).mpr fun _ _ => isBounded_ball
  exact hpacking ι _ s c r m hopen hnonempty hbounded hpos
    (fun i hi => subset_iUnion₂_of_subset i hi Subset.rfl) hdisj

theorem canonical_packing_of_domain_packing {E : Set Position → ℕ → ℝ}
    (hpacking : ∀ (ι : Type) (Ω : Set Position) (s : Finset ι)
      (c : ι → Position) (r : ι → ℝ) (m : ι → ℕ),
      IsOpen Ω → Ω.Nonempty → Bornology.IsBounded Ω →
      (∀ i ∈ s, 0 < r i) → (∀ i ∈ s, ball (c i) (r i) ⊆ Ω) →
      (s : Set ι).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E Ω (∑ i ∈ s, m i) ≤ ∑ i ∈ s, E (ball (c i) (r i)) (m i)) :
    ∀ L (s : Finset SwissCheeseLabel) (c : SwissCheeseLabel → Position)
      (r : SwissCheeseLabel → ℝ) (m : SwissCheeseLabel → ℕ), 0 < L →
      (∀ i ∈ s, 0 < r i) →
      (∀ i ∈ s, ball (c i) (r i) ⊆ ball (0 : Position) L) →
      (s : Set SwissCheeseLabel).PairwiseDisjoint (fun i => ball (c i) (r i)) →
      E (ball (0 : Position) L) (∑ i ∈ s, m i) ≤
        ∑ i ∈ s, E (ball (c i) (r i)) (m i) := by
  intro L s c r m hL hpos hsub hdisj
  exact hpacking SwissCheeseLabel _ s c r m isOpen_ball (nonempty_ball.mpr hL)
    isBounded_ball hpos hsub hdisj

end LiebThirring.ThermoBounds

end
